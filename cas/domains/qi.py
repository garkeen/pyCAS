# -*- coding: utf-8 -*-
"""ℚ(i) 高斯域：第一个代数扩张（架构 §8 关键路径步骤 3 的地基件）。

元素表示 = 标准形对 (re, im)（re, im ∈ ℚ）。参照（详见 reference.md）：
· FriCAS `gaussian.spad`——ComplexCategory 本身就是 MonogenicAlgebra(R,
  x²+1)：ℚ(i) 即商环 ℚ[z]/(z²+1)；Rep 为 Record(real, imag)，标准形
  唯一 ⟹ 判等即结构判等；乘法直接对偶运算 (ac−bd, ad+bc)（语义 =
  模 x²+1 多项式算术的 d=2 特例）；除法走共轭×范数通道。
· Maxima `rat3a.lisp`——代数量成员通道：闭项视为生成元的有理函数，
  模极小多项式约化（求逆 = 模 minpoly 扩展欧几里得；d=2 时退化为
  共轭/范数）。

成员通道：闭项中常数 i 替换为新鲜变元 z → 投影到 ℚ(z) 有理函数
（复用既有 rf 机器）→ 分子分母各自模 z²+1 约化 → 分子 × 分母逆。
x²+1 在 ℚ 上不可约 ⟹ 非零分母约化后范数非零、恒可逆——这正是
ℚ(i) 成域的原因；分母约化为零 ⟺ 原项除零，非成员。

层位纪律：本模块只依赖 cas.term 与本包基座（含 q/qarith 同级的
poly/ratfunc 机器）。i 常数的身份由构造方注入——库拥有常数声明，
投影层接线——不做名字嗅探。

能力（架构 3.2，算法按能力分派不按类型特判）：
· is_field = True：ℚ(i) 是域（x²+1 不可约性是构造前提，FriCAS 同一
  裁定并诚实注明"this is a lie; we must know that x^2+1 is
  irreducible"——前提由声明承担，不由运行时验证）
· is_ordered = False：复数域无序，序判定按能力查表必须拒绝。
  FriCAS gaussian.spad 全文件无 OrderedRing，同一裁定
· is_euclidean = False：带余除法/欧几里得结构属于 ℤ[i]（范数函数），
  ℚ(i) 作为域无需声明；FriCAS 仅当 R 有 IntegerNumberSystem 才给
  Complex(R) 声明 EuclideanDomain，同一裁定
"""

from fractions import Fraction as Fr

from cas import term as T
from cas.term import Sym
from cas.qarith import fold
from cas.domains.base import Domain, Ring, register
from cas.domains.q import Q_RING
from cas.domains.poly import Poly
from cas.domains.ratfunc import rf_from_term


# ---------------------------------------------------------------------------
# 系数环：标准形对上的运算
# ---------------------------------------------------------------------------

class QIRing(Ring):
    """ℚ(i) 系数环：元素为 (re, im) 对，标准形即表示（判等 = 结构判等）。"""

    is_field = True

    def from_int(self, n):
        return (Fr(n), Fr(0))

    def from_frac(self, f):
        return (Fr(f), Fr(0))

    def add(self, a, b):
        return (a[0] + b[0], a[1] + b[1])

    def neg(self, a):
        return (-a[0], -a[1])

    def mul(self, a, b):
        return (a[0] * b[0] - a[1] * b[1],
                a[0] * b[1] + a[1] * b[0])

    def equal(self, a, b) -> bool:
        return a == b

    def div_exact(self, a, b):
        """a/b = a·conj(b)/norm(b)（共轭×范数通道，FriCAS 同式）。

        b 非零 ⟹ norm(b) = re²+im² > 0（ℚ 上正定），恒可逆。"""
        n = b[0] * b[0] + b[1] * b[1]
        if n == 0:
            raise ZeroDivisionError("division by zero")
        return self.mul(a, (b[0] / n, -b[1] / n))


QI_RING = QIRing()


# ---------------------------------------------------------------------------
# 成员通道：闭项 → ℚ(z) → 模 z²+1 约化
# ---------------------------------------------------------------------------

def _lift_const(t, const, z: Sym):
    """把项中的常数原子 const（指针判等，不嗅探名字）替换为变元 z。"""
    if t is const:
        return z
    if isinstance(t, T.Expr) and t.args:
        return T.mk(t.head, tuple(_lift_const(a, const, z) for a in t.args))
    return t


def _pair_mod(p: Poly):
    """单变量多项式模 z²+1 约化为 (re, im)：z^k ≡ (−1)^(k//2)·z^(k mod 2)。"""
    re, im = Fr(0), Fr(0)
    for k, c in p.monos:
        v = -c if (k[0] // 2) % 2 else c
        if k[0] % 2:
            im += v
        else:
            re += v
    return (re, im)


def qi_of_term(i_const, t):
    """闭项 → ℚ(i) 标准形对；非成员返回 None。

    含自由变元、含其他常数/函数（π、sin…）、非整指数幂、除零——
    全部经 ℚ(z) 投影落空或分母不可逆，如实返回 None。"""
    if T.free_vars(t):
        return None                     # 非闭项：ℚ(i) 是常数域
    z = Sym("z")                        # 闭项无自由变元，z 无碰撞
    rf = rf_from_term(Q_RING, _lift_const(t, i_const, z), (z,))
    if rf is None:
        return None
    num = _pair_mod(rf.num)
    den = _pair_mod(rf.den)
    if den[0] == 0 and den[1] == 0:
        return None                     # 分母 ≡ 0 (mod z²+1)：除零项
    return QI_RING.div_exact(num, den)


# ---------------------------------------------------------------------------
# 域
# ---------------------------------------------------------------------------

class QIDomain(Domain):
    """ℚ(i) = {a + b·i}。i 常数身份由构造注入（声明制，不嗅探）。"""

    name = "Q(i)"
    is_field = True
    is_ordered = False
    is_euclidean = False

    def __init__(self, i_const):
        self.i = i_const

    def member(self, t) -> bool:
        return qi_of_term(self.i, t) is not None

    def to_term(self, pair):
        """标准形对 → 规范驻留项（同值同形 → 同指针）。"""
        re, im = pair
        if im == 0:
            return T.N(re)
        im_part = T.times(T.N(im), self.i)
        if re == 0:
            return fold(im_part)
        return fold(T.plus(T.N(re), im_part))

    def normalize(self, t):
        pair = qi_of_term(self.i, t)
        if pair is None:
            return None
        return self.to_term(pair)

    def equal(self, a, b):
        pa = qi_of_term(self.i, a)
        pb = qi_of_term(self.i, b)
        if pa is None or pb is None:
            return None                  # 非成员：调用方越界
        return pa == pb
