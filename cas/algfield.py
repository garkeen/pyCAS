"""ℚ(B)[α] 代数扩张域算术（M7.0）：单一代数对象表示。

# 表示与契约（设计权威 docs/m7_algfield.md）

- 域对象 :class:`AlgField`：K[T]/(m)，K 是任意"叶子域"（Fr / Ga /
  SymRat / RatFunc 皆可——鸭子类型：支持 ``+ - * /`` 与零判定
  :func:`_z`，可哈希）。m 为首一极小多项式，**升序**系数 list；
  构造校验 monic 归一 + 无平方（gcd(m,m')=常数）；不可约性由调用方
  按契约保证（ℚ 系数可用 :func:`af_irreducible_q` 验证）。
- 元素 :class:`AlgElem`：约简后的系数 list，构造即规范形
  （mod m 余式 + trim）——等值 = 规范形逐系数相等。
- 算术：模块内鸭子类型小算术层（_p_*）。不与 cas/univar 共享代码，
  因后者契约要求系数自带 ``is_zero()`` 方法而标量叶没有。
- 必备运算（arch §M7.0 清单）：minpoly 登记/约简（乘法出口余式）、
  求逆（xgcd mod m）、uexgcd、迹 Tr(a·β^t)（牛顿幂和）、范数
  N(a)=Res_T(m,a)（Sylvester 行列式，monic m ⟹ Res=N）、通用结式
  af_res、出口回化 to_term（origin 形态还原）。
- 本模块只依赖地基 {term, errors}，不依赖 risch/integrate/univar。

# 已知边界

- 多符号扩张（ℚ(√2,√3)）暂不表达（基叶限标量/函数域；本原元归一
  是 M7.3）。
- 导子 D 在 K(α) 上的延拓属塔层职责（risch），不在本模块。
"""

from fractions import Fraction as Fr

from cas.errors import PolyError
from cas import term as T
from cas.term import S, N


def _z(c):
    """叶子域零判定（鸭子类型：is_zero() 或标量 == 0）。"""
    return c.is_zero() if hasattr(c, "is_zero") else c == 0


def _leaf_eq(a, b):
    """叶子域等词：先 == ；RatFunc 类（有 .p/.q 无 __eq__）走规范形
    结构比对（全库惯例：比较分子/分母 monos）。"""
    if a is b:
        return True
    r = a == b
    if isinstance(r, bool) and r:
        return True
    pa, qa = getattr(a, "p", None), getattr(a, "q", None)
    pb, qb = getattr(b, "p", None), getattr(b, "q", None)
    if pa is not None and pb is not None:
        return pa.monos == pb.monos and qa.monos == qb.monos
    return False


def _leaf_key(c):
    """叶子域规范哈希键（与 _leaf_eq 保持同余：等值 ⟺ 同键）。"""
    p = getattr(c, "p", None)
    if p is not None:
        q = c.q
        return ("rf", tuple(sorted(p.monos.items())),
                tuple(sorted(q.monos.items())))
    return c


# ---- K[T] 鸭子类型算术层（升序 list；K 叶支持 +-*/ 与 _z） ----------

def _neg_list(cs):
    return [c * Fr(-1) for c in cs]


def _p_trim(cs):
    while cs and _z(cs[-1]):
        cs.pop()
    return cs


def _p_is_zero(cs):
    return not cs or all(_z(c) for c in cs)


def _p_add(a, b):
    n = max(len(a), len(b))
    out = []
    for i in range(n):
        ca = a[i] if i < len(a) else None
        cb = b[i] if i < len(b) else None
        if ca is None:
            out.append(cb)
        elif cb is None:
            out.append(ca)
        else:
            out.append(ca + cb)
    return _p_trim(out)


def _p_neg(a):
    return [c * Fr(-1) for c in a]


def _p_mul(a, b):
    if not a or not b:
        return []
    zero = a[0] * Fr(0)
    out = [zero for _ in range(len(a) + len(b) - 1)]
    for i, ca in enumerate(a):
        if _z(ca):
            continue
        for j, cb in enumerate(b):
            if _z(cb):
                continue
            out[i + j] = out[i + j] + ca * cb
    return _p_trim(out)


def _p_divmod(a, b):
    """K[T] 除法（b 非零）。返回 (q, r) 升序 list。"""
    r = [c for c in a]
    db = len(b) - 1
    lb = b[db]
    q = []
    while len(r) - 1 >= db and not _p_is_zero(r):
        shift = len(r) - 1 - db
        c = r[-1] / lb
        while len(q) <= shift:
            q.append(r[-1] * Fr(0))
        q[shift] = c
        for i in range(db + 1):
            r[shift + i] = r[shift + i] - c * b[i]
        _p_trim(r)
    _p_trim(q)
    return q, r


def _p_pow(cs, n, one):
    out = [one]
    base = list(cs)
    while n > 0:
        if n & 1:
            out = _p_mul(out, base)
        base = _p_mul(base, base)
        n >>= 1
    return out


def _p_xgcd(a, b, one):
    """扩展欧几里得：s·a + t·b = g（monic g）。返回 (s, t, g)。

    不变量：s0·a + t0·b = A；s1·a + t1·b = B。
    """
    A, B = _p_trim(list(a)), _p_trim(list(b))
    s0, s1 = [one], []
    t0, t1 = [], [one]
    while not _p_is_zero(B):
        q, r = _p_divmod(A, B)
        s_new = _p_add(s0, _p_neg(_p_mul(q, s1)))
        t_new = _p_add(t0, _p_neg(_p_mul(q, t1)))
        A, B = B, r
        s0, s1 = s1, s_new
        t0, t1 = t1, t_new
    if _p_is_zero(A):
        return [], [], []
    inv = one / A[-1]
    return ([c * inv for c in s0], [c * inv for c in t0],
            [c * inv for c in A])


class AlgField:
    """K[T]/(m)：单一代数扩张域对象（M7.0 统一表示的登记处）。

    元数据槽（不参与相等/哈希）：
      key     -- 根式出处键 (bv, p_, q_)（risch 参数化共享符号用）
      bracket -- 实嵌入隔离区间 (lo, hi)（Fr 端点；正根式常数专用，
                 精确符号判定消费——A2 隔离判定，非数值采样）
    """

    __slots__ = ("m", "one", "zero", "origin", "key", "bracket")

    def __init__(self, m_coeffs, one_c, zero_c=None, origin=None,
                 key=None, bracket=None):
        cs = _p_trim(list(m_coeffs))
        if _p_is_zero(cs):
            raise PolyError("algfield: zero minpoly")
        lc = cs[-1]
        if _z(lc - one_c):
            self.m = cs
        else:
            self.m = [c / lc for c in cs]     # monic 归一
        if len(self.m) < 2:
            raise PolyError("algfield: minpoly degree >= 1 required")
        self.one = one_c
        self.zero = one_c * Fr(0) if zero_c is None else zero_c
        self.origin = origin
        self.key = key
        self.bracket = bracket
        # 无平方校验：gcd(m, m') 须为常数（不可约性契约另验）
        mp = _p_trim([c * Fr(i) for i, c in enumerate(self.m)][1:])
        if not _p_is_zero(mp):
            if len(self._monic_gcd(self.m, mp)) > 1:
                raise PolyError("algfield: minpoly not squarefree")

    def _monic_gcd(self, a, b):
        A, B = _p_trim(list(a)), _p_trim(list(b))
        while not _p_is_zero(B):
            _, r = _p_divmod(A, B)
            A, B = B, r
        if _p_is_zero(A):
            return []
        s = self.one / A[-1]
        return [c * s for c in A]

    # ---- 元素构造 ---------------------------------------------------

    def elem(self, coeffs):
        return AlgElem(self, coeffs)

    def const(self, c):
        if isinstance(c, int):
            c = Fr(c)
        return AlgElem(self, [c])

    def gen(self):
        """α 本身。"""
        return AlgElem(self, [self.zero, self.one])

    # ---- 幂和 / 迹 --------------------------------------------------

    def pow_sums(self, upto):
        """m 的根幂和 s_1..s_upto（牛顿恒等式，K 系数版；s_k ∈ K）。"""
        asc = self.m
        n = len(asc) - 1
        cd = [asc[n - k] for k in range(1, n + 1)]   # c_1..c_n
        out = []
        for k in range(1, upto + 1):
            acc = self.zero
            for j in range(1, min(k - 1, n) + 1):
                acc = acc + cd[j - 1] * out[k - j - 1]
            if k <= n:
                acc = acc + cd[k - 1] * Fr(k)
            out.append(acc * Fr(-1))
        return out

    def trace_pow(self, e, t=0):
        """Tr(e·β^t) = Σ_i e_i · s_{i+t}（e = Σ e_i T^i，s_0 = n）。"""
        n = len(self.m) - 1
        ps = [self.one * Fr(n)]
        ps.extend(self.pow_sums(n + max(len(e.cs) - 1, 0) + t))
        total = self.zero
        for i, c in enumerate(e.cs):
            if not _z(c):
                total = total + c * ps[i + t]
        return total

    def trace(self, e):
        return self.trace_pow(e, 0)

    # ---- 消费端换算 -------------------------------------------------

    def minpoly_poly(self, sym):
        """极小多项式 → 该符号上的首一 Poly（ℚ 系数，poly 层消费）。"""
        from cas.poly import Poly

        n = len(self.m) - 1
        monos = {}
        for i, c in enumerate(self.m):
            if _z(c):
                continue
            if not isinstance(c, Fr):
                raise PolyError("algfield: non-Q minpoly leaf")
            monos[(i,)] = c          # 升序表：索引即指数
        return Poly((sym,), monos)

    # ---- 域相等（表示级：同一极小多项式 ⟺ 同一域） -----------------

    def __eq__(self, o):
        if not isinstance(o, AlgField):
            return NotImplemented
        return (len(self.m) == len(o.m)
                and all(_leaf_eq(a, b) for a, b in zip(self.m, o.m)))

    def __hash__(self):
        return hash(("AlgField", tuple(_leaf_key(c) for c in self.m)))


def af_norm(e):
    """N_{K(α)/K}(a) = Res_T(m, a)（monic m ⟹ Res = Π a(β_j)）。"""
    if e.is_zero():
        return e.fld.zero
    return af_res(e.fld.m, e.cs, e.fld)


def af_res(f, g, fld):
    """通用结式 Res(f, g)：K[T] 上 Sylvester 行列式（高斯消元）。

    布局（标准定义）：前 deg(g) 行为 T^{d-1-i}·f 的降幂系数（偏移 i），
    后 deg(f) 行为 T^{n-1-j}·g 的降幂系数（偏移 j）；
    det(Sylvester(f,g)) = Res(f,g)。
    """
    zf = _p_trim(list(f))
    zg = _p_trim(list(g))
    if _p_is_zero(zf) or _p_is_zero(zg):
        return fld.zero
    n = len(zf) - 1
    d = len(zg) - 1
    size = n + d
    fd = [zf[n - k] for k in range(n + 1)]   # f 降幂
    gd = [zg[d - k] for k in range(d + 1)]   # g 降幂
    M = []
    for i in range(d):
        row = [fld.zero] * size
        row[i:i + n + 1] = fd
        M.append(row)
    for j in range(n):
        row = [fld.zero] * size
        row[j:j + d + 1] = gd
        M.append(row)
    return _det(M, fld)


def _det(M, fld):
    """K 上行列式（部分主元高斯消元，行交换记号差）。"""
    size = len(M)
    A = [row[:] for row in M]
    sign = Fr(1)
    det = fld.one
    for col in range(size):
        piv = None
        for r in range(col, size):
            if not _z(A[r][col]):
                piv = r
                break
        if piv is None:
            return fld.zero
        if piv != col:
            A[col], A[piv] = A[piv], A[col]
            sign = sign * Fr(-1)
        pv = A[col][col]
        det = det * pv
        inv = fld.one / pv
        for r in range(col + 1, size):
            if not _z(A[r][col]):
                fac = A[r][col] * inv
                A[r] = [vr - fac * vc for vr, vc in zip(A[r], A[col])]
    return det * sign


class AlgElem:
    """K(α) 元素：规范形系数 list（升序，恒 mod m 约简）。"""

    __slots__ = ("fld", "cs")

    def __init__(self, fld, coeffs):
        cs = _p_trim(list(coeffs))
        if len(cs) >= len(fld.m):
            _, cs = _p_divmod(cs, fld.m)
        self.fld = fld
        self.cs = cs

    # ---- 基本性质 ---------------------------------------------------

    @property
    def deg(self):
        return len(self.cs) - 1

    def is_zero(self):
        return _p_is_zero(self.cs)

    def _coerce(self, other):
        if isinstance(other, AlgElem):
            if other.fld != self.fld:
                raise PolyError("algfield: mixed fields")
            return other
        if isinstance(other, int):
            other = Fr(other)
        return AlgElem(self.fld, [other])   # 基叶/标量 -> 常量元素

    # ---- 算术 -------------------------------------------------------

    def __add__(self, o):
        return AlgElem(self.fld,
                       _p_add(self.cs, self._coerce(o).cs))

    __radd__ = __add__

    def __sub__(self, o):
        return AlgElem(self.fld,
                       _p_add(self.cs, _p_neg(self._coerce(o).cs)))

    def __rsub__(self, o):
        return self._coerce(o) - self

    def __mul__(self, o):
        o2 = self._coerce(o)
        return AlgElem(self.fld, _p_mul(self.cs, o2.cs))

    __rmul__ = __mul__

    def __truediv__(self, o):
        return self * self._coerce(o).inv()

    def __rtruediv__(self, o):
        return self._coerce(o) * self.inv()

    def __neg__(self):
        return AlgElem(self.fld, _p_neg(self.cs))

    def __pow__(self, n):
        if not isinstance(n, int):
            raise PolyError("algfield: integer powers only")
        if n < 0:
            return AlgElem(self.fld,
                           _p_pow(self.cs, -n, self.fld.one)).inv()
        return AlgElem(self.fld, _p_pow(self.cs, n, self.fld.one))

    def inv(self):
        """a^{-1} mod m（扩展欧几里得；gcd≠单位 -> PolyError）。"""
        s, _t, g = _p_xgcd(self.cs, self.fld.m, self.fld.one)
        if len(g) != 1:
            raise PolyError("algfield: element not invertible")
        _, rem = _p_divmod(s, self.fld.m)
        return AlgElem(self.fld, rem)

    # ---- 相等 / 哈希 ------------------------------------------------

    def __eq__(self, o):
        if not isinstance(o, AlgElem):
            return NotImplemented
        return (self.fld == o.fld and len(self.cs) == len(o.cs)
                and all(_leaf_eq(a, b) for a, b in zip(self.cs, o.cs)))

    def __hash__(self):
        return hash(("AlgElem",
                     tuple(_leaf_key(c) for c in self.fld.m),
                     tuple(_leaf_key(c) for c in self.cs)))

    # ---- 出口回化 ---------------------------------------------------

    def to_term(self):
        """Σ cᵢ·origin^i —— 根式形态还原（origin 缺失时拒绝）。"""
        og = self.fld.origin
        if og is None:
            raise PolyError("algfield: no origin term for retraction")
        parts = []
        for i, c in enumerate(self.cs):
            if _z(c):
                continue
            ct = c.to_term() if hasattr(c, "to_term") else N(c)
            if i == 0:
                parts.append(ct)
            elif i == 1:
                parts.append(T.times(ct, og))
            else:
                parts.append(T.times(ct, T.pw(og, N(i))))
        if not parts:
            return N(Fr(0))
        if len(parts) == 1:
            return parts[0]
        return T.mk(S("Plus"), tuple(parts))

    def __repr__(self):
        return f"[{', '.join(str(c) for c in self.cs)}]"


# ---- 作用域登记处（M7.0-b 单一来源） --------------------------------
# 取代 poly.ALG_MODULI / risch_core.ALG_RELATIONS /
# ratint.AN_INTERVALS/AN_RELATIONS 四散表示：符号 -> AlgField
# （极小多项式 + 出处键 + 实嵌入区间全在域对象上）。

ALG_FIELDS = {}


def register_alg_field(sym, fld):
    ALG_FIELDS[sym] = fld


def unregister_alg_fields(syms):
    for s in syms:
        ALG_FIELDS.pop(s, None)


# ---- 工厂 ------------------------------------------------------------

def af_q(m_coeffs_asc, origin=None):
    """ℚ(α)：Fr 系数极小多项式（升序）。"""
    coefs = [c if isinstance(c, Fr) else Fr(c) for c in m_coeffs_asc]
    return AlgField(coefs, Fr(1), zero_c=Fr(0), origin=origin)


def af_func(m_rf_asc, vars_, origin=None):
    """函数基 K = ℚ(x,…)(α)：RatFunc 系数极小多项式（升序）。"""
    from cas.ratfunc import RatFunc
    return AlgField(list(m_rf_asc), RatFunc.one(vars_),
                    zero_c=RatFunc.zero(vars_), origin=origin)


def af_irreducible_q(fld):
    """ℚ 系数域上验证极小多项式不可约（Zassenhaus 分解）。

    非 ℚ 系数返回 None（不判定——诚实协议：None=未知，非 False）。
    """
    from cas.poly import Poly

    coefs = []
    for c in fld.m:
        if isinstance(c, Fr):
            coefs.append(c)
        else:
            return None
    tv = S("_af_T")
    monos = {(i,): coefs[i] for i in range(len(coefs)) if not _z(coefs[i])}
    p = Poly((tv,), monos)
    from cas.factor import factor
    _content, facs = factor(p)
    return len(facs) == 1 and facs[0][1] == 1
