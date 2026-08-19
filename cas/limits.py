"""极限引擎（M3，三值诚实）。

管线：代入连续性 -> 环层消去重试 -> Taylor 首阶分析（series.leading_term）
-> 洛必达兑底（预算限次）。发散到 ±∞ 返回 Special("Infinity") 项；
不可判返回 None（诚实拒答，永不静默错）。

单侧极限：side='+'/'-'；双侧极限要求左右一致（∞ 的符号也必须一致）。
设计立场：这是判定通道不是搜索通道——Gruntz 完备算法留待后续分期。
"""

from fractions import Fraction as Fr

from cas import term as T
from cas.term import Expr, Int, Sym, Const
from cas.series import leading_term, SeriesError
from cas.simplify import simplify


def limit(t, x, a, side=None):
    """lim_{x -> a} t。a 为精确数值（Int/Rat 项或 Fraction）或 π 类常数项。

    返回：数值项 / T.INFINITY（±∞，符号含在 Times(-1, ...) 里）/ None（未知）。
    side: '+' 右极限，'-' 左极限，None 双侧。
    非 Fr 点（如 π、π/2）只走代入通道（连续点判定），不可判则 None。
    """
    if T.is_num(a):
        a = T.num_val(a)
    if not isinstance(a, Fr):
        # π 类常数点：直接代入（mk 折叠 sin(π) 等）；不构造平移级数
        v = simplify(T.subst(t, {x: a}))
        if v is not T.UND and _is_real_value(v):
            return v
        return None
    if T.is_num(t) or (isinstance(t, Const) and t not in (T.PI, T.E)):
        return t
    if side is None:
        lp = limit(t, x, a, side="+")
        lm = limit(t, x, a, side="-")
        if lp is None or lm is None:
            return None
        return lp if lp is lm else None
    u = Sym("_limit_u")
    sh = T.subst(t, {x: T.plus(T.N(a), T.neg(u) if side == "-" else u)})
    return _limit_at_0(sh, u)


def _limit_at_0(t, u, depth=0):
    """lim_{u -> 0+} t（左极限已折叠为 u->0+ 形态）。"""
    if depth > 4:
        return None
    # 通道 1：代入（连续点；mk 在 0^-k / 0^r 处折叠出 UND 触发回退）
    v = simplify(T.subst(t, {u: T.ZERO}))
    if v is not T.UND and _is_real_value(v):
        return v
    # 通道 2：环层消去（0/0 有理形态）后重试代入
    c = _cancel_at_0(t, u)
    if c is not None and c is not t:
        v = simplify(T.subst(c, {u: T.ZERO}))
        if v is not T.UND and _is_real_value(v):
            return v
        return _limit_at_0(c, u, depth + 1)
    # 通道 3：首阶分析（含极点发散判定）
    r = _leading(t, u)
    if r is not None:
        k, ccoef, sgn = r
        if k == 0:
            if sgn is None:
                return T.N(ccoef)
            # 首阶为常数但尾部符号不定：值就是首系数（尾部 -> 0）
            return T.N(ccoef)
        if k > 0:
            return T.ZERO
        # 极点：u -> 0+ 时 u^k > 0，符号由首系数决定
        return T.INFINITY if ccoef > 0 else T.neg(T.INFINITY)
    # 通道 4：洛必达兑底（仅 0/0 商形态，预算限次）
    lh = _lhopital(t, u, depth)
    if lh is not None:
        return lh
    return None


def _is_real_value(v):
    """v 是否为可作极限值的实数形态：数值/π/e 及其经 spec 函数与环运算的复合
    （如 e^1、sin(2)、√2）——均为精确实常数；保守拒绝含自由符号的形态。"""
    from cas import spec as _spec

    if T.is_num(v):
        return True
    if v in (T.PI, T.E):
        return True
    if isinstance(v, Expr):
        n = v.head.name
        if n == "Power":
            b, e = v.args
            if isinstance(e, T.Rat) and T.is_num(b) and T.num_val(b) < 0:
                return False   # 负底分数幂：复数，不作实极限值
            return all(_is_real_value(a) for a in v.args)
        if n in ("Plus", "Times", "Abs"):
            return all(_is_real_value(a) for a in v.args)
        if n == "Log":
            arg = v.args[0]
            if T.is_num(arg) and T.num_val(arg) <= 0:
                return False   # log(非正) 非实数（域健全性，永不静默错）
            return all(_is_real_value(a) for a in v.args)
        if _spec.get(n) is not None:
            return all(_is_real_value(a) for a in v.args)
    return False


def _leading(t, u):
    """首阶分析 -> (阶, 首系数, 尾部符号可判?)；失败 None。"""
    try:
        k, c, tail = leading_term(t, u, Fr(0), 10)
    except (SeriesError, Exception):
        return None
    # 尾部在 u->0+ 趋于 0；整体符号 = 首系数符号（尾部足够小，除非尾部恒等抵消）
    return (k, c, True)


def _cancel_at_0(t, u):
    """0/0 商的环层消去：通分后约去公因子（ops.cancel 语义，限单变量）。"""
    from cas import ops
    from cas.errors import PolyError

    try:
        return ops.cancel(t)
    except (PolyError, Exception):
        return None


def _lhopital(t, u, depth):
    """洛必达：仅对 f/g 商形态且 f(0)=g(0)=0 时应用（导数走 diff/spec）。"""
    from cas.diff import d

    if not (isinstance(t, Expr) and t.head.name == "Times"):
        return None
    num, den = _frac_parts(t)
    if num is None or den is None:
        return None
    n0 = simplify(T.subst(num, {u: T.ZERO}))
    d0 = simplify(T.subst(den, {u: T.ZERO}))
    if n0 is not T.ZERO or d0 is not T.ZERO:
        return None
    ratio = T.div(d(num, u), d(den, u))
    return _limit_at_0(simplify(ratio), u, depth + 1)


def _frac_parts(t):
    """Times 形态拆 (分子, 分母)；分母含负幂因子时重组。"""
    num = []
    den = []
    for a in t.args:
        if isinstance(a, Expr) and a.head.name == "Power" and isinstance(a.args[1], Int) and a.args[1].v < 0:
            be = -a.args[1].v
            den.append(a.args[0] if be == 1 else T.pw(a.args[0], T.N(be)))
        elif T.is_num(a) and T.num_val(a) < 0:
            num.append(a)
        else:
            num.append(a)
    if not den:
        return None, None
    n = T.times(*num) if num else T.ONE
    d = T.times(*den) if len(den) > 1 else den[0]
    return n, d
