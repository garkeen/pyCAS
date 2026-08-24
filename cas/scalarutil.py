"""标量域助手单点（M6.6 归拢）：ℚ(i)/ℚ(i,params) 系数叶的算术与
复数分解。原散落于 risch.py（Ga 标量簇）与 integrate.py（分解簇），
跨模块懒导入是漂移温床——现为本文件唯一实现，调用方一律顶层导入。

层位：仅依赖 {poly, gaussian, errors} 地基；risch/integrate 可安全
顶层导入本模块。契约：输入系数叶恒为 {Fr, Ga, SymRat} 三选一
（N1 系数域封闭声明），越界抛 PolyError。
"""

from fractions import Fraction as Fr

from cas.errors import PolyError
from cas.gaussian import Ga
from cas.poly import Poly, SymRat


# ---------------------------------------------------------------------------
# Ga 标量算术（原 risch.py）
# ---------------------------------------------------------------------------

def lcm2(a, b):
    """整数最小公倍数（math.lcm 的显式版，避免版本差异）。"""
    from math import gcd as _g
    return a * b // _g(a, b)


def ga_den(ga):
    """Ga 元素的公分母（re/im 分母的 lcm）。"""
    return lcm2(ga.re.denominator, ga.im.denominator)


def rf_const_ga(rf):
    """RatFunc 是否为 ℚ(i) 标量；是则返回 Ga，否则 None。"""
    for pp in (rf.p, rf.q):
        for k in pp.monos:
            if any(e != 0 for e in k):
                return None
    num = rf.p.const_val()
    den = rf.q.const_val()
    num_g = num if isinstance(num, Ga) else Ga(num)
    den_g = den if isinstance(den, Ga) else Ga(den)
    if den_g.is_zero():
        return None
    return num_g / den_g


def ga_vec_to_ints(vec):
    """Ga 常数向量 -> 本原整向量 | None（含非常数/非有理分量）。"""
    gs = []
    for e in vec:
        g = rf_const_ga(e)
        if g is None:
            return None
        gs.append(g)
    den = 1
    for g in gs:
        den = lcm2(den, ga_den(g))
    ints = []
    for g in gs:
        val = g * den
        if val.im != 0 or val.re.denominator != 1:
            return None
        ints.append(int(val.re))
    from math import gcd as _g2
    acc = 0
    for v2 in ints:
        acc = _g2(acc, abs(v2))
    if acc == 0:
        return None
    return [v2 // acc for v2 in ints]


def mk_zero_like(one_c):
    """与 one_c 同变量集的零 RatFunc（算术构造，免依赖构造器细节）。"""
    return one_c - one_c


# ---------------------------------------------------------------------------
# ℚ(i,params) 分解（原 integrate.py）
# ---------------------------------------------------------------------------

def leaf_has_ga(c):
    """叶系数是否携带 Ga 分量（递归穿 SymRat）。"""
    if isinstance(c, SymRat):
        return symrat_has_ga(c)
    if isinstance(c, Fr):
        return False
    return hasattr(c, "norm")           # Ga（ℚ(i) 域元素）


def symrat_has_ga(c):
    """SymRat 是否内嵌 Ga 叶（ℚ(i,params) 混合轨道标志）。"""
    for pp in (c.num, c.den):
        for cc in pp.monos.values():
            if leaf_has_ga(cc):
                return True
    return False


def coef_zero(c):
    """任意域叶的零判定。"""
    if isinstance(c, Fr):
        return c == 0
    if isinstance(c, SymRat):
        return c.is_zero()
    return bool(c.re == 0 and c.im == 0) if hasattr(c, "norm") else c == 0


def coef_re_im(c):
    """系数 -> (re, im) 纯参数 SymRat 对（ℚ(i,params) 规范化）。

    SymRat 内嵌 Ga 时分母有理化：(nr+i·ni)/(dr+i·di) 乘 (dr-i·di)——
    全程 Poly 有限运算，无分数塔增长。"""
    if isinstance(c, Fr):
        return c, Fr(0)
    if isinstance(c, SymRat):
        if not symrat_has_ga(c):
            return c, Fr(0)
        nr, ni = poly_re_im(c.num)
        dr, di = poly_re_im(c.den)
        dd = dr * dr + di * di
        if dd.is_zero():
            raise PolyError("zero coefficient denominator")
        ren = nr * dr + ni * di
        imn = ni * dr - nr * di
        return SymRat(ren, dd), SymRat(imn, dd)
    if hasattr(c, "norm"):
        # Ga：分量递归取复数对后组合。value = re + i·im，
        # (re_r+i·re_i) + i·(im_r+i·im_i) = (re_r - im_i) + i·(re_i + im_r)
        if isinstance(c.re, Fr):
            rr, ri = c.re, Fr(0)
        else:
            rr, ri = coef_re_im(c.re)
        if isinstance(c.im, Fr):
            ir, ii = c.im, Fr(0)
        else:
            ir, ii = coef_re_im(c.im)
        return rr - ii, ri + ir
    raise PolyError(f"coefficient outside supported domains: {c!r}")


def poly_re_im(p):
    """Poly -> (re, im)：逐系数实虚拆分，结果叶仅 Fr/纯参数 SymRat。"""
    re_m, im_m = {}, {}
    for k, c in p.monos.items():
        r, i_ = coef_re_im(c)
        if not coef_zero(r):
            re_m[k] = r
        if not coef_zero(i_):
            im_m[k] = i_
    return Poly(p.vars, re_m), Poly(p.vars, im_m)
