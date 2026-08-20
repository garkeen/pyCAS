from fractions import Fraction as Fr

from cas.errors import PolyError
from cas.factor import squarefree_decomp, factor
from cas.poly import Poly, SymRat, _rat_inv, _rat_add, _rat_mul, div_exact, is_param_poly


def _poly_sqrt(p):
    """Fr 系数 Poly 完全平方 -> sqrt（Poly）；否则 None。

    主变量长除法平方根：q 最高项系数 s = sqrt(p 最高项系数)（低变量递归），
    后续项由 cur = p − q² 的最高项除以 2·q 最高项系数逐项解出；
    末尾 q·q == p 精确复核（交叉项如 (a-b)² 展开后仍被正确处理）。
    """
    from math import isqrt

    if p.is_zero():
        return p
    if not p.vars:
        c = p.const_val()
        if c < 0:
            return None
        a = isqrt(c.numerator)
        b = isqrt(c.denominator)
        if a * a == c.numerator and b * b == c.denominator:
            return Poly((), {(): Fr(a, b)})
        return None
    x = p.vars[0]

    def _lc_poly(q):
        d = q.degree(x)
        return Poly(q.vars[1:], {k[1:]: v for k, v in q.monos.items() if k[0] == d})

    cur = p
    q = Poly.zero(p.vars)
    while not cur.is_zero():
        d = cur.degree(x)
        dq = q.degree(x) if not q.is_zero() else -1
        if dq == -1:
            if d % 2:
                return None
            slc = _poly_sqrt(_lc_poly(cur))
            if slc is None:
                return None
            m = Poly(p.vars, {(d // 2,) + k: v for k, v in slc.monos.items()})
        else:
            dr = d - dq
            if dr < 0 or dr >= dq:
                return None
            try:
                mc = div_exact(_lc_poly(cur), _lc_poly(q).scalar(Fr(2)))
            except PolyError:
                return None
            if mc.is_zero():
                return None
            m = Poly(p.vars, {(dr,) + k: v for k, v in mc.monos.items()})
        q_old = q
        q = q + m
        cur = cur - q_old.scalar(Fr(2)) * m - m * m
    if q * q == p:
        return q
    return None


def _coef_is_square(c):
    if isinstance(c, SymRat):
        return _poly_sqrt(c.num) is not None and _poly_sqrt(c.den) is not None
    from math import isqrt

    a = isqrt(c.numerator)
    b = isqrt(c.denominator)
    return a * a == c.numerator and b * b == c.denominator


def _coef_sqrt(c):
    if isinstance(c, SymRat):
        return SymRat(_poly_sqrt(c.num), _poly_sqrt(c.den))
    from math import isqrt

    return Fr(isqrt(c.numerator), isqrt(c.denominator))


def _param_factor_quad(g, x):
    """ℚ(params) 上 monic 二次因子的不可约分解。

    判别式完全平方 -> 两个互素线性因子（根 ∈ 系数域）；否则 None（不可约）。
    """
    pc = g.monos.get((1,), Fr(0))
    qc = g.monos.get((0,), Fr(0))
    D = _rat_add(_rat_mul(pc, pc), _rat_mul(Fr(-4), qc))
    if _coef_is_square(D):
        sd = _coef_sqrt(D)
        half = Fr(1) / 2
        r1 = _rat_mul(_rat_add(_rat_mul(Fr(-1), pc), sd), half)
        r2 = _rat_mul(_rat_add(_rat_mul(Fr(-1), pc), _rat_mul(Fr(-1), sd)), half)
        return [
            Poly((x,), {(1,): Fr(1), (0,): _rat_mul(Fr(-1), r1)}),
            Poly((x,), {(1,): Fr(1), (0,): _rat_mul(Fr(-1), r2)}),
        ]
    return None


def _param_factors(g, x):
    """ℚ(params) 上单变量多项式分解为互素不可约因子。

    因子保留首项系数（与 ℚ 域 factor 的 primitive 部分一致，积分器内部
    自行按 lc 规范化）；可约二次的 lc 作为 content 返回，由 apart 折入
    ctotal 校正分子。返回 (因子列表, content 或 None)。
    """
    n = g.degree(x)
    if n <= 0:
        return [], None
    if n == 1:
        return [g], None
    if n == 2:
        lc = g.lc(x)
        facs = _param_factor_quad(g.scalar(_rat_inv(lc)), x)
        if facs is None:
            return [g], None
        return facs, lc
    raise PolyError(f"parameter-domain factorization: degree {n} unsupported")


def _xgcd(a, b, x):
    r0, r1 = a, b
    s0, s1 = Poly.one(a.vars), Poly.zero(a.vars)
    t0, t1 = Poly.zero(a.vars), Poly.one(a.vars)
    while not r1.is_zero():
        q, r = r0.udivmod(r1)
        r0, r1 = r1, r
        s0, s1 = s1, s0 - q * s1
        t0, t1 = t1, t0 - q * t1
    if r0.is_zero():
        return Poly.zero(a.vars), Poly.zero(a.vars)
    lc = r0.lc(x)
    return s0.scalar(Fr(1) / lc), t0.scalar(Fr(1) / lc)


def _apart_power(f, g, k, x):
    out = []
    whole = Poly.zero(f.vars)
    cur = f
    j = k
    while not cur.is_zero() and j >= 1:
        qq, rr = cur.udivmod(g)
        out.append((rr, g, j))
        cur = qq
        j -= 1
    if not cur.is_zero():
        whole = cur
    return out, whole


def _split_frac(r, sqf, x, out, whole):
    if len(sqf) == 1:
        g0, k0 = sqf[0]
        terms, w = _apart_power(r, g0, k0, x)
        out.extend(terms)
        if not w.is_zero():
            whole.append(w)
        return
    mid = len(sqf) // 2
    left, right = sqf[:mid], sqf[mid:]
    a = Poly.one(r.vars)
    for g0, k0 in left:
        a = a * g0 ** k0
    b = Poly.one(r.vars)
    for g0, k0 in right:
        b = b * g0 ** k0
    s, t = _xgcd(a, b, x)
    _split_frac(r * s, right, x, out, whole)
    _split_frac(r * t, left, x, out, whole)


def apart(f, g, x=None):
    if len(f.vars) != 1 or f.vars != g.vars:
        raise PolyError("univariate only")
    x = f.vars[0] if x is None else x
    if g.is_zero():
        raise PolyError("division by zero")
    q, r = f.udivmod(g)
    sqf = []
    ctotal = Fr(1)
    for g0, k0 in squarefree_decomp(g):
        if is_param_poly(g0):
            # 参数域：不可约因子（1 次直接；2 次判判别式；更高阶暂不支持）。
            # 可约二次的首项系数作为 content 折入 ctotal，校正分子。
            facs, pc = _param_factors(g0, x)
            if pc is not None:
                ctotal = _rat_mul(ctotal, pc)
            for h in facs:
                sqf.append((h, k0))
        else:
            c0, facs = factor(g0)
            ctotal = ctotal * c0
            for h, _ in facs:
                sqf.append((h, k0))
    out, whole = [], []
    if not r.is_zero():
        if ctotal != 1:
            r = r.scalar(_rat_inv(ctotal))
        _split_frac(r, sqf, x, out, whole)
    for w in whole:
        q = q + w
    return q, out