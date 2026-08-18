from fractions import Fraction as Fr

from cas.errors import PolyError
from cas.factor import squarefree_decomp, factor
from cas.poly import Poly


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
    for g0, k0 in squarefree_decomp(g):
        _, facs = factor(g0)
        for h, _ in facs:
            sqf.append((h, k0))
    out, whole = [], []
    if not r.is_zero():
        _split_frac(r, sqf, x, out, whole)
    for w in whole:
        q = q + w
    return q, out