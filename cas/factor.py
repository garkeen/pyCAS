from fractions import Fraction as Fr
from math import gcd
import random

from cas.errors import PolyError
from cas.poly import Poly, ugcd


def squarefree_decomp(f):
    if len(f.vars) != 1 or f.is_zero():
        raise PolyError("univariate non-zero required")
    x = f.vars[0]
    g = ugcd(f, f.deriv(x))
    if g.is_zero():
        return []
    w = f.udivmod(g)[0]
    out = []
    i = 1
    while not (w.is_const() and w.const_val() == 1):
        y = ugcd(w, g)
        z = w.udivmod(y)[0]
        if not (z.is_const() and z.const_val() == 1):
            out.append((z, i))
        w = y
        if g.is_zero():
            break
        g = g.udivmod(y)[0]
        i += 1
    return out


def _trim(a):
    while a and a[0] == 0:
        a = a[1:]
    return a


def _mod_sub(a, b, p):
    return _mod_add(a, [(-x) % p for x in b], p)


def _mod_add(a, b, p):
    n = max(len(a), len(b))
    out = [0] * n
    offa = n - len(a)
    offb = n - len(b)
    for i in range(len(a)):
        out[offa + i] = a[i]
    for j in range(len(b)):
        out[offb + j] = (out[offb + j] + b[j]) % p
    return _trim(out)


def _mod_mul(a, b, p):
    out = [0] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        for j, bj in enumerate(b):
            out[i + j] = (out[i + j] + ai * bj) % p
    return _trim(out)


def _mod_divmod(a, b, p):
    if not b:
        raise ZeroDivisionError("mod-p division by zero")
    q = [0] * max(0, len(a) - len(b) + 1)
    r = list(a)
    inv = pow(b[0], p - 2, p)
    da = len(a) - 1
    while len(r) >= len(b) and r:
        t = r[0] * inv % p
        q[da - (len(r) - 1)] = t
        for i in range(len(b)):
            r[i] = (r[i] - t * b[i]) % p
        r = _trim(r)
    return _trim(q), _trim(r)


def _monic(a, p):
    if not a:
        return a
    lc = pow(a[0], p - 2, p)
    return [c * lc % p for c in a]


def _mod_gcd(a, b, p):
    a, b = _trim(list(a)), _trim(list(b))
    if not a:
        return _monic(b, p)
    if not b:
        return _monic(a, p)
    while b:
        _, r = _mod_divmod(a, b, p)
        a, b = b, r
    return _monic(a, p)


def _mod_xgcd(a, b, p):
    r0, r1 = list(a), list(b)
    s0, s1 = [1], [0]
    t0, t1 = [0], [1]
    while r1:
        q, r = _mod_divmod(r0, r1, p)
        r0, r1 = r1, r
        s0, s1 = s1, _mod_sub(s0, _mod_mul(q, s1, p), p)
        t0, t1 = t1, _mod_sub(t0, _mod_mul(q, t1, p), p)
    if not r0:
        return [1], [], []
    lc = r0[0]
    inv = pow(lc, p - 2, p)
    return (
        [c * inv % p for c in r0],
        [c * inv % p for c in s0],
        [c * inv % p for c in t0],
    )


def _mod_pow(x, e, m, p):
    res = [1]
    base = _mod_divmod(_trim(list(x)), m, p)[1]
    while e:
        if e & 1:
            res = _mod_divmod(_mod_mul(res, base, p), m, p)[1]
        base = _mod_divmod(_mod_mul(base, base, p), m, p)[1]
        e >>= 1
    return res


def _modp_poly(f, p):
    x = f.vars[0]
    d = f.degree(x)
    cs = {}
    for k, v in f.monos.items():
        cs[k[0]] = v
    out = []
    for i in range(d, -1, -1):
        v = cs.get(i, Fr(0))
        out.append(v.numerator % p * pow(v.denominator % p, p - 2, p) % p)
    return _trim(out)


def _ddf(f, p):
    out = []
    rem = list(f)
    if not rem:
        return out
    t = [1, 0]
    k = 1
    while len(rem) > 2 * k and len(rem) > 1:
        t = _mod_pow(t, p, rem, p)
        g = _mod_gcd(rem, _mod_sub(t, [1, 0], p), p)
        if len(g) > 1:
            out.append((k, g))
            rem = _mod_divmod(rem, g, p)[0]
            t = _mod_divmod(t, rem, p)[1]
        k += 1
    if len(rem) > 1:
        out.append((len(rem) - 1, rem))
    return out


def _cz_split(g, p, d, rng):
    deg = len(g) - 1
    if deg == d:
        return [g]
    while True:
        r = [rng.randrange(p) for _ in range(deg)]
        r = _trim(r)
        if len(r) < 2:
            r = [1, 0]
        e = (pow(p, d) - 1) // 2
        h = _mod_pow(r, e, g, p)
        h = _mod_sub(h, [1], p)
        g1 = _mod_gcd(g, h, p)
        if 1 < len(g1) < len(g):
            return _cz_split(g1, p, d, rng) + _cz_split(
                _mod_divmod(g, g1, p)[0], p, d, rng
            )


def _choose_prime(f, rng, n=4):
    """收集 n 个"合适"素数候选（不整除 lc、mod p 无重根、DDF 分解）。

    返回 [(p, facs)]，facs = mod p 下非平凡不可约因子列表。
    """
    x = f.vars[0]
    lc_num = abs(f.lc(x).numerator)
    fp2 = None
    p = 3
    candidates = []
    while len(candidates) < n:
        if _is_prime(p) and lc_num % p != 0:
            fp = _modp_poly(f, p)
            fp2 = _modp_poly(f.deriv(x), p)
            if _mod_gcd(fp, fp2, p) == [1]:
                facs = []
                for d, g in _ddf(fp, p):
                    facs.extend(_cz_split(g, p, d, rng))
                facs = [g for g in facs if len(g) > 1]
                candidates.append((p, facs))
                if len(facs) < 15:
                    break
        p += 2
    if not candidates:
        raise PolyError("no suitable prime")
    return candidates


def _add_int(a, b):
    n = max(len(a), len(b))
    out = [0] * n
    offa = n - len(a)
    offb = n - len(b)
    for i in range(len(a)):
        out[offa + i] = a[i]
    for j in range(len(b)):
        out[offb + j] += b[j]
    return _trim(out)


def _sub_mod(a, b, m):
    n = max(len(a), len(b))
    out = [0] * n
    offa = n - len(a)
    offb = n - len(b)
    for i in range(len(a)):
        out[offa + i] = a[i]
    for j in range(len(b)):
        out[offb + j] -= b[j]
    return _sym_mod(out, m)


def _add_mod(a, b, m):
    return _sym_mod(_add_int(a, b), m)


def _sym_mod(a, m):
    return _int_poly(a, m)


def _to_int(a, p):
    return [c % p for c in a]


def _trunc(a, pl):
    return _sym_mod(a, pl)


def _l1_norm(a):
    return sum(abs(c) for c in a)


def _is_prime(n):
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    d = 3
    while d * d <= n:
        if n % d == 0:
            return False
        d += 2
    return True


def _subsets(seq, k):
    out = []
    n = len(seq)

    def rec(start, chosen):
        if len(chosen) == k:
            out.append(tuple(chosen))
            return
        for i in range(start, n):
            chosen.append(seq[i])
            rec(i + 1, chosen)
            chosen.pop()

    rec(0, [])
    return out


def _hensel_step(m, f, g, h, s, t):
    M = m * m
    e = _sub_mod(f, _mul_int(g, h), M)
    q, r = _int_divmod(_mul_int(s, e), h)
    if any(c % m for c in r):
        raise PolyError("hensel step non-integral")
    q = _trunc(q, M)
    r = _trunc(r, M)
    u = _add_mod(_mul_int(t, e), _mul_int(q, g), M)
    G = _add_mod(g, u, M)
    H = _add_mod(h, r, M)
    u = _add_mod(_mul_int(s, G), _mul_int(t, H), M)
    b = _sub_mod(u, [1], M)
    c, d = _int_divmod(_mul_int(s, b), H)
    if any(c2 % m for c2 in d):
        raise PolyError("hensel bezout non-integral")
    c = _trunc(c, M)
    d = _trunc(d, M)
    u = _add_mod(_mul_int(t, b), _mul_int(c, G), M)
    S = _sub_mod(s, d, M)
    T = _sub_mod(t, u, M)
    return G, H, S, T


def _hensel(p, f, f_list, l):
    r = len(f_list)
    lc = f[0]
    if r == 1:
        inv = pow(lc, -1, p ** l)
        return [_trunc([c * inv % (p ** l) for c in f], p ** l)]
    m = p
    k = r // 2
    g = [lc % p]
    for f_i in f_list[:k]:
        g = _mod_mul(g, f_i, p)
    h = f_list[k]
    for f_i in f_list[k + 1 :]:
        h = _mod_mul(h, f_i, p)
    _, s, t = _mod_xgcd(g, h, p)
    g = _to_int(g, p)
    h = _to_int(h, p)
    s = _to_int(s, p)
    t = _to_int(t, p)
    d = 0
    while (1 << d) < l:
        d += 1
    for _ in range(d):
        g, h, s, t = _hensel_step(m, f, g, h, s, t)
        m = m * m
    return _hensel(p, g, f_list[:k], l) + _hensel(p, h, f_list[k:], l)


def _test_pl(fc, q, pl):
    if q > pl // 2:
        q = q - pl
    if not q:
        return True
    return fc % q == 0


def _int_poly(poly, p):
    out = []
    half = p // 2
    for c in poly:
        v = c % p
        if v > half:
            v -= p
        out.append(v)
    return _trim(out)


def _int_gcd_list(cs):
    g = 0
    for c in cs:
        g = gcd(g, abs(c))
    return g


def _mul_int(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        for j, bj in enumerate(b):
            out[i + j] += ai * bj
    return _trim(out)


def _int_divmod(a, b):
    if not b:
        raise ZeroDivisionError
    if len(a) < len(b):
        return [0], list(a)
    q = [0] * (len(a) - len(b) + 1)
    r = list(a)
    da = len(a) - 1
    while len(r) >= len(b) and r:
        if r[0] % b[0] != 0:
            return q, r
        t = r[0] // b[0]
        q[da - (len(r) - 1)] = t
        for i in range(len(b)):
            r[i] -= t * b[i]
        r = _trim(r)
    return q, r


def _coeffs(p):
    x = p.vars[0]
    d = p.degree(x)
    out = [0] * (d + 1)
    for k, v in p.monos.items():
        out[d - k[0]] = int(v)
    return out


def _poly_from_coeffs(cs, vars_):
    m = {}
    d = len(cs) - 1
    for i, c in enumerate(cs):
        if c != 0:
            m[(d - i,)] = c
    return Poly(vars_, m)


def _zassenhaus(f, rng):
    x = f.vars[0]
    n = f.degree(x)
    if n <= 1:
        return [f]
    candidates = _choose_prime(f, rng, 4)
    p, facs = min(candidates, key=lambda c: len(c[1]))
    facs = [_monic(g, p) for g in facs]
    facs = [g for g in facs if len(g) > 1]
    fc = _coeffs(f)
    A = max(abs(c) for c in fc)
    b = abs(f.lc(x).numerator)
    B = int((n + 1) ** 0.5 * 2 ** n * A * b) + 1
    l = 1
    pe = p
    while pe <= 2 * B:
        pe *= p
        l += 1
    pl = p ** l
    modular = _hensel(p, fc, facs, l)
    g = [_trunc(m, pl) for m in modular]
    T = set(range(len(g)))
    factors = []
    s = 1
    while 2 * s <= len(T):
        done = False
        for S in _subsets(sorted(T), s):
            if b == 1:
                q = 1
                for i in S:
                    q = q * g[i][-1] % pl
                if not _test_pl(fc[-1], q, pl):
                    continue
            else:
                G = [b]
                for i in S:
                    G = _mul_int(G, g[i])
                G = _trunc(G, pl)
                gc = _int_gcd_list(G)
                G = _trim([c // gc for c in G])
                q = G[-1]
                if q and fc[-1] % q != 0:
                    continue
            if b == 1:
                G = [b]
                for i in S:
                    G = _mul_int(G, g[i])
                G = _trunc(G, pl)
            H = [b]
            for i in T - set(S):
                H = _mul_int(H, g[i])
            H = _trunc(H, pl)
            if _l1_norm(G) * _l1_norm(H) <= B:
                gc = _int_gcd_list(G)
                G = _trim([c // gc for c in G])
                if G and G[0] < 0:
                    G = [-c for c in G]
                T = T - set(S)
                factors.append(G)
                hc = _int_gcd_list(H)
                H = _trim([c // hc for c in H])
                if H and H[0] < 0:
                    H = [-c for c in H]
                fc = H
                b = abs(H[0]) if H else 1
                done = True
                break
        if not done:
            s += 1
    out = [fc] if fc and len(fc) > 1 else []
    return [_poly_from_coeffs(g_, f.vars) for g_ in factors + out]


def factor(f, rng=None):
    if len(f.vars) != 1:
        raise PolyError("univariate only")
    x = f.vars[0]
    if f.is_zero():
        return Fr(0), []
    if rng is None:
        rng = random.Random(42)
    c, prim = f.primitive()
    if prim.degree(x) <= 0:
        return c, []
    factors = []
    for g, mult in squarefree_decomp(prim):
        if g.degree(x) <= 0:
            c = c * g.const_val() ** mult
            continue
        parts = _zassenhaus(g, rng)
        for h in parts:
            if h.degree(x) <= 0:
                continue
            hc, hp = h.primitive()
            if hp.degree(x) > 0:
                factors.append((hp, mult))
    total = Poly.one(f.vars)
    for h, m in factors:
        total = total * h ** m
    if total.is_zero():
        return c, factors
    if prim.lc(x) * total.lc(x) < 0:
        c = -c
    return c, factors


def factor_str(f, rng=None):
    c, factors = factor(f, rng)
    out = []
    if c != 1:
        out.append(str(c))
    for g, m in factors:
        s_ = str(g)
        if "+" in s_ or "-" in s_[1:]:
            s_ = f"({s_})"
        out.append(f"{s_}^{m}" if m > 1 else s_)
    return " * ".join(out) if out else str(c)
