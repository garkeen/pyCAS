"""三角多项式层：Chebyshev/多角度基规范形（sin/cos 幂积 → ∑(aₙ·sin nx + bₙ·cos nx) 唯一线性组合）。"""

from fractions import Fraction as Fr
from math import comb

from cas import term as T
from cas.term import S, N, Expr, Sym, Int, Const, is_num, num_val


def _cadd(u, v):
    return (u[0] + v[0], u[1] + v[1])


def _cmul(u, v):
    return (u[0] * v[0] - u[1] * v[1], u[0] * v[1] + u[1] * v[0])


def _cscale(u, f):
    return (u[0] * f, u[1] * f)


def _i_pow_inv(m):
    """(2i)^-m = 2^-m · (-i)^m：返回 (-i)^m 的 (re, im)。"""
    r = m % 4
    if r == 0:
        return (Fr(1), Fr(0))
    if r == 1:
        return (Fr(0), Fr(-1))
    if r == 2:
        return (Fr(-1), Fr(0))
    return (Fr(0), Fr(1))


def _sin_pow(m):
    """(sin x)^m 的 Laurent 展开：Σ_j C(m,j)·(-1)^j·z^(m-2j) / (2i)^m。"""
    out = {}
    f = Fr(1) / (Fr(2) ** m)
    ip = _i_pow_inv(m)
    for j in range(m + 1):
        c = Fr(comb(m, j)) * (-1) ** j
        k = m - 2 * j
        v = _cmul(_cscale(ip, c * f), (1, 0))
        out[k] = _cadd(out.get(k, (Fr(0), Fr(0))), v)
    return out


def _cos_pow(m):
    """(cos x)^m 的 Laurent 展开：Σ_j C(m,j)·z^(m-2j) / 2^m。"""
    out = {}
    f = Fr(1) / (Fr(2) ** m)
    for j in range(m + 1):
        c = Fr(comb(m, j))
        k = m - 2 * j
        v = (c * f, Fr(0))
        out[k] = _cadd(out.get(k, (Fr(0), Fr(0))), v)
    return out


def _ladd(a, b):
    out = dict(a)
    for k, v in b.items():
        out[k] = _cadd(out.get(k, (Fr(0), Fr(0))), v)
    return {k: v for k, v in out.items() if v != (Fr(0), Fr(0))}


def _lmul(a, b):
    out = {}
    for k1, v1 in a.items():
        for k2, v2 in b.items():
            k = k1 + k2
            out[k] = _cadd(out.get(k, (Fr(0), Fr(0))), _cmul(v1, v2))
    return {k: v for k, v in out.items() if v != (Fr(0), Fr(0))}


def _freq(u, x):
    """arg 的整数频率：x -> 1；k*x（k 为 >=1 的整数值系数，任意排序）-> k。"""
    if u is x:
        return 1
    if isinstance(u, Expr) and u.head.name == "Times" and len(u.args) == 2:
        for a, b in ((u.args[0], u.args[1]), (u.args[1], u.args[0])):
            if b is x and is_num(a):
                f = num_val(a)
                if f.denominator == 1 and f >= 1:
                    return int(f)
    return None


def _expand(t, x):
    """term → Laurent 系数 dict（sin/cos 幂积多项式）；非此形态返回 None。

    Sin/Cos 接受整数频率参数（cos(2*x) 等）——多角度基输出须可再归约
    （规范形幂等性），否则 equivalent 的三角层对谐波形态失明。
    """
    if t is x:
        return None
    if is_num(t):
        return {0: (num_val(t), Fr(0))}
    if isinstance(t, Const):
        return None
    if isinstance(t, Expr):
        n = t.head.name
        if n in ("Sin", "Cos") and len(t.args) == 1:
            m = _freq(t.args[0], x)
            if m is None:
                return None
            if n == "Sin":
                return {m: (Fr(0), Fr(-1, 2)), -m: (Fr(0), Fr(1, 2))}
            return {m: (Fr(1, 2), Fr(0)), -m: (Fr(1, 2), Fr(0))}
        if n == "Plus":
            acc = None
            for a in t.args:
                la = _expand(a, x)
                if la is None:
                    return None
                acc = la if acc is None else _ladd(acc, la)
            return acc or {}
        if n == "Times":
            acc = {0: (Fr(1), Fr(0))}
            for a in t.args:
                la = _expand(a, x)
                if la is None:
                    return None
                acc = _lmul(acc, la)
            return acc
        if n == "Power":
            b, e = t.args
            if isinstance(e, Int) and e.v >= 0 and isinstance(b, Expr) and b.head.name in ("Sin", "Cos"):
                m = _freq(b.args[0], x)
                if m is None:
                    return None
                base = _sin_pow(e.v) if b.head.name == "Sin" else _cos_pow(e.v)
                return {k * m: v for k, v in base.items()}
            return None
    return None


def trig_reduce(t, x):
    """sin/cos 幂积多项式 → 多角度基线性组合（唯一表示）。非幂积形态返回 None。"""
    la = _expand(t, x)
    if la is None:
        return None
    parts = []
    k0 = la.get(0, (Fr(0), Fr(0)))
    if k0[0] != 0:
        parts.append(N(k0[0]))
    kmax = max((k for k in la), default=0)
    for k in range(1, kmax + 1):
        cp = la.get(k, (Fr(0), Fr(0)))
        cm = la.get(-k, (Fr(0), Fr(0)))
        a = cp[0] + cm[0]
        b = -(cp[1] - cm[1])
        if a != 0:
            fac = [N(a)]
            if k == 1:
                fac.append(T.cos(x))
            else:
                fac.append(T.cos(T.times(N(k), x)))
            parts.append(T.times(*fac) if len(fac) > 1 else fac[0])
        if b != 0:
            fac = [N(b)]
            if k == 1:
                fac.append(T.sin(x))
            else:
                fac.append(T.sin(T.times(N(k), x)))
            parts.append(T.times(*fac) if len(fac) > 1 else fac[0])
    if not parts:
        return T.ZERO
    if len(parts) == 1:
        return parts[0]
    return T.mk(S("Plus"), tuple(parts))


def trig_equivalent(a, b, x):
    """两个 sin/cos 幂积多项式是否恒等（多角度基系数比较）。"""
    ra = trig_reduce(a, x)
    rb = trig_reduce(b, x)
    if ra is None or rb is None:
        return None
    return ra is rb