"""Sturm 序列与实根隔离（纯精确有理算术，零数值近似）。

提供：
- sturm_sequence：Sturm 链（对无平方部分计算）；
- real_root_count：区间内不同实根个数（重数不计）；
- isolate_real_roots：全部不同实根的隔离区间（有理端点，每区间恰一根）。
"""

from fractions import Fraction as Fr

from cas.poly import Poly
from cas.factor import squarefree_decomp


def _eval_at(p, x, val):
    """Poly 在有理点 val 的精确值。"""
    idx = p.vars.index(x)
    acc = Fr(0)
    for exps, c in p.monos.items():
        acc += Fr(c) * (val ** exps[idx])
    return acc


def squarefree_part(p):
    """不同因子之积（无平方部分），首一。"""
    x = p.vars[0]
    out = Poly.one(p.vars)
    for g, _mult in squarefree_decomp(p):
        out = out * g
    lc = out.lc(x)
    return out.scalar(Fr(1) / lc) if lc else out


def sturm_sequence(p):
    """p（无平方部分）的 Sturm 链 [s0, s1, ...]，s_{i+1} = -rem(s_{i-1}, s_i)。"""
    x = p.vars[0]
    seq = [p, p.deriv(x)]
    while not seq[-1].is_zero() and seq[-1].degree(x) > 0:
        _, r = seq[-2].udivmod(seq[-1])
        seq.append(-r)
    return seq


def _signs_at(seq, x, val):
    """Sturm 链在 val 的符号序列（零点剔除，标准约定）。"""
    out = []
    for s in seq:
        v = _eval_at(s, x, val)
        if v != 0:
            out.append(1 if v > 0 else -1)
    return out


def _variations(signs):
    n = 0
    for a, b in zip(signs, signs[1:]):
        if a != b:
            n += 1
    return n


def real_root_count(p, lo, hi):
    """p 的不同实根在 (lo, hi] 的个数（Sturm 定理）。"""
    x = p.vars[0]
    seq = sturm_sequence(squarefree_part(p))
    return _variations(_signs_at(seq, x, lo)) - _variations(_signs_at(seq, x, hi))


def _cauchy_bound(p):
    x = p.vars[0]
    lc = abs(p.lc(x))
    m = max((abs(Fr(c)) for c in p.monos.values()), default=Fr(0))
    return Fr(1) + m / lc


def isolate_real_roots(p):
    """全部不同实根的隔离区间：[(lo, hi)]，有理端点，开区间内恰一根，升序。"""
    x = p.vars[0]
    sq = squarefree_part(p)
    if sq.degree(x) <= 0:
        return []
    seq = sturm_sequence(sq)
    B = _cauchy_bound(sq)
    total = _variations(_signs_at(seq, x, -B)) - _variations(_signs_at(seq, x, B))
    if total == 0:
        return []
    out = []

    def rec(lo, hi, n):
        if n == 0:
            return
        if n == 1:
            out.append((lo, hi))
            return
        mid = (lo + hi) / 2
        # 中点处链值全非零（无平方部分保证根不在边界重合时二分仍安全）
        nl = _variations(_signs_at(seq, x, lo)) - _variations(_signs_at(seq, x, mid))
        nh = n - nl
        rec(lo, mid, nl)
        rec(mid, hi, nh)

    rec(-B, B, total)
    return out


def root_multiplicities(p):
    """[(无平方因子 g, 重数 mult)]（squarefree_decomp 透传）。"""
    return squarefree_decomp(p)
