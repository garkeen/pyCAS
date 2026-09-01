# -*- coding: utf-8 -*-
"""单变量实根隔离（最简 CAD 的投影骨架，架构 §6.4 / §8"结式引擎即可起步"）。

全程精确有理算术，无近似：
· Cauchy 界圈定全部实根；
· Sturm 序列 + 符号变差数给开区间内实根个数（Sturm 定理）；
· 二分把每个实根隔离进互不相交的有理端点区间——无理根得开区间
  （根严格在内、端点非根），有理根直接精确命中记为 (r, r)。

只对 ℚ 上的单变量无平方多项式实现；这是实闭域上可判定片段的地基，
与超越根（拒答表第三行，UNDECIDABLE）无关。
"""

from fractions import Fraction as Fr

from cas.domains.poly import (Poly, p_deriv, p_neg, p_divmod_field,
                              p_gcd_univar)
from cas.domains.polytools import p_deg, p_lc, p_monic, p_div_exact


# ---------------------------------------------------------------------------
# 精确求值与符号
# ---------------------------------------------------------------------------

def p_eval_at(p: Poly, x0) -> Fr:
    """单变量稀疏多项式在有理点 x0 的精确值（Horner）。"""
    coefs = {}
    for k, c in p.monos:
        coefs[k[0]] = Fr(c)
    if not coefs:
        return Fr(0)
    deg = max(coefs)
    acc = Fr(0)
    for e in range(deg, -1, -1):
        acc = acc * x0 + coefs.get(e, Fr(0))
    return acc


def coef_sign(v) -> int:
    if v > 0:
        return 1
    if v < 0:
        return -1
    return 0


# ---------------------------------------------------------------------------
# Sturm 序列与变差数
# ---------------------------------------------------------------------------

def sturm_sequence(ring, p: Poly):
    """标准 Sturm 链：p0=p, p1=p', p_{k+1} = −(p_{k−1} mod p_k)。"""
    seq = [p, p_deriv(ring, p, 0)]
    while True:
        _, r = p_divmod_field(ring, seq[-2], seq[-1], 0)
        if r.is_zero():
            break
        seq.append(p_neg(ring, r))
    return seq


def sign_variations(seq, x0) -> int:
    """Sturm 链在 x0 处的符号变差数（逐项求值，零项忽略）。"""
    prev = None
    changes = 0
    for q in seq:
        s = coef_sign(p_eval_at(q, x0))
        if s == 0:
            continue
        if prev is not None and s != prev:
            changes += 1
        prev = s
    return changes


def count_roots(seq, p: Poly, a, b) -> int:
    """Sturm 定理：(a, b] 内不同实根个数 = V(a) − V(b)。

    V 零项忽略，故端点恰为根时该式仍对开/闭端点给出正确计数。"""
    return sign_variations(seq, a) - sign_variations(seq, b)


def count_roots_open(seq, p: Poly, a, b) -> int:
    """开区间 (a, b) 内不同实根个数（右端点为根时扣除）。"""
    n = count_roots(seq, p, a, b)
    if coef_sign(p_eval_at(p, b)) == 0:
        n -= 1
    return n


# ---------------------------------------------------------------------------
# Cauchy 界与二分隔离
# ---------------------------------------------------------------------------

def cauchy_bound(p: Poly) -> Fr:
    """全部实根绝对值 ≤ 1 + max|c_i/lc|（i < deg）。"""
    lc = Fr(p_lc(p, 0))
    m = Fr(0)
    top = p_deg(p, 0)
    for k, c in p.monos:
        if k[0] < top:
            v = abs(Fr(c) / lc)
            if v > m:
                m = v
    return Fr(1) + m


def isolate_squarefree(ring, p: Poly):
    """无平方单变量多项式的实根隔离。

    返回升序、两两不交且**相邻严格留隙**（b_i < a_{i+1}）的区间列表：
    无理根为 (a, b)（a<b，根严格在内），有理根为 (r, r)。二分的终止由
    根个数递减保证；留隙由 _refine_gaps 向各自根收缩保证（根互异、间距为正，
    几何收敛必停），供 CAD 在间隙中取无根样本点。"""
    if p_deg(p, 0) <= 0:
        return []
    seq = sturm_sequence(ring, p)
    M = cauchy_bound(p)
    out = []
    _iso_open(seq, p, Fr(-M), Fr(M), out)
    out.sort(key=lambda iv: iv[0])
    return _refine_gaps(seq, p, out)


def _shrink(seq, p: Poly, iv):
    """把单根隔离区间向根收缩一步（退化 (r, r) 不动）。"""
    a, b = iv
    if a == b:
        return iv
    mid = (a + b) / 2
    if coef_sign(p_eval_at(p, mid)) == 0:
        return (mid, mid)                    # 恰好命中精确有理根
    if count_roots_open(seq, p, a, mid) >= 1:
        return (a, mid)
    return (mid, b)


def _refine_gaps(seq, p: Poly, ivs):
    """收缩相邻触碰/交叠的区间，直到每对相邻区间严格留隙。"""
    changed = True
    while changed:
        changed = False
        for i in range(len(ivs) - 1):
            if ivs[i][1] >= ivs[i + 1][0]:
                ivs[i] = _shrink(seq, p, ivs[i])
                ivs[i + 1] = _shrink(seq, p, ivs[i + 1])
                changed = True
    return ivs


def _iso_open(seq, p: Poly, a, b, out):
    """隔离开区间 (a, b) 内的全部实根（端点 a、b 本身不计入）。"""
    n = count_roots_open(seq, p, a, b)
    if n == 0:
        return
    if n == 1:
        out.append((a, b))
        return
    mid = (a + b) / 2
    if coef_sign(p_eval_at(p, mid)) == 0:
        out.append((mid, mid))            # 精确有理根
        _iso_open(seq, p, a, mid, out)
        _iso_open(seq, p, mid, b, out)
    else:
        _iso_open(seq, p, a, mid, out)
        _iso_open(seq, p, mid, b, out)


def squarefree_part(ring, p: Poly) -> Poly:
    """无平方部分 p / gcd(p, p')：与原式同根集（均单根）。"""
    if p_deg(p, 0) <= 0:
        return p
    g = p_gcd_univar(ring, p, p_deriv(ring, p, 0))
    if g.is_zero() or p_deg(g, 0) == 0:
        return p_monic(ring, p)
    return p_div_exact(ring, p_monic(ring, p), g)


def divisors(n):
    """n 的正因子列表（试除到 √n）。有理根定理候选枚举的公共通道。"""
    n = abs(n)
    if n == 0:
        return []
    out = []
    d = 1
    while d * d <= n:
        if n % d == 0:
            out.append(d)
            if d != n // d:
                out.append(n // d)
        d += 1
    return out


def rational_roots(p: Poly):
    """精确有理根全集（有理根定理），升序去重。

    清分母成整系数后，有理根必为 ±(常数项因子)/(首项系数因子)，有限候选
    逐个精确验证——这是可判定碎片，不是近似。"""
    if p_deg(p, 0) <= 0:
        return []
    from math import gcd
    coefs = {k[0]: Fr(c) for k, c in p.monos}
    lcm = 1
    for c in coefs.values():
        lcm = lcm * c.denominator // gcd(lcm, c.denominator)
    ic = {e: int(coefs[e] * lcm) for e in coefs}
    roots = []
    while ic and ic.get(0, 0) == 0:          # 0 根：逐个降幂
        roots.append(Fr(0))
        ic = {e - 1: c for e, c in ic.items() if e > 0}
    if not ic:
        return sorted(set(roots))
    deg = max(ic)
    a0 = ic.get(0, 0)
    an = ic[deg]
    cands = set()
    for d in divisors(a0):
        for e in divisors(an):
            cands.add(Fr(d, e))
            cands.add(Fr(-d, e))
    for r in cands:
        if coef_sign(p_eval_at(p, r)) == 0:
            roots.append(r)
    return sorted(set(roots))


def real_roots_intervals(ring, p: Poly):
    """任意单变量多项式的实根隔离。

    有理根由有理根定理精确命中为 (r, r)；它们把实轴切成开区间，无理根
    在各自开区间内走 Sturm 隔离（被限制在间隙里，与有理根天然不相交）。
    结果升序、互不相交、相邻严格留隙。"""
    if p_deg(p, 0) <= 0:
        return []
    sf = squarefree_part(ring, p)
    seq = sturm_sequence(ring, sf)
    rat = rational_roots(sf)
    M = cauchy_bound(sf)
    ivs = [(r, r) for r in rat]
    bounds = [Fr(-M)] + rat + [Fr(M)]
    for i in range(len(bounds) - 1):
        _iso_open(seq, sf, bounds[i], bounds[i + 1], ivs)   # 间隙内无理根
    ivs.sort(key=lambda iv: iv[0])
    return _refine_gaps(seq, sf, ivs)
