"""N1 根式规范化（M78.4；manip.spad zroot(:83)/nthr/iroot(:90)/froot(:182)
的算法逻辑，落地为本项目 mk 环规范化的组成部分）。

职责：有理底 n 次根的构造期归一——f^(1/n) = c·r^(1/m) 的 [m,c,r]
记录形：
  · content 抽整 / sqfree 重数 mod n（素重数 μ·p 在模 q 下的整数部
    进系数、余部进残余被开方数）；
  · 指标归约：残余重数与 q 的最大公因 d>1 时指标降为 m=q/d；
  · 同次合并：√a·√b → √(ab)（正有理底无条件成立；负底奇指标同样
    合法；一般复底分支破裂不合并——与 contract.py 同一条诚实纪律）。

边界（诚实声明）：
  · 负底仅奇指标折叠（实数语义）；偶指标负底非实数，不折叠，
    主支 proviso 体系接入后再议；
  · 整数试除上限 10^6，超出诚实放弃（保持原名词，绝不静默错）。
"""

from fractions import Fraction as Fr
from math import gcd

from cas.term import S, N, Expr, Rat, is_num, num_val, mk

_FACTOR_CAP = 10 ** 6


def _factor_int(n):
    """|n|>1 试除分解 {素数: 重数}；超上限诚实返回 None。"""
    n = abs(n)
    out = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            out[d] = out.get(d, 0) + 1
            n //= d
        d += 1 if d == 2 else 2
    if n > 1:
        if n > _FACTOR_CAP:
            return None
        out[n] = out.get(n, 0) + 1
    return out


def _pool_val(pool):
    v = Fr(1)
    for pm, e in pool.items():
        v *= Fr(pm) ** e
    return v


def split_radical(bv, p, q):
    """bv^(p/q) -> c·r^(1/m) 项（[m,c,r] 规范形）。

    返回 None = 已是规范形或诚实不可折叠（大数/偶指标负底）。
    前置：p/q 已约简（f.denominator>1 保证），q ≥ 2。
    """
    if q <= 0 or p <= 0 or not isinstance(bv, Fr):
        return None
    sign = 1
    if bv < 0:
        if q % 2 == 0:
            return None
        sign = -1
        bv = -bv
    fn = _factor_int(bv.numerator)
    if fn is None:
        return None
    fd = _factor_int(bv.denominator)
    if fd is None:
        return None
    mu_map = dict(fn)
    for pm, mu in fd.items():
        mu_map[pm] = mu_map.get(pm, 0) - mu
    # μ·p = s·q + t：整数部进系数池，余部进残余池
    s_pool, res = {}, {}
    for pm, mu in mu_map.items():
        tot = mu * p
        s, t = divmod(tot, q)
        if s:
            s_pool[pm] = s
        if t:
            res[pm] = t
    g = gcd(q, gcd(*res.values()) if res else q)
    m = q // g
    r_pool = {pm: t // g for pm, t in res.items()}
    cval = _pool_val(s_pool) * sign
    rval = _pool_val(r_pool)
    if not res:
        return N(cval)
    if cval == 1 and rval == bv and m == q:
        return None
    parts = []
    if cval != 1:
        parts.append(N(cval))
    parts.append(mk(S("Power"), (N(rval), N(Fr(1, m)))))
    return parts[0] if len(parts) == 1 else mk(S("Times"), tuple(parts))


def merge_same_index(args):
    """Times 因子中同指标数值根式合并。返回新 tuple 或原 tuple
    （同一对象 = 无合并）。每次合并组内因子数严格减少，终止性保证。
    """
    from cas.term import mk

    groups = {}
    keep = []
    changed = False
    for a in args:
        hit = False
        if (isinstance(a, Expr) and a.head.name == "Power"
                and isinstance(a.args[1], Rat)
                and a.args[1].f.denominator > 1
                and is_num(a.args[0])):
            bv = num_val(a.args[0])
            if isinstance(bv, Fr):
                p_, q_ = a.args[1].f.numerator, a.args[1].f.denominator
                if p_ > 0 and (bv > 0 or q_ % 2 == 1):
                    groups.setdefault(q_, []).append((bv, p_))
                    hit = True
        if not hit:
            keep.append(a)
    for q_, lst in groups.items():
        if len(lst) < 2:
            continue
        changed = True
        acc = Fr(1)
        for bv, p_ in lst:
            acc *= bv ** p_
        keep.append(mk(S("Power"), (N(acc), N(Fr(1, q_)))))
    if not changed:
        return args
    return tuple(keep)
