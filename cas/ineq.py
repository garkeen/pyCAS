"""一元多项式不等式求解（Sturm 符号表 + 因式分解精确根）。

解集形态 = 区间并（Interval/Union 的简化表示）：
端点为精确有理数（线性因子给出）或根隔离区间描述子（高次不可约因子）。
"""

from fractions import Fraction as Fr

from cas.poly import Poly
from cas.simplify import expand
from cas.factor import factor
from cas.sturm import isolate_real_roots, real_root_count


def _roots_with_mult(p):
    """[(端点描述, 重数)]：端点 = Fr（精确根）或 (lo, hi) 隔离区间。"""
    x = p.vars[0]
    _c, facs = factor(p)
    entries = []
    for g, mult in facs:
        if g.degree(x) == 1:
            entries.append(((-g.const_val() / g.lc(x)), mult, g))
        else:
            for lo, hi in isolate_real_roots(g):
                entries.append(((lo, hi), mult, g))
    return _refine_disjoint(entries, x)


def _refine_disjoint(entries, x):
    """把重叠的隔离区间二分至两两不交（不同不可约因子的根互异，必终止）。"""
    changed = True
    while changed:
        changed = False
        entries.sort(key=lambda e: e[0] if isinstance(e[0], Fr) else e[0][0])
        for i in range(len(entries) - 1):
            pi = entries[i][0]
            pj = entries[i + 1][0]
            hi_i = pi if isinstance(pi, Fr) else pi[1]
            lo_j = pj if isinstance(pj, Fr) else pj[0]
            if hi_i > lo_j and not isinstance(pi, Fr):
                lo, hi = pi
                mid = (lo + hi) / 2
                g = entries[i][2]
                if real_root_count(g, lo, mid) >= 1:
                    entries[i] = ((lo, mid), entries[i][1], g)
                else:
                    entries[i] = ((mid, hi), entries[i][1], g)
                changed = True
    return entries


def _pos(e):
    """端点位置（排序用）。"""
    return e if isinstance(e, Fr) else (e[0] + e[1]) / 2


def solve_poly_ineq(term_, op, x):
    """解 term op 0（op ∈ Gt/Ge/Lt/Le）。返回 (区间列表, 字符串)。

    区间元素：(lo, hi, lo_incl, hi_incl)，lo/hi 为 Fr、None(±∞) 或
    根描述子 ("root", 因子串, lo, hi)。
    """
    p = Poly.from_term(expand(term_), (x,))
    if p.is_zero():
        ivs = [(None, None, False, False)] if op in ("Ge", "Le") else []
        return ivs, format_intervals(ivs)
    roots = sorted(_roots_with_mult(p), key=lambda e: _pos(e[0]))
    incl = op in ("Ge", "Le")
    want_pos = op in ("Gt", "Ge")

    def endpt(e):
        if isinstance(e, Fr):
            return e
        lo, hi = e
        return ("root", f"{lo}..{hi}", lo, hi)

    sign = 1 if p.lc(x) > 0 else -1
    # 区域从右到左：(r_k, +inf), (r_{k-1}, r_k), ..., (-inf, r_0)
    regions = []  # (lo_end, hi_end, sign) 端点为原始描述
    prev = None   # 右侧边界
    for pos_e, mult, _g in reversed(roots):
        regions.append((pos_e, prev, sign))
        if mult % 2 == 1:
            sign = -sign
        prev = pos_e
    regions.append((None, prev, sign))
    regions.reverse()

    picked = []
    for lo_e, hi_e, sg in regions:
        ok = (sg > 0) == want_pos
        if not ok:
            continue
        lo_v = None if lo_e is None else endpt(lo_e)
        hi_v = None if hi_e is None else endpt(hi_e)
        picked.append((lo_v, hi_v, False, False))
    # 根端点并入（Ge/Le 时 p(root)=0 满足）
    if incl:
        for pos_e, _mult, _g in roots:
            r = endpt(pos_e)
            picked.append((r, r, True, True))
    merged = _merge(picked)
    return merged, format_intervals(merged)


def _merge(ivs):
    """合并相邻区间；单点根 [r,r] 把左右开区间连成整体（如 (x−1)²≥0 → 全实轴）。"""

    def same(a, b):
        if a is None or b is None:
            return a is b
        if isinstance(a, Fr) and isinstance(b, Fr):
            return a == b
        return a == b

    ivs = list(ivs)
    changed = True
    while changed:
        changed = False
        for i, iv in enumerate(ivs):
            lo, hi, li, hi_i = iv
            if not (same(lo, hi) and li and hi_i):
                continue
            left = next((j for j, w in enumerate(ivs) if j != i and same(w[1], lo)), None)
            right = next((j for j, w in enumerate(ivs) if j != i and same(w[0], hi)), None)
            if left is not None and right is not None:
                l, r = ivs[left], ivs[right]
                ivs = [w for j, w in enumerate(ivs) if j not in (i, left, right)]
                ivs.append((l[0], r[1], l[2], r[3]))
            elif left is not None:
                l = ivs[left]
                ivs = [w for j, w in enumerate(ivs) if j not in (i, left)]
                ivs.append((l[0], l[1], l[2], True))
            elif right is not None:
                r = ivs[right]
                ivs = [w for j, w in enumerate(ivs) if j not in (i, right)]
                ivs.append((r[0], r[1], True, r[3]))
            else:
                continue
            changed = True
            break

    def key(t):
        lo = t[0]
        if lo is None:
            return Fr(-10 ** 12)
        if isinstance(lo, Fr):
            return lo
        return (lo[2] + lo[3]) / 2

    return sorted(ivs, key=key)


def format_intervals(ivs):
    """解集打印：(-inf, -1) U [1, inf)；单点 [a]；空集 empty；全实 (-inf, inf)。"""

    def fmt_pt(v, side):
        if v is None:
            return "-inf" if side == "lo" else "inf"
        if isinstance(v, Fr):
            return str(v.numerator) if v.denominator == 1 else f"{v.numerator}/{v.denominator}"
        _tag, _s, lo, hi = v
        return f"RootOf(({lo}, {hi}))"

    if not ivs:
        return "empty"
    parts = []
    for lo, hi, li, hi_i in ivs:
        lb = "[" if li else "("
        rb = "]" if hi_i else ")"
        parts.append(f"{lb}{fmt_pt(lo, 'lo')}, {fmt_pt(hi, 'hi')}{rb}")
    return " U ".join(parts)
