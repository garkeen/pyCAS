"""K[x₁..xₙ] 多项式域：稀疏系数字典 + 泛系数环协议。

标准形：展开收集的系数-单项式规范序（指数元组升序，零系数剔除，
构造即冻结）。同域判等 = 标准形结构比较，完全判定。

表示复杂度：加法 O(|p|+|q|)，乘法 O(|p|·|q|)（字典合并），
无递归、无树分配——热路径全部是 dict/tuple 操作。

泛型性：系数经 Ring 协议 opaque 处理；ℚ 之外的高斯域、ℚ(α) 商环
实现同一协议即可挂载，多项式层零改动。
"""

from dataclasses import dataclass
from fractions import Fraction as Fr

from cas import term as T
from cas.term import Expr, Int, Sym
from cas.domains.base import Domain, Ring, RingError, register


# ---------------------------------------------------------------------------
# Poly：不可变稀疏多项式
# ---------------------------------------------------------------------------

@dataclass(frozen=True, slots=True)
class Poly:
    """vars: 变量序（固定）；monos: ((exp...), coef) 按指数升序的规范元组。"""
    vars: tuple
    monos: tuple

    def is_zero(self) -> bool:
        return not self.monos

    def deg_in(self, i: int) -> int:
        return max((k[i] for k, _ in self.monos), default=-1)


def _norm(ring: Ring, vars_, monos_dict: dict) -> Poly:
    """dict -> 冻结规范形：剔零 + 指数升序。唯一构造出口。"""
    ks = sorted(k for k, c in monos_dict.items() if not ring.is_zero(c))
    return Poly(vars_, tuple((k, monos_dict[k]) for k in ks))


def p_zero(vars_):
    return Poly(vars_, ())


def p_const(ring: Ring, vars_, c):
    z = (0,) * len(vars_)
    return _norm(ring, vars_, {z: c})


def p_add(ring: Ring, p: Poly, q: Poly) -> Poly:
    d = dict(p.monos)
    for k, c in q.monos:
        d[k] = ring.add(d.get(k, ring.from_int(0)), c)
        if ring.is_zero(d[k]):
            del d[k]
    return _norm(ring, p.vars, d)


def p_neg(ring: Ring, p: Poly) -> Poly:
    return Poly(p.vars, tuple((k, ring.neg(c)) for k, c in p.monos))


def p_sub(ring: Ring, p: Poly, q: Poly) -> Poly:
    return p_add(ring, p, p_neg(ring, q))


def p_mul(ring: Ring, p: Poly, q: Poly) -> Poly:
    if p.is_zero() or q.is_zero():
        return p_zero(p.vars)
    d = {}
    for ka, ca in p.monos:
        for kb, cb in q.monos:
            k = tuple(x + y for x, y in zip(ka, kb))
            d[k] = ring.add(d.get(k, ring.from_int(0)), ring.mul(ca, cb))
    return _norm(ring, p.vars, d)


def p_pow(ring: Ring, p: Poly, n: int) -> Poly:
    """快速幂，n ≥ 0。"""
    if n < 0:
        raise ValueError("negative exponent")
    r = p_const(ring, p.vars, ring.from_int(1))
    b = p
    while n:
        if n & 1:
            r = p_mul(ring, r, b)
        b = p_mul(ring, b, b)
        n >>= 1
    return r


def p_scale(ring: Ring, p: Poly, c) -> Poly:
    if ring.is_zero(c):
        return p_zero(p.vars)
    return Poly(p.vars, tuple((k, ring.mul(c, m)) for k, m in p.monos))


def p_divmod_field(ring: Ring, p: Poly, q: Poly, var_i: int):
    """域系数环上的全除法（按变量 var_i 的字典序主幂）。

    要求 ring 提供精确除法 div_exact（ℚ 天然满足）。返回 (quot, rem)。
    """
    if q.is_zero():
        raise ZeroDivisionError("poly division by zero")
    ex_div = lambda a, b: ring.div_exact(a, b)
    rem = dict(p.monos)
    quot = {}
    dq_top = max((k[var_i] for k, _ in q.monos), default=-1)
    q_lead = max(q.monos, key=lambda kc: kc[0][var_i])
    while True:
        live = [(k, c) for k, c in rem.items() if not ring.is_zero(c)]
        if not live:
            break
        k, c = max(live, key=lambda kc: kc[0][var_i])
        e = k[var_i] - dq_top
        if e < 0:
            break
        # 商单项式指数：k - q_lead 指数（逐分量）
        mono = tuple(a - b for a, b in zip(k, q_lead[0]))
        lc = ex_div(c, q_lead[1])
        quot = {mono: lc} if not quot else {**quot, mono: quot.get(mono, ring.from_int(0)) + lc}
        # 减去 lc * mono * q
        sub = {}
        for kq, cq in q.monos:
            kk = tuple(a + b for a, b in zip(mono, kq))
            sub[kk] = ring.mul(lc, cq)
        for kk, cc in sub.items():
            nv = ring.sub(rem.get(kk, ring.from_int(0)), cc)
            if ring.is_zero(nv):
                rem.pop(kk, None)
            else:
                rem[kk] = nv
    return (_norm(ring, p.vars, quot), _norm(ring, p.vars, rem))


def p_gcd_univar(ring: Ring, p: Poly, q: Poly) -> Poly:
    """单变量（len(vars)==1）域上欧几里得 GCD，monic 规范。

    这是通用算法（欧几里得），非特判；多变量 GCD 待通用算法就位后
    作为其快路径接入，当前不提供。"""
    if len(p.vars) != 1:
        raise ValueError("univariate only")
    a, b = p, q
    while not b.is_zero():
        _, r = p_divmod_field(ring, a, b, 0)
        a, b = b, r
    if a.is_zero():
        return p_zero(p.vars)
    lead = max(a.monos, key=lambda kc: kc[0][0])
    monic = p_scale(ring, a, ring.div_exact(ring.from_int(1), lead[1]))
    return monic


def p_deriv(ring: Ring, p: Poly, var_i: int) -> Poly:
    """对第 var_i 个变元求形式导数（域内导子，留在 K[x] 内）。

    D(Σ c·x^k) = Σ (D(c)·x^k + c·k_i·x^(k-e_i))：系数导子经
    ring.deriv 委托——常数域为零，含参/代数扩张覆写即生效。"""
    d = {}
    for k, c in p.monos:
        dc = ring.deriv(c)
        if not ring.is_zero(dc):
            d[k] = ring.add(d.get(k, ring.from_int(0)), dc)
        ki = k[var_i]
        if ki:
            kk = tuple(kj - (1 if j == var_i else 0) for j, kj in enumerate(k))
            d[kk] = ring.add(d.get(kk, ring.from_int(0)),
                             ring.mul(ring.from_int(ki), c))
    return _norm(ring, p.vars, d)


# ---------------------------------------------------------------------------
# 项 <-> 多项式
# ---------------------------------------------------------------------------

def from_term(ring: Ring, t, vars_: tuple) -> Poly | None:
    """驻留项 -> Poly；越出 K[x] 片段（未知符号、非整指数、其他头）
    返回 None。成员测试与转换一体完成。"""
    idx = {v: i for i, v in enumerate(vars_)}
    zero = (0,) * len(vars_)

    def rec(u) -> dict | None:
        if isinstance(u, Int):
            return {zero: ring.from_int(u.v)} if u.v else {}
        if T.is_num(u):
            try:
                return {zero: ring.from_frac(T.num_val(u))}
            except RingError:
                return None
        if isinstance(u, Sym):
            if u in idx:
                k = tuple(1 if j == idx[u] else 0 for j in range(len(vars_)))
                return {k: ring.from_int(1)}
            return None
        if isinstance(u, Expr):
            n = u.head.name
            if n == "Plus":
                acc = {}
                for a in u.args:
                    pa = rec(a)
                    if pa is None:
                        return None
                    for k, c in pa.items():
                        acc[k] = ring.add(acc.get(k, ring.from_int(0)), c)
                return {k: c for k, c in acc.items() if not ring.is_zero(c)}
            if n == "Times":
                acc = {zero: ring.from_int(1)}
                for a in u.args:
                    pa = rec(a)
                    if pa is None:
                        return None
                    nxt = {}
                    for k1, c1 in acc.items():
                        for k2, c2 in pa.items():
                            k = tuple(x + y for x, y in zip(k1, k2))
                            nxt[k] = ring.add(nxt.get(k, ring.from_int(0)),
                                              ring.mul(c1, c2))
                    acc = {k: c for k, c in nxt.items() if not ring.is_zero(c)}
                return acc
            if n == "Power":
                b, e = u.args
                pb = rec(b)
                if pb is None or not isinstance(e, Int) or e.v < 0:
                    return None
                cur = {zero: ring.from_int(1)}
                base = pb
                nn = e.v
                while nn:
                    if nn & 1:
                        nxt = {}
                        for k1, c1 in cur.items():
                            for k2, c2 in base.items():
                                k = tuple(x + y for x, y in zip(k1, k2))
                                nxt[k] = ring.add(nxt.get(k, ring.from_int(0)),
                                                  ring.mul(c1, c2))
                        cur = {k: c for k, c in nxt.items()
                               if not ring.is_zero(c)}
                    nn >>= 1
                    if nn:
                        nxt = {}
                        for k1, c1 in base.items():
                            for k2, c2 in base.items():
                                k = tuple(x + y for x, y in zip(k1, k2))
                                nxt[k] = ring.add(nxt.get(k, ring.from_int(0)),
                                                  ring.mul(c1, c2))
                        base = {k: c for k, c in nxt.items()
                                if not ring.is_zero(c)}
                return cur
        return None

    d = rec(t)
    if d is None:
        return None
    return _norm(ring, vars_, d)


def to_term(ring: Ring, p: Poly):
    """Poly -> 标准形驻留项：Σ coef·Π x^e，mk 排序驻留。"""
    terms = []
    for k, c in p.monos:
        var_factors = [v for v, e in zip(p.vars, k) if e == 1]
        var_powers = [T.pw(v, T.N(e)) for v, e in zip(p.vars, k) if e > 1]
        vf = var_factors + var_powers
        is_one = ring.equal(c, ring.from_int(1))
        if is_one and vf:
            ft = vf[0] if len(vf) == 1 else T.mk(T.S("Times"), tuple(vf))
        else:
            coef_t = T.N(c) if isinstance(c, Fr) else _coef_term(ring, c)
            facs = [coef_t] + vf
            ft = facs[0] if len(facs) == 1 else T.mk(T.S("Times"), tuple(facs))
        terms.append(ft)
    if not terms:
        return T.N(0)
    return terms[0] if len(terms) == 1 else T.mk(T.S("Plus"), tuple(terms))


def _coef_term(ring: Ring, c):
    """非 ℚ 系数的项化钩子：环自带渲染时使用；ℚ 环不会走到这里。"""
    render = getattr(ring, "to_term", None)
    if render is None:
        raise TypeError(f"ring {ring!r} cannot render coefficient {c!r}")
    return render(c)


# ---------------------------------------------------------------------------
# 域对象
# ---------------------------------------------------------------------------

class PolyDomain(Domain):
    """K[x₁..xₙ]，K 为含 ℚ 的域系数环。"""

    def __init__(self, vars_, ring: Ring, name: str | None = None):
        self.vars = tuple(vars_)
        self.ring = ring
        self.name = name or "K[" + ",".join(v.name for v in self.vars) + "]"
        # 能力（架构 3.2）：K[x] 单变量且系数为域时才是欧几里得整环
        self.is_euclidean = bool(ring.is_field and len(self.vars) == 1)

    def member(self, t) -> bool:
        return from_term(self.ring, t, self.vars) is not None

    def normalize(self, t):
        p = from_term(self.ring, t, self.vars)
        if p is None:
            return None
        return to_term(self.ring, p)

    def equal(self, a, b):
        pa = from_term(self.ring, a, self.vars)
        pb = from_term(self.ring, b, self.vars)
        if pa is None or pb is None:
            return None                  # 非成员：调用方越界
        return pa.monos == pb.monos


_ring_cache = {}


def poly_domain(*vars_) -> PolyDomain:
    """按变量集缓存域对象（域是值对象，同变集共享实例）。"""
    key = tuple(vars_)
    d = _ring_cache.get(key)
    if d is None:
        d = register(PolyDomain(key, _default_ring()))
        _ring_cache[key] = d
    return d


_DEFAULT_RING = None


def _default_ring():
    global _DEFAULT_RING
    if _DEFAULT_RING is None:
        from cas.domains.q import Q_RING
        _DEFAULT_RING = Q_RING
    return _DEFAULT_RING
