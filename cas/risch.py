"""微分域塔（Risch M5.0）：DifferentialExtension 对应物 + 塔上求导。

参照：Bronstein《Symbolic Integration I》第 4-6 章；sympy risch.py 的
DifferentialExtension（level/case 结构）；maxima risch.lisp（属性表存
各扩展导数 + spderivative 链式求导——本模块的 derivation 同思路，
但在扁平多元 Poly 上做全变量链式法则）。

M5.0 范围：塔构建（exp/primitive 单项式，参数限 Q(x)）+ derivation
+ term<->塔双向转换。积分算法本体（Hermite 推广/residue_reduce/RDE）
在 M5.1+；三角经复指数在 M5.3（maxima trigin1 路线）。

诚实边界：代数依赖（exp(log(x)/2)）、嵌套超越参数（exp(x*e^x)）、
三角函数输入一律 RischUnsupported 拒绝——绝不静默错。
"""

from fractions import Fraction as Fr
from math import gcd

from cas import term as T
from cas.term import S, N, Expr, Sym
from cas.poly import Poly
from cas.errors import PolyError


class RischUnsupported(Exception):
    """塔构建失败（携带原因，诚实拒答的载体）。"""

    def __init__(self, reason):
        super().__init__(reason)
        self.reason = reason


class DiffExt:
    """微分域塔 K_0 < K_1 < ... < K_n，K_0 = Q(x)。

    levels[i]：塔变量（levels[0] = 积分变量 x）；
    cases[i]：'base' | 'exp' | 'primitive'；
    ws[i]：(wn, wd) Poly((x,)) 对——exp: D(t_i) = (wn/wd)*t_i；
    primitive: D(t_i) = wn/wd（= u'/u）；
    terms[i]：塔变量的原函数形态（backsubs 用，如 Exp(x/2)、Log(x)）。
    """

    __slots__ = ("levels", "cases", "ws", "terms")

    def __init__(self, x):
        self.levels = [x]
        self.cases = ["base"]
        self.ws = [None]
        self.terms = [x]

    @property
    def vars(self):
        return tuple(self.levels)

    def add(self, case, w, term, name_hint):
        t = _fresh_sym(self.levels, name_hint)
        self.levels.append(t)
        self.cases.append(case)
        self.ws.append(w)
        self.terms.append(term)
        return t

    def dpair(self, j, all_vars):
        """D(levels[j]) 作为 all_vars 上的 (num, den) 分式。"""
        if self.cases[j] == "base":
            return Poly.const(all_vars, Fr(1)), Poly.one(all_vars)
        wn, wd = self.ws[j]
        wn = _embed(wn, all_vars)
        wd = _embed(wd, all_vars)
        if self.cases[j] == "exp":
            tj = _embed(Poly.mono(all_vars, self.levels[j], 1), all_vars)
            return _rmul_polys(wn, wd, tj, Poly.one(all_vars))
        return wn, wd


# ---------------------------------------------------------------------------
# 分式助手（塔元素的 (num, den) 代数；den monic 化由 cancel 保证）
# ---------------------------------------------------------------------------

def _embed(p, all_vars):
    """Poly(子集变量) -> Poly(all_vars)（缺失维度指数置零）。"""
    if p.vars == tuple(all_vars):
        return p
    idx = [all_vars.index(v) for v in p.vars]
    out = {}
    for k, c in p.monos.items():
        nk = [0] * len(all_vars)
        for i, j in enumerate(idx):
            nk[j] = k[i]
        out[tuple(nk)] = c
    return Poly(all_vars, out)


def _rmul_polys(an, ad, bn, bd):
    """(an/ad)*(bn/bd)，约化。"""
    n = an * bn
    d = ad * bd
    return _cancel(n, d)


def _cancel(n, d):
    """轻量规范：常数 content 约化 + 分母 monic。

    多项式 gcd 约化不在 M5.0 范围（Hermite 推广在 M5.1 正规处理）；
    此处只防分式代数的系数膨胀。
    """
    if n.is_zero():
        return Poly.zero(n.vars), Poly.one(n.vars)
    cn, cd = n.content(), d.content()
    c = _fr_gcd(cn, cd)
    if c != 0 and c != 1:
        n = n.scalar(Fr(1) / c)
        d = d.scalar(Fr(1) / c)
    lc = d.lc(d.vars[0])
    if lc != 1:
        n = n.scalar(Fr(1) / lc)
        d = d.scalar(Fr(1) / lc)
    return n, d


def _fr_gcd(a, b):
    from math import gcd as _g

    if a == 0:
        return abs(b)
    if b == 0:
        return abs(a)
    n = _g(abs(a.numerator), abs(b.numerator))
    d = a.denominator * b.denominator // _g(a.denominator, b.denominator)
    return Fr(n, d)


def _radd(a, b):
    """(an,ad)+(bn,bd)。"""
    an, ad = a
    bn, bd = b
    if an.is_zero():
        return b
    if bn.is_zero():
        return a
    return _cancel(an * bd + bn * ad, ad * bd)


# ---------------------------------------------------------------------------
# 收集与归组
# ---------------------------------------------------------------------------

def _collect_exts(t):
    """显式栈遍历：收集 (Exp 参数项集合, Log 参数项集合)。"""
    exps, logs = [], []
    seen = set()
    stack = [t]
    while stack:
        u = stack.pop()
        if id(u) in seen:
            continue
        seen.add(id(u))
        if isinstance(u, Expr):
            n = u.head.name
            if n == "Exp" and len(u.args) == 1:
                exps.append(u.args[0])
            elif n == "Log" and len(u.args) == 1:
                logs.append(u.args[0])
            stack.extend(u.args)
    return exps, logs


def _group_integer_powers(args):
    """Fr 倍数关系归组（sympy integer_powers 同款）。

    返回 [(base_arg, [(arg, mult)])]，mult 为整数且组内互素
    （content = 1，基取最大合法形态）。
    """
    groups = []
    for a in args:
        placed = False
        for base, members in groups:
            q = _ratio(a, base)
            if q is not None:
                members.append((a, q))
                placed = True
                break
        if not placed:
            groups.append((a, [(a, Fr(1))]))
    out = []
    for base, members in groups:
        k = 1
        for _, q in members:
            k = k * q.denominator // gcd(k, q.denominator)
        mults = [int(q * k) for _, q in members]
        g = 0
        for m in mults:
            g = gcd(g, abs(m))
        g = g or 1
        # 新基 = base * g/k（倍数 m/g 全整数且互素）
        new_base = _scale_arg(base, Fr(g, k))
        out.append((new_base, list(zip([a for a, _ in members], [m // g for m in mults]))))
    return out


def _ratio(a, b):
    """a/b 是 Fr 则返回，否则 None（Q(x) 上：pb 整除 pa 且商为常数）。"""
    pa = _try_qx(a)
    pb = _try_qx(b)
    if pa is None or pb is None or pb.is_zero():
        return None
    qa, ra = pa.udivmod(pb)
    if not ra.is_zero() or not qa.is_const():
        return None
    return qa.const_val()


def _scale_arg(arg, c):
    """arg 的 Fr 倍（保驻留形态）。"""
    return T.mk(S("Times"), (arg, N(c))) if c != 1 else arg


def _try_qx(t):
    """term -> Poly((x,)) 或 None（非 Q(x) 有理函数形态）。"""
    try:
        return Poly.from_term(t, (T.S("x"),))
    except PolyError:
        return None


def _fresh_sym(levels, hint):
    used = {v.name for v in levels}
    if hint not in used:
        return S(hint)
    i = 1
    while f"{hint}{i}" in used:
        i += 1
    return S(f"{hint}{i}")


# ---------------------------------------------------------------------------
# 塔构建
# ---------------------------------------------------------------------------

def build_extension(f, x):
    """term -> (DiffExt, fa, fd)：f 在塔上的 (num, den) 表示。

    建塔顺序 log 先 exp 后（sympy handle_first='log' 同款：primitive
    在下、超指数在外）。参数非 Q(x) -> RischUnsupported。
    """
    de = DiffExt(x)
    exps, logs = _collect_exts(f)

    # log 层（primitive）：u 必须 in Q(x) 且非常数
    log_map = {}
    for u in logs:
        up = _try_qx(u)
        if up is None:
            raise RischUnsupported(
                "log argument not rational in " + x.name + ": nested/algebraic extension"
            )
        if up.is_const() or up.degree(x) == 0:
            continue   # log(常数) 属常数域，不建层
        key = u
        if key in log_map:
            continue
        du = up.deriv(x)
        w = _cancel(du, up)
        t = de.add("primitive", w, T.mk(S("Log"), (u,)), "l")
        log_map[key] = t

    # exp 层（hyperexponential）：arg in Q(x)，Fr 倍数归组
    exp_map = {}
    for base, members in _group_integer_powers(exps):
        bp = _try_qx(base)
        if bp is None:
            raise RischUnsupported(
                "exponent not rational in " + x.name + ": nested/algebraic extension"
            )
        if bp.degree(x) == 0:
            continue   # exp(常数) = 常数因子
        w = (bp.deriv(x), Poly.one((x,)))
        t = de.add("exp", w, T.mk(S("Exp"), (base,)), "t")
        for arg, m in members:
            exp_map[arg] = (t, m)

    # 重写 f 到塔上：Exp(m*base) -> t^m，Log(u) -> tl
    subs = {}
    for arg, (t, m) in exp_map.items():
        target = T.pw(T.S(t.name), N(m)) if m != 1 else T.S(t.name)
        subs[T.mk(S("Exp"), (arg,))] = target
    for u, t in log_map.items():
        subs[T.mk(S("Log"), (u,))] = T.S(t.name)
    g = T.subst(f, subs) if subs else f

    # 残留检查：漏网的 Exp/Log = 塔覆盖不全（诚实拒绝）
    rexp, rlog = _collect_exts(g)
    if rexp or rlog:
        raise RischUnsupported("expression not covered by the differential extension")

    try:
        fa, fd = _frac_from_term(g, de.vars)
    except PolyError as ex:
        raise RischUnsupported("not rational over the extension: " + str(ex))
    return de, fa, fd


def _frac_from_term(t, vars_):
    """term -> 约化 (num, den) Poly 对（负整数幂入分母）。"""
    num = _frac_num(t, vars_)
    return _cancel(num[0], num[1])


def _frac_num(t, vars_):
    if T.is_num(t):
        return Poly.const(vars_, T.num_val(t)), Poly.one(vars_)
    if isinstance(t, Sym):
        for v in vars_:
            if t is v:
                return Poly.mono(vars_, t, 1), Poly.one(vars_)
        raise PolyError("free symbol outside extension: " + t.name)
    if isinstance(t, Expr):
        n = t.head.name
        if n == "Plus":
            an, ad = Poly.zero(vars_), Poly.one(vars_)
            for a in t.args:
                bn, bd = _frac_num(a, vars_)
                an, ad = _radd((an, ad), (bn, bd))
            return an, ad
        if n == "Times":
            an, ad = Poly.one(vars_), Poly.one(vars_)
            for a in t.args:
                bn, bd = _frac_num(a, vars_)
                an, ad = _rmul_polys(an, ad, bn, bd)
            return an, ad
        if n == "Power":
            b, e = t.args
            bn, bd = _frac_num(b, vars_)
            if isinstance(e, T.Int) and e.v >= 0:
                return bn ** e.v, bd ** e.v
            if isinstance(e, T.Int):
                return bd ** (-e.v), bn ** (-e.v)
            raise PolyError("non-integer power in extension")
    raise PolyError("not rational over extension: " + repr(t))


# ---------------------------------------------------------------------------
# 塔上求导（maxima spderivative 对应物：扁平 Poly 全变量链式法则）
# ---------------------------------------------------------------------------

def derivation(p, de):
    """Poly(de.vars) -> (num, den)：塔上导数 D（约化分式）。

    D(sum c_k * prod v^e) = sum_j [d(mono)/dv_j] * D(v_j)；
    系数 c_k in Q 导数为零；D(v_j) 由 cases/ws 给出。
    """
    vars_ = p.vars
    acc_n, acc_d = Poly.zero(vars_), Poly.one(vars_)
    for exps, c in p.monos.items():
        for j, v in enumerate(vars_):
            e = exps[j]
            if e == 0:
                continue
            nk = tuple(x - (1 if i == j else 0) for i, x in enumerate(exps))
            pre = Poly(vars_, {nk: c * e})
            dn, dd = de.dpair(j, vars_)
            acc_n, acc_d = _radd(
                (acc_n, acc_d), _rmul_polys(pre, Poly.one(vars_), dn, dd)
            )
    return _cancel(acc_n, acc_d)


# ---------------------------------------------------------------------------
# 回写（塔 -> term）
# ---------------------------------------------------------------------------

def tower_to_term_pair(a, d, de):
    """(num, den) Poly -> term（逐层 backsubst）。"""
    nt = a.to_term() if not a.is_zero() else T.ZERO
    dt = d.to_term()
    val = T.div(nt, dt) if not dt is T.ONE else nt
    subs = {}
    for i in range(1, len(de.levels)):
        subs[T.S(de.levels[i].name)] = de.terms[i]
    if not subs:
        return val
    return T.subst(val, subs)


# ---------------------------------------------------------------------------
# M5.1a/M5.2：塔上 K[t] 视图积分（t = exp(eta) 或 primitive θ）
#
# 表示：K[t] 多项式 = 系数 list [c_0..c_n]（c_i: RatFunc——K = Q(x) 显式
#       有理函数域，M5.2 起；升序）；K(t) 分式 = (A, d)（A, d: K[t]）。
# 塔上导数 D: K[t] -> K[t]（K 是域，Dθ = v ∈ K 或 Dt = η'·t）：
#   exp:       D(Σa_k t^k)  = Σ (Da_k + k·η'·a_k) t^k          （对角）
#   primitive: D(Σa_k θ^k)  = Σ_i (Da_i + (i+1)·v·a_{i+1}) θ^i  （移位）
# special 因子：exp 的 t（gcd(t,Dt)=t≠1）；primitive 无（gcd(θ,v)=1，
#   θ 正规）——primitive 全部因子走 normal 路线。
# ---------------------------------------------------------------------------

def _univar(p, ti):
    """Poly(all_vars) -> K[t_i] 系数 list（升序，K 元素 = RatFunc）。"""
    from cas.ratfunc import RatFunc

    sub = tuple(v for v in p.vars if v is not ti)
    j = p.vars.index(ti)
    out = [RatFunc.zero(sub)]
    for k, c in p.monos.items():
        e = k[j]
        while len(out) <= e:
            out.append(RatFunc.zero(sub))
        nk = tuple(x for i, x in enumerate(k) if i != j)
        out[e] = out[e] + RatFunc.from_poly(Poly(sub, {nk: c}))
    return out


def _from_univar(coeffs, all_vars, ti):
    """系数 list（RatFunc）-> 塔上 (num, den) Poly 对。"""
    j = all_vars.index(ti)

    def shift(p, e):
        # embed 后 p 已含 t 维度（指数 0）——替换位置 j 的指数，非插入
        return Poly(all_vars, {k[:j] + (e,) + k[j + 1:]: c
                               for k, c in p.monos.items()})

    num = Poly.zero(all_vars)
    den = Poly.one(all_vars)
    for e, c in enumerate(coeffs):
        if c.is_zero():
            continue
        pe = shift(_embed(c.p, all_vars), e)
        qe = _embed(c.q, all_vars)      # 分母不带 θ^e 权重
        num = num * qe + den * pe
        den = den * qe
    return _cancel(num, den)


def _u_add(a, b, zero):
    n = max(len(a), len(b))
    out = []
    for i in range(n):
        ca = a[i] if i < len(a) else zero
        cb = b[i] if i < len(b) else zero
        out.append(ca + cb)
    return _u_trim(out)


def _u_trim(cs):
    while cs and cs[-1].is_zero():
        cs.pop()
    return cs


def _u_neg(a, neg):
    return [neg(c) for c in a]


def _u_mul(a, b, zero):
    if not a or not b:
        return []
    out = [zero for _ in range(len(a) + len(b) - 1)]
    for i, ca in enumerate(a):
        if ca.is_zero():
            continue
        for j, cb in enumerate(b):
            if cb.is_zero():
                continue
            out[i + j] = out[i + j] + ca * cb
    return _u_trim(out)


def _u_divmod(a, b, zero):
    """K[t] 除法（b 非零，K = RatFunc 域）。返回 (q, r) 系数 list。"""
    r = [c for c in a]
    db = len(b) - 1
    lb = b[db]
    if len(r) - 1 < db:
        return [], _u_trim(r)
    q = [zero for _ in range(len(r) - db)]
    while len(r) - 1 >= db and not _u_is_zero(r):
        shift = len(r) - 1 - db
        lc = r[-1]
        c = lc / lb
        q[shift] = c
        for i in range(db + 1):
            r[shift + i] = r[shift + i] - c * b[i]
        _u_trim(r)
    return _u_trim(q), _u_trim(r)


def _u_is_zero(cs):
    return not cs or all(c.is_zero() for c in cs)


def _u_gcd(a, b, zero):
    """K[t] gcd（欧几里得 + monic）。K 是域——首系数总可逆。"""
    A, B = _u_trim([c for c in a]), _u_trim([c for c in b])
    while not _u_is_zero(B):
        _, r = _u_divmod(A, B, zero)
        A, B = B, r
    if _u_is_zero(A):
        return []
    s = zero.one(zero.p.vars) / A[-1]
    return [c * s for c in A]


def _u_inv_mod(a, m, zero):
    """a 的逆 mod m（gcd(a,m)=1）。扩展欧几里得：s*a + t*m = g -> s/g。

    初始化 s0=0（对应 r0=m）、s1=1（对应 r1=a）；结束时 s0*a ≡ g (mod m)。
    """
    r0, r1 = [c for c in m], _u_trim([c for c in a])
    s0, s1 = [zero], [zero.one(zero.p.vars)]
    while not _u_is_zero(r1):
        q, r = _u_divmod(r0, r1, zero)
        qs = _u_mul(q, s1, zero)
        s_new = _u_add(s0, _u_neg(qs, lambda c: c * Fr(-1)), zero)
        s0, s1 = s1, s_new
        r0, r1 = r1, r
    # r0 = gcd；互素时为 K 中单位（非零元素），s0*a ≡ gcd (mod m)
    if _u_is_zero(r0):
        raise RischUnsupported("zero gcd in inverse")
    s = r0[0].one(r0[0].p.vars) / r0[0]
    out = [c * s for c in s0]
    _, rem = _u_divmod(out, m, zero)
    return rem


def _u_deriv_x(coeffs):
    """K 层求导：逐系数 d/dx。"""
    xv = coeffs[0].p.vars[0] if coeffs and coeffs[0].p.vars else T.S("x")
    return [c.deriv(xv) for c in coeffs]


def _derive_ut(coeffs, de, j):
    """塔上 D 作用于 Σ a_k t_j^k -> K[t] 系数 list（无分母——K 是域）。

    exp:       D(Σa_k t^k) = Σ (Da_k + k·η'·a_k) t^k          （对角）
    primitive: D(Σa_k θ^k) = Σ_i (Da_i + (i+1)·v·a_{i+1}) θ^i  （移位）
    """
    from cas.ratfunc import RatFunc

    wn, wd = de.ws[j]
    w = RatFunc(wn, wd)
    xv = coeffs[0].p.vars[0] if coeffs else de.levels[0]
    n = len(coeffs)
    out = []
    for i in range(n):
        a = coeffs[i]
        term = a.deriv(xv) if not a.is_zero() else RatFunc.zero((xv,))
        if de.cases[j] == "exp":
            if i > 0 and not a.is_zero():
                term = term + a * w * Fr(i)
        else:  # primitive：右邻贡献 (i+1)·v·a_{i+1}
            if i + 1 < n and not coeffs[i + 1].is_zero():
                term = term + coeffs[i + 1] * w * Fr(i + 1)
        out.append(term)
    return _u_trim(out)


def _exp_w(de, j):
    """第 j 层的 w = D(t)/t 或 D(θ)（RatFunc）。"""
    from cas.ratfunc import RatFunc

    wn, wd = de.ws[j]
    return RatFunc(wn, wd)


# ---------------------------------------------------------------------------
# M5.1b：Risch 微分方程 exp case——y' + k*eta'*y = g（y ∈ Q(x)）
#
# 极点分析：p^m ∥ denom(y) => y' 有 p^{m+1} 极点而 k*eta'*y 只有 p^m
# （eta' 多项式）=> p^{m+1} | denom(g)。故 denom(y) 的界
# D = Π p^{e-1}（p^e ∥ denom(g)，e>=2）；z = y*D 多项式化后待定系数。
# f = k*eta' != 0 保证齐次多项式解只有 0（deg y' < deg f*y）=> 解唯一。
# ---------------------------------------------------------------------------

def _poly_to_list(p):
    """Poly((x,)) -> 升序 Fr 系数 list。"""
    xv = p.vars[0]
    d = p.degree(xv)
    out = [Fr(0)] * (d + 1)
    for k, v in p.monos.items():
        out[k[0]] = v
    return out


def _list_to_poly(cs, vars_):
    """升序 Fr list -> Poly（一元）。"""
    return Poly(vars_, {(e,): c for e, c in enumerate(cs) if c != 0})


def _gauss_solve(M, b):
    """Fr 系数线性方程组高斯消元。返回解 list | None（无解）。

    自由变量取 0（f != 0 时 RDE 齐次只有零解，理论保证无自由变量；
    此处取 0 为防御性特解）。
    """
    n = len(M)
    cols = len(M[0]) if n else 0
    A = [row[:] + [b[i]] for i, row in enumerate(M)]
    piv_cols = []
    r = 0
    for cidx in range(cols):
        piv = None
        for i in range(r, n):
            if A[i][cidx] != 0:
                piv = i
                break
        if piv is None:
            continue
        A[r], A[piv] = A[piv], A[r]
        pv = A[r][cidx]
        A[r] = [v / pv for v in A[r]]
        for i in range(n):
            if i != r and A[i][cidx] != 0:
                fac = A[i][cidx]
                A[i] = [vi - fac * vr for vi, vr in zip(A[i], A[r])]
        piv_cols.append(cidx)
        r += 1
        if r == n:
            break
    for i in range(n):
        if all(v == 0 for v in A[i][:cols]) and A[i][-1] != 0:
            return None
    sol = [Fr(0)] * cols
    for i, cidx in enumerate(piv_cols):
        sol[cidx] = A[i][-1]
    return sol


def _rde_exp_solve(k, eta_p, an, ad, zero):
    """解 y' + k*eta'*y = an/ad（y ∈ Q(x)）。返回 y: Poly | None。

    None = 无有理解（该频率分量不可初等的证明载体）。
    """
    xv = zero.vars[0]
    f = eta_p.scalar(Fr(k))
    # 步骤1：分母界 D = Π p^{e-1}（p^e ∥ denom(g)，e>=2）
    Dp = Poly.one(zero.vars)
    from cas.factor import squarefree_decomp

    for pp, e in squarefree_decomp(ad):
        if e >= 2:
            Dp = Dp * pp ** (e - 1)
    # 步骤2：z = y*D；两边乘 ad：ad*D*z' + (f*D − D')*ad*z = an*D²
    A_ = ad * Dp
    B_ = (f * Dp - Dp.deriv(xv)) * ad
    C_ = an * Dp * Dp
    degB = B_.degree(xv)
    degC = C_.degree(xv)
    if degB < 0:
        # B ≡ 0：f*D = D' 且 ad 常数——eta' 多项式时仅 f=0，已排除
        raise RischUnsupported("degenerate RDE (f*D == D')")
    N = degC - degB
    if N < 0:
        # z 只能 = 0；rhs 非零即无解
        return None if not C_.is_zero() else Poly.zero(zero.vars)
    # 步骤3：待定系数线性方程组
    A_l = _poly_to_list(A_)
    B_l = _poly_to_list(B_)
    C_l = _poly_to_list(C_)
    ncols = N + 1
    top = max(len(C_l) - 1, (len(B_l) - 1) + N,
              (len(A_l) - 1) + (N - 1) if N > 0 else 0)
    nrows = max(top, len(C_l) - 1) + 1
    M = [[Fr(0)] * ncols for _ in range(nrows)]
    rhs_v = [Fr(0)] * nrows
    for i, cv in enumerate(C_l):
        rhs_v[i] = cv
    for ci in range(ncols):
        # 基 z = x^ci：LHS = A*(ci*x^(ci-1)) + B*x^ci
        if ci > 0:
            for ai, av in enumerate(A_l):
                m = ai + ci - 1
                M[m][ci] += av * Fr(ci)
        for bi, bv in enumerate(B_l):
            M[bi + ci][ci] += bv
    sol = _gauss_solve(M, rhs_v)
    if sol is None:
        return None
    return _list_to_poly(sol, zero.vars)


def risch_exp_integrate(fa, fd, de, j):
    """exp 单项式积分主入口（M5.1：真分式 + 频率分解）。

    返回 ((rat_part, logs, nonel, leftover), freqs, status)：
    freqs = {k: g_k}（g_k: RatFunc）——全部非零频率分量（正幂商 +
    负幂低幂 + residue t 幂剩余），k≠0 待 RDE；status: 'ok'。
    """
    from cas.ratfunc import RatFunc

    zero = RatFunc.zero((de.levels[0],))
    tj = de.levels[j]

    A = _univar(fa, tj)
    D = _univar(fd, tj)
    if _u_is_zero(A):
        return (None, None, None, None), {}, "ok"

    # 多项式部分：商 Q 的频率 + 真分式 R
    dq = len(D) - 1
    dp = len(A) - 1
    pos_freqs = {}
    if dp >= dq:
        Q, R = _u_divmod(A, D, zero)
        for k, c in enumerate(Q):
            if not c.is_zero():
                pos_freqs[k] = c
        A = R
        if _u_is_zero(A):
            return (None, None, None, None), pos_freqs, "ok"

    res, neg_freqs, st = _integrate_proper(A, D, de, j, zero)
    freqs = dict(pos_freqs)
    for k, v in neg_freqs.items():
        freqs[k] = freqs[k] + v if k in freqs else v
    return res, freqs, st


def _integrate_proper(A, D, de, j, zero):
    """真分式积分：special 分离（仅 exp）+ 无平方分解 + Hermite + residue。

    返回 ((rat_part, logs, nonel, leftover), neg_freqs, status)：
    neg_freqs = {k: g_k}——t 负幂频率分量（k<0，M5.1b RDE 处理）。
    primitive 层无 special 因子（gcd(θ,v)=1，θ 正规），全走 normal。
    """
    if de.cases[j] == "primitive":
        res, st = _integrate_normal(A, D, de, j, zero)
        return res, {}, st
    # special 分离：D = t^m * q0（q0[0] != 0）
    m = 0
    q0 = list(D)
    while len(q0) > 0 and q0[0].is_zero():
        q0 = q0[1:]
        m += 1
    q0 = _u_trim(q0)
    if m > 0:
        k_m = min(m, len(A))
        low, high = A[:k_m], A[k_m:]
        # 低段 Σ a_k t^{k-m}（负幂频率）；高段走正规路线
        neg_freqs = {}
        for k, c in enumerate(low):
            if not c.is_zero():
                neg_freqs[k - m] = c
        if _u_is_zero(high):
            return (None, None, None, None), neg_freqs, "ok"
        res, st = _integrate_normal(high, q0, de, j, zero)
        return (res[0], res[1], res[2], res[3]), neg_freqs, st
    res, st = _integrate_normal(A, D, de, j, zero)
    rat_part, logs, nonel, leftover = res
    if isinstance(leftover, tuple) and leftover and leftover[0] == "special":
        # residue 剩余的 t 幂部分 -> 正频
        pos_freqs = {k: c for k, c in enumerate(leftover[1]) if not c.is_zero()}
        return (rat_part, logs, nonel, None), pos_freqs, st
    return res, {}, st


def _integrate_normal(A, D, de, j, zero):
    """正规分母真分式：无平方分解 -> 部分分式 -> Hermite(e>1) + residue(e=1)。

    返回 (rat_part, logs, nonel, leftover, status)：
    rat_part = [(u_k, p, k)] 有理部分 u_k/p^k；logs = [(c, g)] 对数项；
    nonel = (num, p)|None 不可初等剩余（residue 无常数根——Bronstein 定理：
    真分式情形 residue 失败即证明不可初等）；leftover = K 分式递归 x 层。
    """
    tj = de.levels[j]
    factors = _squarefree_decomp_t(D, zero)
    rat_part = []
    logs = []
    nonel = None
    leftover = None
    for p, e in factors:
        cof = _u_divmod(D, _u_pow(p, e, zero), zero)[0]
        B = _u_divmod(_u_mul(A, _u_inv_mod_t(cof, D, zero), zero), _u_pow(p, e, zero), zero)[1]
        if e > 1:
            rat, (B1, _) = _hermite_pe(B, p, e, de, j, zero)
            rat_part.extend(rat)
        else:
            B1 = B
        lg, rem = _residue_sqfr(B1, p, de, j, zero)
        logs.extend(lg)
        if not _u_is_zero(rem):
            q, r = _u_divmod(rem, p, zero)
            if _u_is_zero(r):
                # 剩余恰为多项式：exp 下 t 幂部分 -> 频率 RDE；
                # primitive 下 θ-多项式剩余 -> 回多项式积分（leftover）
                if de.cases[j] == "exp" and any(not c.is_const() for c in q):
                    return (rat_part, logs, None, ("special", q)), "ok"
                leftover = q if leftover is None else _u_add(leftover, q, zero)
            else:
                nonel = (rem, p)
    return (rat_part, logs, nonel, leftover), "ok"


def _u_pow(cs, n, zero):
    out = [zero.one(zero.p.vars)]
    base = list(cs)
    while n > 0:
        if n & 1:
            out = _u_mul(out, base, zero)
        base = _u_mul(base, base, zero)
        n >>= 1
    return out


def _u_inv_mod_t(a, m, zero):
    """K[t] 上 a^{-1} mod m。"""
    return _u_inv_mod(a, m, zero)


def _squarefree_decomp_t(D, zero):
    """K[t] 无平方分解 [(p, e)]（形式导数 gcd 递归）。"""
    def rec(cur):
        if len(cur) <= 1 or _u_is_zero(cur):
            return []
        dc = _u_formal_deriv(cur)
        g = _u_gcd(cur, dc, zero)
        if len(g) <= 1:
            return [(cur, 1)]
        core, r = _u_divmod(cur, g, zero)
        if not _u_is_zero(r):
            raise RischUnsupported("squarefree division failed")
        rest = rec(g)
        single = core
        for pp, _mm in rest:
            single = _u_divmod(single, pp, zero)[0]
        out = [(pp, mm + 1) for pp, mm in rest]
        if len(single) > 1:
            out.append((single, 1))
        return out

    out = rec(list(D))
    # 规范序：按次数升序稳定组装
    return sorted(out, key=lambda pe: len(pe[0]))


def _u_formal_deriv(cs):
    """形式偏导 ∂/∂t（系数不动）。"""
    return _u_trim([c * Fr(k) for k, c in enumerate(cs)][1:])


def _hermite_pe(a, p, e, de, j, zero):
    """∫ a/p^e（p 无平方正规）-> (有理部分 [(u_k, p, k)], 剩余 (b, p))。

    逐层：u ≡ -(k-1)^{-1}*(a mod p)*inv(D(p)) (mod p)；
    v = (a + (k-1)*u*D(p))/p - D(u)，整除性由 u 构造保证。
    """
    rat = []
    cur_a, cur_e = list(a), e
    while cur_e >= 2:
        u, v = _hermite_factor(cur_a, p, cur_e, de, j, zero)
        if not _u_is_zero(u):
            rat.append((u, p, cur_e - 1))
        cur_a = v
        cur_e -= 1
    return rat, (cur_a, p)


def _hermite_factor(a, p, e, de, j, zero):
    """单层剥离：∫ a/p^e -> 贡献 u/p^{e-1}，剩余 v/p^{e-1}。

    u ≡ -(e-1)^{-1}·(a mod p)·inv(D(p) mod p) (mod p)（K 域上，无 wd 因子）。
    """
    Pm = _derive_ut(p, de, j)             # D(p)：K[t] 元素
    r = _u_divmod(a, p, zero)[1]
    pm1 = _u_inv_mod(Pm, p, zero)
    coef = Fr(-1) / (e - 1)
    u = [c * coef for c in _u_mul(r, pm1, zero)]
    _, u = _u_divmod(u, p, zero)
    # N = a + (e-1)*u*D(p) 整除 p
    N_ = _u_add(list(a), _u_mul([c * Fr(e - 1) for c in u], Pm, zero), zero)
    M, rem = _u_divmod(N_, p, zero)
    if not _u_is_zero(rem):
        raise RischUnsupported("hermite divisibility failed")
    Du = _derive_ut(u, de, j)
    v = _u_add(M, _u_neg(Du, lambda c: c * Fr(-1)), zero)
    return u, v


# ---------------------------------------------------------------------------
# residue_reduce（Rothstein-Trager；结式经 Bareiss 行列式，K[z] 系数）
# ---------------------------------------------------------------------------

def _neg_poly(c):
    return c * Fr(-1)


def _sylvester_res(fz, gz):
    """res_t(f, g)：fz/gz 是 K[z] 多项式（list[K 元素]，z 升序——与 K[t] 同构）。

    Sylvester 矩阵 + Bareiss 行列式（K[z] 整环上 exact division）。
    行列式与标准结式至多差符号——求根用途下无关紧要。
    """
    from cas.ratfunc import RatFunc

    m = len(fz) - 1     # deg f
    n = len(gz) - 1     # deg g
    size = m + n
    if size <= 0:
        return []
    M = []
    for i in range(n):
        row = [[] for _ in range(size)]
        for jj in range(i, min(i + m + 1, size)):
            row[jj] = fz[m - (jj - i)]
        M.append(row)
    for i in range(m):
        row = [[] for _ in range(size)]
        for jj in range(i, min(i + n + 1, size)):
            row[jj] = gz[n - (jj - i)]
        M.append(row)
    zero = RatFunc.zero((T.S("x"),))
    return _bareiss_det(M, size, zero)


# ---------------------------------------------------------------------------
# Bareiss 行列式（元素 = K[z] 多项式 = list[K 元素]，与 K[t] 同构——_u_* 通用）
# ---------------------------------------------------------------------------

def _u_sub(a, b):
    """K 多项式减法（zero 自参数推断）。"""
    from cas.ratfunc import RatFunc

    src = a if a else b
    z = RatFunc.zero(src[0].p.vars) if src else RatFunc.zero((T.S("x"),))
    return _u_add(a, _u_neg(b, lambda c: c * Fr(-1)), z)


def _u_mul0(a, b):
    """K 多项式乘法（zero 自参数推断）。"""
    from cas.ratfunc import RatFunc

    if not a or not b:
        return []
    z = RatFunc.zero(a[0].p.vars)
    return _u_mul(a, b, z)


def _bareiss_det(M, size, zero):
    """Bareiss 分式免除行列式（元素为 K[z] 多项式，_u_* 层直接适用）。"""
    A = [row[:] for row in M]
    prev = None         # 上一步主元；第一步除数为 1（不除）
    sign = 1
    for k in range(size - 1):
        if _u_is_zero(A[k][k]):
            for i in range(k + 1, size):
                if not _u_is_zero(A[i][k]):
                    A[k], A[i] = A[i], A[k]
                    sign = -sign
                    break
            else:
                return []
        pk = A[k][k]
        for i in range(k + 1, size):
            for jj in range(k + 1, size):
                num = _u_sub(_u_mul0(A[i][jj], pk), _u_mul0(A[i][k], A[k][jj]))
                if prev is not None:
                    q, r = _u_divmod(num, prev, zero)
                    if not _u_is_zero(r):
                        raise RischUnsupported("bareiss exact division failed")
                    A[i][jj] = q
                else:
                    A[i][jj] = num
        prev = pk
    det = _u_trim(A[size - 1][size - 1])
    det = _uz_trim_det(det)
    return det if sign == 1 else _u_neg(det, lambda c: c * Fr(-1))


def _uz_trim_det(p):
    return _u_trim(p)


def _residue_sqfr(B, p, de, j, zero):
    """∫ B/p（p 无平方正规）-> (logs [(c, g)], rem)。

    R(z) = res_t(B - z*D(p), p)；常数根 c（free of x）->
    贡献 c*log(g)，g = gcd(p, B - c*D(p))；剩余 rem（分母仍 p）
    = 不可初等成分。Bronstein 定理：真分式 + 无常数根 => 不可初等
    （M5.1b 补多项式部分后为完整证明）。solve 无法定根时显式异常——
    绝不静默把可积成分误判为不可积。
    """
    Dp = _derive_ut(p, de, j)
    nb = max(len(B), len(Dp))
    Bp = B + [zero for _ in range(nb - len(B))]
    Dpp = Dp + [zero for _ in range(nb - len(Dp))]
    # fz[i] = B_i - z*Dp_i（K[z] 多项式 = list[K 元素]）
    fz = [[b, _neg_poly(d)] for b, d in zip(Bp, Dpp)]
    gz = [[c] for c in p]
    Rz = _sylvester_res(fz, gz)
    logs = []
    rem = list(B)
    if len(Rz) >= 1 and not _u_is_zero(Rz):
        roots = _constant_roots(Rz)
        for c in roots:
            # fc = fz 代入 z=c：b + c*(-d)
            fc = []
            for zp in fz:
                val = zp[0]
                if len(zp) > 1:
                    val = val + zp[1] * c
                fc.append(val)
            fc = _u_trim(fc)
            g = _u_gcd(fc, p, zero)
            if len(g) <= 1:
                continue
            logs.append((T.N(c), g))
            Dg = _derive_ut(g, de, j)
            cof = _u_divmod(p, g, zero)[0]
            ct = zero.one(zero.p.vars) * c
            corr = _u_mul([ct], _u_mul(Dg, cof, zero), zero)
            rem = _u_add(rem, _u_neg(corr, lambda cc: cc * Fr(-1)), zero)
    return logs, _u_trim(rem)


def _uz_trim_list(cs):
    return _u_trim(cs)


def _constant_roots(Rz):
    """R(z) ∈ Q(x)[z] 的常数根：转 term 用 solve，含 x 的根丢弃。

    含 x 的根被丢弃正是数学语义：非常数 residue 不对应初等对数项。
    solve 无法判定（unsupported）时抛异常——绝不静默漏根（漏根会把
    可积成分误判为不可初等，违反永不静默错）。代数数值根（根式/RootOf）
    是合法 residue 常数，但系数组装需 Q(alpha) 域——M5.2 扩展，此处
    显式异常（不误判为不可积）。
    """
    from cas.solve import solve as _solve

    z = T.S("_rz")
    terms = []
    for e, c in enumerate(Rz):
        if c.is_zero():
            continue
        ct = c.to_term()
        terms.append(T.times(ct, T.pw(z, N(e))) if e else ct)
    if not terms:
        return []
    poly_t = T.mk(S("Plus"), tuple(terms)) if len(terms) > 1 else terms[0]
    r = _solve(poly_t, z)
    if r.status != "ok":
        raise RischUnsupported(
            "cannot determine constant roots of the resultant: " + (r.note or ""))
    out = []
    for sol in r.solutions:
        if not _free_of_x(sol):
            continue
        if not T.is_num(sol):
            raise RischUnsupported("algebraic residue roots pending M5.2")
        out.append(T.num_val(sol))
    return out


def _free_of_x(t):
    xv = T.S("x")
    return xv not in T.free_vars(t)


# ---------------------------------------------------------------------------
# 结果组装（塔 -> term）
# ---------------------------------------------------------------------------

def assemble_exp_result(rat_part, logs, nonel, de, j):
    """M5.1a 积分结果 -> term（组装 + backsubs）。"""
    tj = de.levels[j]
    subs = {de.levels[j]: de.terms[j]}
    rat_part = rat_part or []
    logs = logs or []
    parts = []
    for u, p, k in rat_part:
        un, ud = _from_univar(u, de.vars, tj)
        pn, pd = _from_univar(p, de.vars, tj)
        ut = T.subst(tower_to_term_pair(un, ud, de), subs)
        pt = T.subst(tower_to_term_pair(pn, pd, de), subs)
        parts.append(T.div(ut, T.pw(pt, N(k))))
    for c, g in logs:
        gn, gd = _from_univar(g, de.vars, tj)
        gt = T.subst(tower_to_term_pair(gn, gd, de), subs)
        parts.append(T.times(c, T.log(gt)))
    if nonel is not None:
        num, p = nonel
        nn, nd = _from_univar(num, de.vars, tj)
        pn, pd = _from_univar(p, de.vars, tj)
        from cas.pprint import to_str as _ts

        raise RischNonElementary(
            "integral of " + _ts(T.div(
                T.subst(tower_to_term_pair(nn, nd, de), subs),
                T.subst(tower_to_term_pair(pn, pd, de), subs))) +
            " over the tower is not elementary (no constant residue roots)"
        )
    if not parts:
        return T.ZERO
    if len(parts) == 1:
        return parts[0]
    return T.mk(S("Plus"), tuple(parts))


class RischNonElementary(Exception):
    """不可初等证明载体（Bronstein 决策程序的否定结论）。"""

    def __init__(self, reason):
        super().__init__(reason)
        self.reason = reason


def integrate_exp_tower(f, x):
    """顶层 API：term -> term（初等原函数）或 RischNonElementary/RischUnsupported。

    M5.1/M5.2 范围：单层塔（exp 或 primitive，K = Q(x)）。按最外层 case
    分派——exp 走频率 RDE（y' + k·η'·y = g），primitive 走逐阶有理积分。
    """
    de, fa, fd = build_extension(f, x)
    # 找最外层塔层
    j = len(de.levels) - 1
    if j == 0:
        raise RischUnsupported("no extension layer in expression")
    case = de.cases[j]
    # M5.2 单层限制：多层塔的系数域含低层变量（递归塔 pending M5.2b）
    if len(de.levels) > 2:
        raise RischUnsupported(
            "multiple extension layers: recursive tower pending M5.2b")
    if case == "primitive":
        return risch_primitive_integrate(fa, fd, de, j)
    return _integrate_exp_layer(fa, fd, de, j)


def _integrate_exp_layer(fa, fd, de, j):
    """exp 层积分（M5.1 算法体）。"""
    from cas.integrate import integrate_rational
    from cas.ratfunc import RatFunc

    eta_p = de.ws[j][0]
    (rat_part, logs, nonel, leftover), freqs, st = risch_exp_integrate(fa, fd, de, j)

    # 频率逐阶 RDE
    freq_terms = []       # [(b_k, k)] -> b_k * t^k
    rde_fail = None       # 首个无解频率（不可初等证明载体）
    for k in sorted(freqs):
        g = freqs[k]
        if k == 0:
            leftover = [g] if leftover is None else _u_add(leftover, [g], RatFunc.zero((de.levels[0],)))
            continue
        if not g.q.is_const():
            raise RischUnsupported(
                "RDE with rational g pending: eta' polynomial restriction")
        b = _rde_exp_solve(k, eta_p, g.p, g.q, Poly.zero((de.levels[0],)))
        if b is None:
            rde_fail = k
            break
        bp = RatFunc.from_poly(b)
        if not bp.is_zero():
            freq_terms.append((bp, k))

    expr = assemble_exp_result(rat_part, logs, nonel, de, j)
    tj = de.levels[j]
    for bk, k in freq_terms:
        bt = T.subst(bk.to_term(), {tj: de.terms[j]})
        tk = T.pw(de.terms[j], N(k)) if k != 1 else de.terms[j]
        parts = T.times(bt, tk)
        expr = T.plus(expr, parts)
    if leftover is not None and any(not c.is_zero() for c in leftover):
        lf = _u_trim(list(leftover))
        cv = Fr(0)
        for c in lf:
            if not c.is_zero():
                if not c.is_const():
                    raise RischUnsupported(
                        "non-constant theta-free leftover over Q(x)")
                cv += c.const_val()
        P = Poly.const((de.levels[0],), cv)
        val, ok, _method = integrate_rational(P, Poly.one((de.levels[0],)), de.levels[0])
        if not ok:
            raise RischUnsupported("leftover rational integration failed")
        expr = T.plus(expr, val)
    if rde_fail is not None:
        from cas.pprint import to_str as _ts

        g = freqs[rde_fail]
        raise RischNonElementary(
            "not elementary: the %s component has no rational solution of "
            "the Risch differential equation y' + %d*eta'*y = %s "
            "(proved; eta' = %s)" % (
                ("t^%d" % rde_fail) if rde_fail != 1 else "t",
                rde_fail,
                _ts(g.to_term()),
                _ts(RatFunc(eta_p, Poly.one(eta_p.vars)).to_term()),
            )
        )
    return expr, de


# ---------------------------------------------------------------------------
# M5.2：primitive 层积分（θ = log(u)，Dθ = v = u'/u ∈ K，K = Q(x) 单层）
#
# 多项式部分 Σ a_k θ^k 总可积：逐阶 Db_k = a_k − (k+1)·v·b_{k+1} 归到
# Q(x) 有理积分（完备）；log/atan 成分剥离直进结果（入 b_k 会以
# k·v·log(·) 污染高阶方程）。真分式走 Hermite+residue（θ 正规——
# gcd(θ, v) = 1，无 special 因子，比 exp 干净）。
# ---------------------------------------------------------------------------

def _integrate_poly_part_prim(Q, de, j):
    """∫ Σ a_k θ^k -> ([(b_k, k)], extras)。

    sympy integrate_primitive_polynomial 同构（limited_integrate 循环）：
    每轮取残差最高次系数 a，求 (b, c) 使 Db + c·v = a（K=Q(x) 特化：
    c = ∫a 的 log(u) 成分系数——齐次常数/升次统一于此；b = 有理部分），
    贡献 c·θ^{m+1}/(m+1) + b·θ^m，残差严格降次终止。
    非 log(u) 的 log/atan 成分 = 需要新 primitive 层，诚实拒答
    （不是不可积证明——是当前塔覆盖不足）。
    """
    from cas.ratfunc import RatFunc
    from cas.integrate import integrate_rational

    v = _exp_w(de, j)
    xv = de.levels[0]
    zero = RatFunc.zero((xv,))
    out = []
    extras = []
    p = list(Q)
    while not _u_is_zero(p):
        m = len(p) - 1
        a = p[m]
        _t, ok, _prov, rat_term, extra = integrate_rational(
            a.p, a.q, xv, structured=True)
        if not ok:
            raise RischUnsupported(
                "rational integration failed in primitive poly part")
        try:
            rf = RatFunc.from_term(rat_term, (xv,))
        except PolyError:
            raise RischUnsupported(
                "non-rational rational part in primitive poly part")
        c = None
        if extra is not T.ZERO:
            wn, wd = de.ws[j]
            alpha, rest = _split_log_coeff(extra, wd.to_term())
            if rest is not T.ZERO:
                raise RischUnsupported(
                    "integral requires a new logarithmic extension "
                    "(pending recursive tower)")
            if alpha != 0:
                c = alpha
        q0 = [zero] * (m + 2)
        if c is not None:
            q0[m + 1] = zero.one(zero.p.vars) * (Fr(c) / Fr(m + 1))
        q0[m] = rf
        p = _u_sub(p, _derive_ut(q0, de, j))
        if not q0[m + 1].is_zero():
            out.append((q0[m + 1], m + 1))
        if not q0[m].is_zero():
            out.append((q0[m], m))
    return out, extras


def _split_log_coeff(extra, u_term):
    """extra（term）-> (alpha: Fr, rest: term)。

    提取 Log(恰为 u_term) 成分的总系数（驻留指针判等）；其余成分重组。
    """
    parts = extra.args if isinstance(extra, T.Expr) \
        and extra.head.name == "Plus" else (extra,)
    alpha = Fr(0)
    rest_parts = []
    for t in parts:
        hit, coef = _log_u_factor(t, u_term)
        if hit:
            alpha += T.num_val(coef)
        else:
            rest_parts.append(t)
    rest = T.mk(S("Plus"), tuple(rest_parts)) if len(rest_parts) > 1 \
        else (rest_parts[0] if rest_parts else T.ZERO)
    return alpha, rest


def _log_u_factor(t, u_term):
    """t 是否含 Log(u_term) 因子。-> (bool, 系数 term)。"""
    if isinstance(t, T.Expr) and t.head.name == "Log" \
            and len(t.args) == 1 and t.args[0] is u_term:
        return True, T.ONE
    if isinstance(t, T.Expr) and t.head.name == "Times":
        lgs = [a for a in t.args if isinstance(a, T.Expr)
               and a.head.name == "Log" and len(a.args) == 1
               and a.args[0] is u_term]
        if len(lgs) == 1:
            coef = T.ONE
            for o in t.args:
                if o is not lgs[0]:
                    coef = T.times(coef, o)
            return True, coef
    return False, None


def risch_primitive_integrate(fa, fd, de, j):
    """primitive 层积分主入口（M5.2：K = Q(x) 单层）。"""
    from cas.ratfunc import RatFunc

    zero = RatFunc.zero((de.levels[0],))
    tj = de.levels[j]

    A = _univar(fa, tj)
    D = _univar(fd, tj)
    if _u_is_zero(A):
        return T.ZERO, de

    expr = T.ZERO
    dq = len(D) - 1
    dp = len(A) - 1
    if dp >= dq:
        Q, R = _u_divmod(A, D, zero)
        pairs, extras = _integrate_poly_part_prim(Q, de, j)
        for bk, k in pairs:
            bt = T.subst(bk.to_term(), {tj: de.terms[j]})
            tk = T.pw(de.terms[j], N(k)) if k != 1 else de.terms[j]
            expr = T.plus(expr, T.times(bt, tk))
        A = R
    else:
        extras = []
    if not _u_is_zero(A):
        res, _negf, st = _integrate_proper(A, D, de, j, zero)
        sub_expr = assemble_exp_result(res[0], res[1], res[2], de, j)
        expr = T.plus(expr, sub_expr)
        if res[3] is not None and any(not c.is_zero() for c in res[3]):
            lf = _u_trim(list(res[3]))
            if all(c.is_const() for c in lf):
                cv = sum((c.const_val() for c in lf), Fr(0))
                from cas.integrate import integrate_rational as _ir

                val, ok, _m = _ir(Poly.const((de.levels[0],), cv),
                                  Poly.one((de.levels[0],)), de.levels[0])
                if not ok:
                    raise RischUnsupported("leftover rational integration failed")
                expr = T.plus(expr, val)
            else:
                # θ-多项式剩余：递归（deg_θ 严格小于原，终止）
                fn, fdd = _from_univar(lf, de.vars, tj)
                sub2, _de2 = risch_primitive_integrate(fn, fdd, de, j)
                expr = T.plus(expr, sub2)
    for e in extras:
        expr = T.plus(expr, e)
    return expr, de
