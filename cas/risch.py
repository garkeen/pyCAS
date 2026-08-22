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
    ws[i]：RatFunc（K_{i-1} 上）——exp: D(t_i) = w*t_i；
    primitive: D(t_i) = w；
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
        w = self.ws[j]
        wn = _embed(w.p, all_vars)
        wd = _embed(w.q, all_vars)
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

def _tower_deriv_frac(nn, nd, de):
    """D(nn/nd) 在塔上的 RatFunc（nn, nd: Poly(de.vars)）。"""
    from cas.ratfunc import RatFunc

    an, ad = derivation(nn, de)
    bn, bd = derivation(nd, de)
    num = an * bd * nd - nn * bn * ad
    den = ad * bd * nd * nd
    return RatFunc(num, den)


def _tower_logderiv(nn, nd, de):
    """D(nn/nd)/(nn/nd)（primitive 层 w = u'/u）在塔上的 RatFunc。"""
    from cas.ratfunc import RatFunc

    an, ad = derivation(nn, de)
    bn, bd = derivation(nd, de)
    num = an * bd * nd - nn * bn * ad
    den = ad * bd * nn * nd     # 注意分母含 nn——除以 u 本身
    return RatFunc(num, den)


def build_extension(f, x):
    """term -> (DiffExt, fa, fd)：f 在塔上的 (num, den) 表示。

    建塔顺序 log 先 exp 后（sympy handle_first='log' 同款：primitive
    在下、超指数在外）。参数重写到当前塔上表示（M5.2b 多层：log(log x)
    类嵌套合法）；参数非塔上有理函数 -> RischUnsupported。
    """
    from cas.ratfunc import RatFunc

    de = DiffExt(x)
    subs = {}   # 原始 Exp/Log term -> 塔符号（驻留键）

    def tower_frac(t):
        """t 在当前塔上的 (num, den)；含未覆盖 Exp/Log/非有理 -> PolyError。"""
        g = T.subst(t, subs) if subs else t
        return _frac_from_term(g, de.vars)

    # 工作队列：反复扫描直到无新层可建（嵌套参数依赖内层先建，
    # 如 log(log(x)) 外层需等内层）；永久建不了的由末尾残留检查拒绝。
    while True:
        exps, logs = _collect_exts(f)
        changed = False

        # log 层（primitive）：u = 塔上分式且非常数
        for u in logs:
            key = T.mk(S("Log"), (u,))
            if key in subs:
                continue
            try:
                un, ud = tower_frac(u)
            except PolyError:
                continue   # 本轮建不了（内层未就绪或永不可建）
            if un.is_const() and ud.is_const():
                continue   # log(常数) 属常数域，不建层
            w = _tower_logderiv(un, ud, de)   # D(u)/u
            tl = de.add("primitive", w, key, "l")
            subs[key] = T.S(tl.name)
            changed = True

        # exp 层（hyperexponential）：base = 塔上分式，Fr 倍数归组
        for base, members in _group_integer_powers(exps):
            key = T.mk(S("Exp"), (base,))
            if key in subs:
                continue
            try:
                bn, bd = tower_frac(base)
            except PolyError:
                continue
            if bn.is_const() and bd.is_const():
                continue   # exp(常数) = 常数因子
            # 代数依赖守卫：base 含既有塔变量 => e^base 与塔代数相关
            # （如 exp(log(x)/2): t² = x），破坏超越性 => 诚实拒绝
            if any(e > 0 for mono in bn.monos for e in mono[1:]) \
                    or any(e > 0 for mono in bd.monos for e in mono[1:]):
                raise RischUnsupported(
                    "exponent depends on existing tower variables: "
                    "algebraic dependency")
            w = _tower_deriv_frac(bn, bd, de)   # eta' = D(base)
            t = de.add("exp", w, key, "t")
            subs[key] = T.S(t.name)
            changed = True

        if not changed:
            break

    # 重写 f 到塔上：Exp(m*base) -> t^m（归组成员按幂次展开），Log(u) -> tl
    full_subs = dict(subs)
    for base, members in _group_integer_powers(_collect_exts(f)[0]):
        key = T.mk(S("Exp"), (base,))
        if key not in subs:
            continue
        tv = subs[key]
        for arg, m in members:
            full_subs[T.mk(S("Exp"), (arg,))] = T.pw(tv, N(m)) if m != 1 else tv
    g = T.subst(f, full_subs) if full_subs else f

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

def tower_to_term_pair(a, d, de, backsub=True):
    """(num, den) Poly -> term（backsub=False 保留塔符号）。"""
    nt = a.to_term() if not a.is_zero() else T.ZERO
    dt = d.to_term()
    val = T.div(nt, dt) if not dt is T.ONE else nt
    if not backsub:
        return val
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
    """塔上 D 作用于 Σ a_k t_j^k -> K[t] 系数 list（K 是域，无分母）。

    exp:       D(Σa_k t^k) = Σ (Da_k + k·η'·a_k) t^k          （对角）
    primitive: D(Σa_k θ^k) = Σ_i (Da_i + (i+1)·v·a_{i+1}) θ^i  （移位）
    """
    from cas.ratfunc import RatFunc

    w = de.ws[j]
    zv = RatFunc.zero(w.p.vars)   # 系数域零元（vars = levels[:j]）
    n = len(coeffs)
    out = []
    for i in range(n):
        a = coeffs[i]
        # K 层导数必须是塔上导数 D_K（多层时 d/dx 不够——D(l)=1/x 类）
        term = _tower_deriv_frac(a.p, a.q, de) if not a.is_zero() else zv
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
    return de.ws[j]


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
    z0 = b[0] * 0 if n else Fr(0)   # 系数域零元（Fr/Ga 通用）
    sol = [z0] * cols
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
                # 剩余恰为多项式：exp 下全部进频率（k=0 分量由低层递归
                # 积分处理）；primitive 下回本层多项式循环（leftover）
                if de.cases[j] == "exp":
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
    """积分结果 -> 塔符号 term（不回写——出口统一 backsubst）。"""
    tj = de.levels[j]
    rat_part = rat_part or []
    logs = logs or []
    parts = []
    for u, p, k in rat_part:
        un, ud = _from_univar(u, de.vars, tj)
        pn, pd = _from_univar(p, de.vars, tj)
        ut = tower_to_term_pair(un, ud, de, backsub=False)
        pt = tower_to_term_pair(pn, pd, de, backsub=False)
        parts.append(T.div(ut, T.pw(pt, N(k))))
    for c, g in logs:
        gn, gd = _from_univar(g, de.vars, tj)
        gt = tower_to_term_pair(gn, gd, de, backsub=False)
        parts.append(T.times(c, T.log(gt)))
    if nonel is not None:
        num, p = nonel
        nn, nd = _from_univar(num, de.vars, tj)
        pn, pd = _from_univar(p, de.vars, tj)
        from cas.pprint import to_str as _ts

        raise RischNonElementary(
            "integral of " + _ts(T.div(
                tower_to_term_pair(nn, nd, de, backsub=False),
                tower_to_term_pair(pn, pd, de, backsub=False))) +
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
    """顶层 API：term -> (term, de)（初等原函数）或异常。

    M5.2b 递归塔：任意 primitive/exp 层序列，K 上积分递归下降。
    内部全程塔符号空间，出口统一回写。
    """
    de, fa, fd = build_extension(f, x)
    j = len(de.levels) - 1
    if j == 0:
        raise RischUnsupported("no extension layer in expression")
    expr = _risch_rec(fa, fd, de, j)
    subs = {T.S(de.levels[i].name): de.terms[i]
            for i in range(1, len(de.levels))}
    if subs:
        expr = T.subst(expr, subs)
    return expr, de


def _integrate_in_K(g, de, j):
    """∫g dx，g ∈ K_j = ℚ(x, t₁..t_{j-1})（RatFunc on levels[:j]）→ term。"""
    from cas.integrate import integrate_rational

    if j <= 1:
        xv = de.levels[0]
        val, ok, _prov = integrate_rational(g.p, g.q, xv)
        if not ok:
            raise RischUnsupported("rational integration failed in base field")
        return val
    return _risch_rec(g.p, g.q, de, j - 1)


def _limited_integrate(a, de, j):
    """K_j 上求 (b_rf, c) 使 Db + c·v = a（limited integration 问题）。

    全程塔符号空间：c = ∫a 中 log(θ_j) 成分系数——θ_j 的对数形态
    Log(u_j) 的塔符号即本层变量自身。其余 log/atan 成分无法由 b ∈ K_j
    解释 -> rest ≠ 0 表示该塔内无解形态。
    """
    from cas.ratfunc import RatFunc

    syms = {de.terms[i]: T.S(de.levels[i].name)
            for i in range(1, len(de.levels))}
    u_sym = T.subst(de.terms[j].args[0], syms)   # u_j 的塔符号形态
    val = _integrate_in_K(a, de, j)
    rat_t, alpha, rest = _decompose_integral(val, u_sym, syms)
    if rest is not T.ZERO:
        return None, None, rest
    try:
        b_rf = RatFunc.from_term(rat_t, tuple(de.levels[:j]))
    except PolyError:
        return None, None, val
    return b_rf, (alpha if alpha != 0 else None), T.ZERO


def _has_trans_head(t):
    """t 是否含 Log/Atan 头（任意深度）。"""
    stack = [t]
    while stack:
        u = stack.pop()
        if isinstance(u, T.Expr):
            if u.head.name in ("Log", "Atan"):
                return True
            stack.extend(u.args)
    return False


def _decompose_integral(val, u_sym, syms):
    """塔符号空间的初等原函数 term -> (rat_term, alpha, rest)。

    - Log(g) 且 g ≡ u_sym：alpha 累加（limited 的 c）
    - Log(g) 且 g ≡ 某已建层参数 u_i：替换为塔符号 S(levels[i])（低层
      residue 出的 log(θ_i) 即 θ_i 自身形态，归 rat）
    - 其余含 Log/Atan 头：rest（新层候选，塔外成分）
    - 纯有理：rat
    """
    parts = val.args if isinstance(val, T.Expr) and val.head.name == "Plus" \
        else (val,)
    alpha = Fr(0)
    rest_parts = []
    rat_parts = []
    for t in parts:
        hit, coef = _log_u_factor_generic(t, u_sym)
        if hit:
            alpha += T.num_val(coef)
            continue
        mapped, new_t = _map_known_log(t, syms)
        if mapped:
            rat_parts.append(new_t)
        elif _has_trans_head(t):
            rest_parts.append(t)
        else:
            rat_parts.append(t)
    rat_t = T.mk(S("Plus"), tuple(rat_parts)) if len(rat_parts) > 1 \
        else (rat_parts[0] if rat_parts else T.ZERO)
    rest = T.mk(S("Plus"), tuple(rest_parts)) if len(rest_parts) > 1 \
        else (rest_parts[0] if rest_parts else T.ZERO)
    return rat_t, alpha, rest


def _log_u_factor_generic(t, u_sym):
    """t 是否含 Log(恰为 u_sym) 因子。-> (bool, 系数 term)。"""
    if isinstance(t, T.Expr) and t.head.name == "Log" \
            and len(t.args) == 1 and t.args[0] is u_sym:
        return True, T.ONE
    if isinstance(t, T.Expr) and t.head.name == "Times":
        lgs = [a for a in t.args if isinstance(a, T.Expr)
               and a.head.name == "Log" and len(a.args) == 1
               and a.args[0] is u_sym]
        if len(lgs) == 1:
            coef = T.ONE
            for o in t.args:
                if o is not lgs[0]:
                    coef = T.times(coef, o)
            return True, coef
    return False, None


def _map_known_log(t, syms):
    """t 中 Log(u_i)（u_i = 第 i 层参数）替换为塔符号 S(levels[i])。

    返回 (是否替换发生, 新 term)。t 不含任何已知 Log 时 (False, t)。
    """
    if not isinstance(t, T.Expr):
        return False, t
    hit = [False]

    def rec(u):
        if not isinstance(u, T.Expr):
            return u
        if u.head.name == "Log" and len(u.args) == 1:
            for key, sym in syms.items():
                if isinstance(key, T.Expr) and key.head.name == "Log" \
                        and len(key.args) == 1 and key.args[0] is u.args[0]:
                    hit[0] = True
                    return sym
        return T.mk(u.head, tuple(rec(a) for a in u.args))

    out = rec(t)
    return hit[0], out


def _primitive_poly_part(Q, de, j):
    """∫ Σ a_k θ^k：limited_integrate 循环（sympy integrate_primitive_polynomial
    同构）。每轮残差最高次严格下降，终止。"""
    from cas.ratfunc import RatFunc
    from cas.pprint import to_str as _ts

    sub = tuple(de.levels[:j])
    zero = RatFunc.zero(sub)
    out = []
    p = list(Q)
    while not _u_is_zero(p):
        m = len(p) - 1
        a = p[m]
        b_rf, c, rest = _limited_integrate(a, de, j)
        if b_rf is None:
            raise RischUnsupported(
                "component requires integration outside the tower: "
                + _ts(rest)[:80])
        q0 = [zero] * (m + 2)
        if c is not None:
            q0[m + 1] = zero.one(zero.p.vars) * (Fr(c) / Fr(m + 1))
        q0[m] = b_rf
        p = _u_sub(p, _derive_ut(q0, de, j))
        if not q0[m + 1].is_zero():
            out.append((q0[m + 1], m + 1))
        if not q0[m].is_zero():
            out.append((q0[m], m))
    return out


# ---------------------------------------------------------------------------
# M5.2c：塔系数域上的 Risch 微分方程（exp 层频率方程 y' + k·w·y = g，
# y ∈ K_j 含低层塔变量）。f = k·w 不含塔变量（exp 守卫保证）=> 极点分析
# 直接成立：den(y) | Π s^{e-1}（s^e ∥ den(g) 正规因子）——无需 weak
# normalization（那处理的是 f 本身有塔极点的 cancellation 情形）。
# 多项式化后 K 域线性系统待定系数；有解经精确验证输出，无解返回 None
# （unsupported，绝不误判不可积——完整 cancellation 分析留后续）。
# ---------------------------------------------------------------------------

def _u_gauss_solve_k(M, b):
    """K 域（RatFunc）线性方程组高斯消元。返回解 list | None（无解）。"""
    n = len(M)
    cols = len(M[0]) if n else 0
    if n == 0 or cols == 0:
        return [] if not any(not x.is_zero() for x in b) else None
    one = b[0].one(b[0].p.vars)
    A = [list(M[r]) + [b[r]] for r in range(n)]
    piv_cols = []
    r = 0
    for cidx in range(cols):
        piv = None
        for i in range(r, n):
            if not A[i][cidx].is_zero():
                piv = i
                break
        if piv is None:
            continue
        A[r], A[piv] = A[piv], A[r]
        pv = A[r][cidx]
        inv = one / pv
        A[r] = [x * inv for x in A[r]]
        for i in range(n):
            if i != r and not A[i][cidx].is_zero():
                fac = A[i][cidx]
                A[i] = [vi - fac * vr for vi, vr in zip(A[i], A[r])]
        piv_cols.append(cidx)
        r += 1
        if r == n:
            break
    for i in range(n):
        if all(x.is_zero() for x in A[i][:cols]) and not A[i][cols].is_zero():
            return None
    sol = [one.zero(one.p.vars) for _ in range(cols)]
    for i, cidx in enumerate(piv_cols):
        sol[cidx] = A[i][cols]
    return sol


def _restrict(rf, vars_):
    """RatFunc 收缩到指定变量集（缺失维度指数须全零，否则 PolyError）。"""
    from cas.ratfunc import RatFunc as _RF

    def shrink(p):
        if p.vars == tuple(vars_):
            return p
        idx = {v: i for i, v in enumerate(p.vars)}
        out = {}
        for k, c in p.monos.items():
            for v in p.vars:
                if v not in vars_ and k[idx[v]] != 0:
                    raise PolyError("cannot restrict: variable present")
            out[tuple(k[idx[v]] if v in idx else 0 for v in vars_)] = c
        return Poly(tuple(vars_), out)

    return _RF(shrink(rf.p), shrink(rf.q))


# ---------------------------------------------------------------------------
# M5.2c-ii：塔域 Risch DE 完备判定
#
# 解 D(y) + f·y = g（y ∈ K_j = ℚ(x, t₁..t_{j-1})），三态返回：
#   (y, 'ok')          有理解（出口精确验证兜底，验证不过 = 内部错误异常）
#   (None, 'proved')   无有理解的机器证明（界否定/贪心余量/整除性失败）
#   (None, 'undecided') 当前理论不可判——绝不猜测、绝不误证
#
# 唯一算法参考：FriCAS intpar.spad ParametricRischDE（weak normalization
# :920 / get_denom :910 / 变换 :1406-1410 / 右端缩放 :1237）+ sympy rde.py
# 的 bound_degree / spde / no_cancel_b_large / no_cancel_b_small /
# no_cancel_equal / cancel_* 分派细节补全。已知切片边界（触发时诚实
# undecided，绝不降级猜测）：
#   S-a primitive db==da 共振的 radical 判定（is_log_deriv_k_t_radical）
#   S-b B==0 cancellation（is_deriv_in_field 机器）
#   S-c 非常数比值的共振判定（limited_integrate / parametric_log_deriv 完整版）
# ---------------------------------------------------------------------------


def _fu_add(n1, d1, n2, d2, zero):
    """K[t] 分式加法（n/d 为 univar list；空分母按单位 1 规范化）。"""
    one_c = zero.one(zero.p.vars)
    d1 = d1 if d1 else [one_c]
    d2 = d2 if d2 else [one_c]
    return (_u_add(_u_mul(n1, d2, zero), _u_mul(n2, d1, zero), zero),
            _u_mul(d1, d2, zero))


def _fu_mul(n1, d1, n2, d2, zero):
    one_c = zero.one(zero.p.vars)
    d1 = d1 if d1 else [one_c]
    d2 = d2 if d2 else [one_c]
    return (_u_mul(n1, n2, zero), _u_mul(d1, d2, zero))


def _u_deg(cs):
    return len(_u_trim(list(cs))) - 1


def _u_xgcd(a, b, zero):
    """扩展欧几里得：返回 (s, t, g) 使 s·a + t·b = g。"""
    one_c = zero.one(zero.p.vars)
    r0, r1 = _u_trim([c for c in b]), _u_trim([c for c in a])
    s0, s1 = [], [one_c]
    t0, t1 = [one_c], []
    while not _u_is_zero(r1):
        q, r = _u_divmod(r0, r1, zero)
        s_new = _u_sub(s0, _u_mul(q, s1, zero))
        t_new = _u_sub(t0, _u_mul(q, t1, zero))
        r0, r1 = r1, r
        s0, s1 = s1, s_new
        t0, t1 = t1, t_new
    if _u_is_zero(r0):
        return s0, t0, []
    inv = one_c / r0[0]
    return [c * inv for c in s0], [c * inv for c in t0], \
        [c * inv for c in r0]


def _u_diophantine(b, a, c, zero):
    """解 r·b + z·a = c（sympy gcdex_diophantine(b, a, c) 语义）。"""
    s, t, g = _u_xgcd(b, a, zero)
    if _u_is_zero(g):
        return None
    qq, rr = _u_divmod(c, g, zero)
    if not _u_is_zero(rr):
        return None
    return _u_mul(s, qq, zero), _u_mul(t, qq, zero)


def _split_ns(p, der_fn, zero):
    """intrf.spad:141 split：p = normal·special。

    normal 的平方因子与 D(p) 互素；special 为 D-不变型因子。
    返回 (normal_list, special_list)。
    """
    p = _u_trim(list(p))
    if _u_is_zero(p) or len(p) <= 1:
        return list(p), []
    dp = der_fn(p)
    dfp = _u_formal_deriv(p)
    if _u_is_zero(_u_sub(dp, dfp)):
        return list(p), []
    g = _u_gcd(p, dp, zero)
    if len(g) <= 1:
        return list(p), []
    gd = _u_gcd(p, dfp, zero)
    if len(gd) <= 1:
        pbar = list(g)
    else:
        pbar, r = _u_divmod(g, gd, zero)
        if not _u_is_zero(r):
            return list(p), []
    if len(pbar) <= 1:
        return list(p), []
    rest, rr = _u_divmod(p, pbar, zero)
    if not _u_is_zero(rr):
        return list(p), []
    rn, rs = _split_ns(rest, der_fn, zero)
    return rn, _u_mul(pbar, rs, zero)


def _normal_part(p, der_fn, zero):
    return _split_ns(p, der_fn, zero)[0]


def _make_der_fn(de, jv):
    """视图层 jv 的 K[t]-导子 der1：D(Σcᵢτⁱ)。jv==0 时 D=d/dx、dk=1。"""
    if jv == 0:
        def der_fn(cs):
            out = []
            nn = len(cs)
            for i in range(nn):
                a = cs[i]
                term = a.deriv(de.levels[0]) if not a.is_zero() \
                    else a * Fr(0)
                if i + 1 < nn and not cs[i + 1].is_zero():
                    term = term + cs[i + 1] * Fr(i + 1)
                out.append(term)
            return _u_trim(out)
        return der_fn
    return lambda cs: _derive_ut(cs, de, jv)


def _wn_normalize(fn, fd, de, jv, der_fn, zero):
    """intpar.spad:920 weak normalization（非参数化特化）。

    返回 (fn2, fd2, pn, pd)：f_new = fn2/fd2 已消 normal 极点；
    p = pn/pd 使 v = y·p 时新方程右端须 ×p（intpar:1237）、解 ÷p（:1239）。
    无法判定返回 None。
    """
    one_c = zero.one(zero.p.vars)
    pn, pd = [one_c], []
    d = _normal_part(fd, der_fn, zero)
    if len(d) <= 1:
        return list(fn), list(fd), pn, pd
    g0 = _u_gcd(d, der_fn(d), zero)
    d0 = _u_divmod(d, g0, zero)[0]
    dd = _u_gcd(d0, g0, zero)
    d1 = _u_divmod(d0, dd, zero)[0]
    if len(d1) <= 1:
        return list(fn), list(fd), pn, pd
    q2, r2 = _u_divmod(fd, d1, zero)
    if not _u_is_zero(r2):
        return None
    d2 = q2
    s_, _t_, g_ = _u_xgcd(d2, d1, zero)
    if _u_is_zero(g_):
        return None
    qqf, rf = _u_divmod(fn, g_, zero)
    if not _u_is_zero(rf):
        return None
    a_ = _u_mul(s_, qqf, zero)
    d1d = der_fn(d1)
    nb = max(len(a_), len(d1d))
    a_pad = list(a_) + [zero for _ in range(nb - len(a_))]
    d_pad = list(d1d) + [zero for _ in range(nb - len(d1d))]
    fz = [[ai, c * Fr(-1)] for ai, c in zip(a_pad, d_pad)]
    gz = [[ci] for ci in d1]
    Rz = _sylvester_res(fz, gz)
    rl = []
    if Rz and not _u_is_zero(Rz):
        for mval in _constant_roots(Rz):
            try:
                mv = mval if isinstance(mval, Fr) else Fr(mval)
            except Exception:
                return None
            if mv.denominator != 1 or mv <= 0:
                continue
            fm = _u_sub(a_pad, [c * mv for c in d_pad])
            pi_m = _u_gcd(fm, d1, zero)
            if len(pi_m) <= 1:
                continue
            rl.append((pi_m, int(mv)))
    fn2, fd2 = list(fn), list(fd)
    for pi_m, mv in rl:
        fn2, fd2 = _fu_sub(fn2, fd2,
                           [c * Fr(mv) for c in der_fn(pi_m)],
                           list(pi_m), zero)
        for _ in range(mv):
            pn, pd = _fu_mul(pn, pd, list(pi_m), [], zero)
    return fn2, fd2, pn, pd


def _dk_pair(de, jv):
    """D(levels[jv]) 的 τ-系数表示 (n_list, d_list)。"""
    tview = de.levels[jv]
    dk_n, dk_d = de.dpair(jv, tuple(de.levels[:jv + 1]))
    return _univar(dk_n, tview), _univar(dk_d, tview)


def _solve_low(lam, rhs, de, jl):
    """低层 RDE D(s)+λ·s=rhs，s ∈ levels[:jl]（jl>=1 递归，jl==0 基层）。"""
    if jl >= 1:
        return _rde_tower_solve(lam, rhs, de, jl)
    return _rde_base_rde(lam, rhs, de)


def _rde_base_rde(lam, rhs, de):
    """ℚ(x)：D(s)+λ·s=rhs。λ 多项式 -> 极点分析完备判定；否则 undecided。"""
    from cas.ratfunc import RatFunc

    xv = de.levels[0]
    if not (lam.q.is_const() and lam.p.vars == (xv,) and
            rhs.p.vars == (xv,) and rhs.q.vars == (xv,)):
        return None, 'undecided'
    # λ 任意多项式（含常数）、rhs 任意有理式：极点分析 + 待定系数完备
    b = _rde_exp_solve(1, lam.p, rhs.p, rhs.q, Poly.zero((xv,)))
    if b is None:
        return None, 'proved'
    if isinstance(b, Poly):
        b = RatFunc.from_poly(b)
    return b, 'ok'


def _poly_rde_final(bbr, cn, n, case_v, base_flag, dk_deg, dk_ncs,
                    der_fn, de, jv, zero):
    """sympy solve_poly_rde 非参数版：解 D(u)+bbr·u=cn（deg u ≤ n）。

    返回 ('ok', u_list) | ('proved', None) | ('undecided', reason)。
    """
    dB = _u_deg(bbr)
    thr = max(0, dk_deg - 1)

    def corr(cc, pmono):
        return _u_sub(cc, _u_add(der_fn(pmono), _u_mul(bbr, pmono, zero),
                                 zero))

    # no_cancel_b_large
    if not _u_is_zero(bbr) and (base_flag or dB > thr):
        u_acc, cc, mm = [], list(cn), n
        while not _u_is_zero(cc):
            stp = _u_deg(cc) - dB
            if stp < 0 or stp > mm:
                return 'proved', None
            pmono = [zero for _ in range(stp)] + [cc[-1] / bbr[dB]]
            u_acc = _u_add(u_acc, pmono, zero)
            mm = stp - 1
            cc = corr(cc, pmono)
        return 'ok', u_acc

    # no_cancel_b_small（含降到低层的 (h,b0,c0) 归约）
    if (_u_is_zero(bbr) or dB < dk_deg - 1) and (base_flag or dk_deg >= 2):
        u_acc, cc, mm = [], list(cn), n
        low_eq = None
        while not _u_is_zero(cc):
            dcc = _u_deg(cc)
            stp = 0 if mm == 0 else dcc - dk_deg + 1
            if stp < 0 or stp > mm:
                return 'proved', None
            if stp > 0:
                pmono = [zero for _ in range(stp)] + \
                    [cc[-1] / (dk_ncs[dk_deg] * Fr(stp))]
            else:
                if dB != dcc:
                    return 'proved', None
                if dB == 0:
                    low_eq = (bbr[0], cc[0])
                    break
                pmono = [cc[-1] / bbr[0]]
            u_acc = _u_add(u_acc, pmono, zero)
            mm = stp - 1
            cc = corr(cc, pmono)
        if low_eq is not None:
            yl, stl = _solve_low(low_eq[0], low_eq[1], de, jv)
            if stl != 'ok':
                return stl, None
            return 'ok', _u_add(u_acc, [yl], zero)
        return 'ok', u_acc

    # no_cancel_equal（共振贪心，自包含）
    if dk_deg >= 2 and dB == dk_deg - 1:
        lc_ratio = (bbr[dB] * Fr(-1)) / dk_ncs[dk_deg]
        big_m = -1
        if lc_ratio.is_const() and lc_ratio.const_val().denominator == 1 \
                and lc_ratio.const_val() > 0:
            big_m = int(lc_ratio.const_val())
        u_acc, cc, mm = [], list(cn), n
        while not _u_is_zero(cc):
            dcc = _u_deg(cc)
            stp = max(big_m, dcc - dk_deg + 1)
            if stp < 0 or stp > mm:
                return 'proved', None
            uu = stp * dk_ncs[dk_deg] + bbr[dB]
            if uu.is_zero():
                return 'undecided', 'no_cancel_equal tail recursion pending'
            if stp > 0:
                pmono = [zero for _ in range(stp)] + [cc[-1] / uu]
            else:
                if dcc != dk_deg - 1:
                    return 'proved', None
                pmono = [cc[-1] / bbr[dB]]
            u_acc = _u_add(u_acc, pmono, zero)
            mm = stp - 1
            cc = corr(cc, pmono)
        return 'ok', u_acc

    # cancellation 形态
    if _u_is_zero(bbr):
        return 'undecided', 'S-b: B=0 cancellation pending'
    if dB != 0:
        return 'undecided', 'unexpected B degree in cancellation shape'
    lam = bbr[0]
    w_eta = de.ws[jv] if case_v == 'exp' and jv >= 1 else None
    u_acc, cc, mm = [], list(cn), n
    while not _u_is_zero(cc):
        jd = _u_deg(cc)
        if jd > mm:
            return 'proved', None
        lam_j = lam + w_eta * Fr(jd) if w_eta is not None else lam
        s_rf, stl = _solve_low(lam_j, cc[-1], de, jv)
        if stl != 'ok':
            return stl, None
        stm = [zero for _ in range(jd)] + [s_rf]
        u_acc = _u_add(u_acc, stm, zero)
        mm = jd - 1
        cc = corr(cc, stm)
    return 'ok', u_acc


def _rde_tower_solve(f, g, de, j):
    """完备判定求解器入口（契约见块注释）。j>=2 进塔机制（视图 jv=j-1>=1）；
    j==1 即 ℚ(x) 基层，直接委托极点分析（基层无更低视图，塔机制不适用）。"""
    from cas.ratfunc import RatFunc

    if j < 1:
        return None, 'undecided'
    if j == 1:
        return _rde_base_rde(f, g, de)
    tview = de.levels[j - 1]
    case_v = de.cases[j - 1]
    jv = j - 1
    sub_vars = tuple(de.levels[:jv])

    def RF_of(ncs, dcs):
        nump = _from_univar(ncs, tuple(de.levels[:j]), tview)
        denp = _from_univar(dcs, tuple(de.levels[:j]), tview)
        if nump[0].is_zero():
            return RatFunc.zero(tuple(de.levels[:j]))
        return RatFunc(nump[0] * denp[1], denp[0] * nump[1])

    zero = RatFunc.zero(sub_vars)
    one_c = zero.one(sub_vars)
    der_fn = _make_der_fn(de, jv)

    dk_ncs, dk_dcs = _dk_pair(de, jv)
    if _u_deg(_u_formal_deriv(dk_dcs)) >= 0:
        return None, 'undecided'
    dk_deg = _u_deg(dk_ncs)

    fn = _univar(f.p, tview)
    fd = _univar(f.q, tview)
    gn = _univar(g.p, tview)
    gd = _univar(g.q, tview)

    # ---- Step 1: weak normalization（intpar:920；右端缩放 :1237）----
    wn = _wn_normalize(fn, fd, de, jv, der_fn, zero)
    if wn is None:
        return None, 'undecided'
    fn2, fd2, pn, pd = wn
    gn2, gd2 = _fu_mul(gn, gd, pn, pd, zero)

    # ---- Step 2: normal denominator -> 多项式方程（intpar:910, 1406-1410）----
    dn_ = _normal_part(fd2, der_fn, zero)
    en_ = _normal_part(gd2, der_fn, zero)
    gg = _u_gcd(dn_, en_, zero)
    hq, hr = _u_divmod(_u_gcd(en_, der_fn(en_), zero),
                       _u_gcd(gg, der_fn(gg), zero), zero)
    if not _u_is_zero(hr):
        return None, 'undecided'
    h = hq
    aa = _u_mul(dn_, h, zero)
    dh = der_fn(h)
    bbr_n = _u_sub(_u_mul(aa, fn2, zero), _u_mul(dn_, dh, zero))
    bq, br = _u_divmod(bbr_n, fd2, zero)
    if not _u_is_zero(br):
        return None, 'undecided'
    bbr = bq
    aa1 = _u_mul(aa, h, zero)
    cn, cd = _fu_mul(aa1, [one_c], gn2, gd2, zero)

    # ---- Step 3: C 的 τ-分母必须已消（Laurent 型右端 -> undecided）----
    if _u_deg(_u_formal_deriv(cd)) >= 0:
        return None, 'undecided'

    u_list = []
    if not _u_is_zero(cn):
        inv_cd = one_c / cd[0]
        cn = [c * inv_cd for c in cn]

        da, db, dc = _u_deg(aa), _u_deg(bbr), _u_deg(cn)
        base_flag = (case_v == 'base')

        # ---- Step 4: 次数界（sympy bound_degree 移植 + 切片边界）----
        if case_v == 'base':
            n = max(0, dc - max(db, da - 1))
            if db == da - 1 and da >= 1:
                al = (bbr[db] * Fr(-1)) / aa[da]
                if al.is_const():
                    cv = al.const_val()
                    if cv.denominator == 1:
                        n = max(n, int(cv), dc - db)
                else:
                    return None, 'undecided'
        elif case_v == 'primitive':
            n = max(0, dc - db) if db > da else max(0, dc - da + 1)
            if db == da - 1:
                al = (bbr[db] * Fr(-1)) / aa[da]
                eta_rf = RF_of(dk_ncs, dk_dcs)
                if not eta_rf.is_zero():
                    rho = al / eta_rf
                    if rho.is_const():
                        cv = rho.const_val()
                        if cv.denominator == 1 and cv > 0:
                            n = max(n, int(cv))
                    else:
                        return None, 'undecided'      # S-c
            elif db == da and da != 0:
                return None, 'undecided'              # S-a
            # da==db==0：cancellation 逐度下降，naive 界 n>=dc 不截断，
            # 无需共振修正（安全性：各度独立处理到底）
        else:  # exp
            n = max(0, dc - max(da, db))
            if da == db and da != 0:
                al = (bbr[db] * Fr(-1)) / aa[da]
                rho = al / de.ws[jv]
                if rho.is_const():
                    cv = rho.const_val()
                    if cv.denominator == 1 and cv > 0:
                        n = max(n, int(cv))
                else:
                    return None, 'undecided'          # S-c
            # da==db==0：exp 对角下降同理安全

        # ---- Step 5: spde 归约核（sympy spde 忠实移植）----
        alpha_l = [one_c]
        beta_l = []
        proved = False
        guard = 0
        while True:
            guard += 1
            if guard > 64:
                return None, 'undecided'
            if _u_is_zero(cn):
                break
            if n < 0:
                proved = True
                break
            gfac = _u_gcd(aa, bbr, zero)
            qa_, ra_ = _u_divmod(aa, gfac, zero)
            qb_, rb_ = _u_divmod(bbr, gfac, zero)
            qc_, rc_ = _u_divmod(cn, gfac, zero)
            if not _u_is_zero(rc_) or not _u_is_zero(ra_) \
                    or not _u_is_zero(rb_):
                proved = True                         # gcd ∤ => 无解
                break
            aa, bbr, cn = qa_, qb_, qc_
            if _u_deg(aa) == 0:
                inv_a = one_c / aa[0]
                bbr = [c * inv_a for c in bbr]
                cn = [c * inv_a for c in cn]
                break
            rz = _u_diophantine(bbr, aa, cn, zero)
            if rz is None:
                proved = True
                break
            r_, z_ = rz
            bbr = _u_add(bbr, der_fn(aa), zero)
            cn = _u_sub(z_, der_fn(r_))
            n -= _u_deg(aa)
            beta_l = _u_add(beta_l, _u_mul(alpha_l, r_, zero), zero)
            alpha_l = _u_mul(alpha_l, aa, zero)

        if proved:
            return None, 'proved'

        # ---- Step 6: 终解分派 ----
        if _u_is_zero(cn):
            u_list = list(beta_l)
        else:
            st_f, res_u = _poly_rde_final(bbr, cn, n, case_v, base_flag,
                                          dk_deg, dk_ncs, der_fn, de, jv,
                                          zero)
            if st_f != 'ok':
                return None, st_f
            u_list = _u_add(_u_mul(alpha_l, res_u, zero), beta_l, zero)

    # ---- Step 7: 组合 y = u/(h·p) + 出口精确验证 ----
    oneL = [one_c]
    ynum_cs = _u_mul(u_list, list(pd) or oneL, zero)
    yden_cs = _u_mul(h, list(pn) or oneL, zero)
    y = RF_of(ynum_cs, yden_cs)
    dy = _tower_deriv_frac(y.p, y.q, de)
    if not (dy + f * y - g).p.is_zero():
        raise RischUnsupported(
            "internal: RDE candidate failed exact verify "
            "(this is a bug, not an honest refusal)")
    return y, 'ok'


def _exp_freq_part(freqs, de, j):
    """exp 频率分量：k=0 → 低层递归积分；k≠0 → RDE。任一频率无解
    => 不可初等证明；理论无法判定（多元 cancellation 等）=> unsupported。"""
    from cas.ratfunc import RatFunc

    tj = de.levels[j]
    xv = de.levels[0]
    expr = T.ZERO
    freq_terms = []
    rde_fail = None
    for k in sorted(freqs):
        g = freqs[k]
        if k == 0:
            expr = T.plus(expr, _integrate_in_K(g, de, j))
            continue
        w = de.ws[j] * Fr(k)
        if g.q.is_const() and g.p.vars == (xv,) \
                and w.q.is_const() and w.p.vars == (xv,):
            # base 快路径：现有 ℚ(x) 极点分析求解器（无解即 proved——
            # η' 多项式保证界严格）
            b = _rde_exp_solve(k, de.ws[j].p, g.p, g.q, Poly.zero((xv,)))
            proved = b is None
        else:
            # 塔系数域：M5.2c-ii 完备判定求解器
            b, st = _rde_tower_solve(w, g, de, j)
            if st == 'proved':
                rde_fail = k
                break
            if st != 'ok':
                raise RischUnsupported(
                    "Risch DE on the tower undecidable with current theory "
                    "(%s); frequency k=%d" % (st, k))
        if b is None:
            if proved:
                rde_fail = k
                break
            raise RischUnsupported(
                "Risch DE on the tower undecidable with current theory "
                "(cancellation analysis pending); frequency k=%d" % k)
        bp = b
        if not bp.is_zero():
            freq_terms.append((bp, k))
    for bk, k in freq_terms:
        bt = bk.to_term()   # 塔符号形态（出口统一回写）
        tk = T.pw(T.S(tj.name), N(k)) if k != 1 else T.S(tj.name)
        expr = T.plus(expr, T.times(bt, tk))
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
                _ts(de.ws[j]),
            )
        )
    return expr


def _risch_rec(fa, fd, de, j):
    """在第 j 层积分 fa/fd（Poly(levels[:j+1])）——递归塔核心。

    商/真分式分离后按 case 分派：primitive 多项式走 limited 循环，
    exp 多项式走频率 RDE；真分式共用 Hermite+residue（泛型）；
    leftover 按 case 回本层多项式循环（primitive，deg 严格降）或
    低层递归积分（exp 的 k=0 分量）。
    """
    from cas.ratfunc import RatFunc
    from cas.integrate import integrate_rational

    sub = tuple(de.levels[:j])
    zero = RatFunc.zero(sub)
    tj = de.levels[j]
    case = de.cases[j]

    A = _univar(fa, tj)
    D = _univar(fd, tj)
    if _u_is_zero(A):
        return T.ZERO

    dq = len(D) - 1
    dp = len(A) - 1
    if dp >= dq:
        Q, R = _u_divmod(A, D, zero)
    else:
        Q, R = [], A

    expr = T.ZERO
    if case == "primitive":
        for bk, k in _primitive_poly_part(Q, de, j):
            bt = bk.to_term()   # 塔符号形态
            tk = T.pw(T.S(tj.name), N(k)) if k != 1 else T.S(tj.name)
            expr = T.plus(expr, T.times(bt, tk))
        res, negf, st = (None, None, None, None), {}, "ok"
        if not _u_is_zero(R):
            res, negf, st = _integrate_proper(R, D, de, j, zero)
    else:
        freqs = {k: c for k, c in enumerate(Q) if not c.is_zero()}
        res, negf, st = (None, None, None, None), {}, "ok"
        if not _u_is_zero(R):
            res, negf, st = _integrate_proper(R, D, de, j, zero)
        for k, v in negf.items():
            freqs[k] = freqs[k] + v if k in freqs else v
        expr = T.plus(expr, _exp_freq_part(freqs, de, j))

    rat_part, logs, nonel, leftover = res
    expr = T.plus(expr, assemble_exp_result(rat_part, logs, nonel, de, j))

    if leftover is not None and any(not c.is_zero() for c in leftover):
        lf = _u_trim(list(leftover))
        if case == "primitive":
            # θ-多项式剩余：回本层多项式积分（deg 严格降，终止）
            fn, fdd = _from_univar(lf, de.vars, tj)
            expr = T.plus(expr, _risch_rec(fn, fdd, de, j))
        else:
            # exp：ℚ 常数剩余（非常数系数已在频率分量中）
            cv = Fr(0)
            for c in lf:
                if not c.is_zero():
                    cv += c.const_val()
            if cv != 0:
                xv = de.levels[0]
                val, ok, _m = integrate_rational(Poly.const((xv,), cv),
                                                 Poly.one((xv,)), xv)
                if not ok:
                    raise RischUnsupported("leftover rational integration failed")
                expr = T.plus(expr, val)
    return expr

