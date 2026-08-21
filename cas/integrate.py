"""有理函数不定积分：Hermite 分解 + 对数部分（线性闭式 / RootOf）+ 符号验证通道。"""

from fractions import Fraction as Fr

from cas.errors import PolyError
from cas.poly import Poly, SymRat, ugcd
from cas.apart import apart
from cas.algnum import RootOf, qa_div, qa_mul, qa_inv, tr_power_sums, tr_eval, coefs
from cas.simplify import simplify
from cas.pprint import to_str
from cas import term as T
from cas.term import S, N, Sym


def _coef_term(c):
    """Fr/SymRat 系数 -> term（N 只收数值；参数系数转有理函数项）。"""
    if isinstance(c, SymRat):
        return c.to_term()
    return N(c)


def _frac(t, x):
    """term 有理式 → (P, Q)（递归通分，未约分）。"""
    if isinstance(t, T.Expr):
        n = t.head.name
        if n == "Times":
            acc = (Poly.one((x,)), Poly.one((x,)))
            for a in t.args:
                pa, qa = _frac(a, x)
                acc = (acc[0] * pa, acc[1] * qa)
            return acc
        if n == "Plus":
            acc = (Poly.zero((x,)), Poly.one((x,)))
            for a in t.args:
                pa, qa = _frac(a, x)
                acc = (acc[0] * qa + pa * acc[1], acc[1] * qa)
            return acc
        if n == "Power":
            b, e = t.args
            pb, qb = _frac(b, x)
            if not isinstance(e, T.Int):
                raise PolyError("non-integer power")
            if e.v >= 0:
                return (pb ** e.v, qb ** e.v)
            return (qb ** (-e.v), pb ** (-e.v))
    return Poly.from_term(t, (x,)), Poly.one((x,))


def _rat_pair(t, x):
    """term 有理函数 -> (P, Q)，约分。"""
    num, den = _frac(t, x)
    g = ugcd(num, den)
    if not g.is_zero():
        num = num.udivmod(g)[0]
        den = den.udivmod(g)[0]
    return num, den


def _qa_to_term(c, beta):
    parts = []
    for k, v in c.monos.items():
        r = k[0]
        b = beta.to_term()
        if r == 0:
            parts.append(_coef_term(v))
        elif r == 1:
            parts.append(T.times(_coef_term(v), b))
        else:
            parts.append(T.times(_coef_term(v), T.pw(b, N(r))))
    if not parts:
        return N(Fr(0))
    if len(parts) == 1:
        return parts[0]
    return T.mk(S("Plus"), tuple(parts))


def _hermitte_power(a, p, k, x):
    """∫ a/p^k（p 不可约，deg a < k·deg p）→ (有理项列表, a1, k1)：
    ∫ = Σ u_i/p^{k-i} + ∫ a1/p^{k1}，k1 递减至 1。
    递推：∫ a/p^k = u/p^{k-1} + ∫ v/p^{k-1}，
    u ≡ -a·inv(p')/(k-1) (mod p)，v = (a + (k-1)·u·p')/p - u'。"""
    terms = []
    while k >= 2:
        pp = p.deriv(x)
        r = a.udivmod(p)[1]
        u = qa_mul(r, qa_inv(pp, p), p).scalar(Fr(-1) / (k - 1))
        u = u.udivmod(p)[1]
        v = (a + u.scalar(k - 1) * pp).udivmod(p)[0] - u.deriv(x)
        terms.append((u, p, k - 1))
        a, k = v, k - 1
    return terms, a, k


def _classify_discriminant(D):
    """参数判别式（SymRat）符号分类：pos / neg / unknown。

    decide 区间通道判 D>0 / D<0（平方和+常数等结构显然情形可判；
    自由符号一般情形诚实返回 unknown）。
    """
    from cas.decide import decide, T3
    from cas.context import Context

    ctx = Context()
    Dt = D.to_term()
    if decide(T.mk(S("Gt"), (Dt, T.ZERO)), ctx) is T3.YES:
        return "pos"
    if decide(T.mk(S("Lt"), (Dt, T.ZERO)), ctx) is T3.YES:
        return "neg"
    return "unknown"


def _log_terms(f, p, x):
    """∫ f/p（p 不可约，deg f < deg p）→ 对数/反正切项列表：
    ('lin', c, p)：c·ln(p)；('atan', f, p, pc, D)：二次负判别式实形式；
    ('root', C, p, n)：Σ C(β_j)·ln(x − β_j)。"""
    n = p.degree(x)
    if n == 1:
        lc = p.lc(x)
        if lc != 1:
            p = p.scalar(Fr(1) / lc)
        return [("lin", f.const_val() / lc, p)]
    if n == 2:
        # 实形式（判别式有理可判）：x²+pc·x+q 且 D=4q−pc²>0 时
        # ∫(Ax+B)/p = (A/2)ln(p) + (2B−A·pc)/√D · atan((2x+pc)/√D)
        lc = p.lc(x)
        pm = p.scalar(Fr(1) / lc) if lc != 1 else p
        fm = f.scalar(Fr(1) / lc) if lc != 1 else f
        pc = pm.monos.get((1,), Fr(0))
        qc = pm.monos.get((0,), Fr(0))
        D = 4 * qc - pc * pc   # Fr 或 SymRat
        if isinstance(D, SymRat):
            # 参数判别式：符号分类（pos/neg/unknown）。
            # pos (D>0 恒正)  → atan 实形式（√D 实）
            # neg (D<0 恒负)  → ln 差实形式（√(-D) 实，避免复 atan）
            # unknown (符号不定) → atan 通用形式 + proviso [D≠0]
            # （atan 公式对 D≠0 任何符号成立：复对数主值组合，符号验证背书）
            # D ≡ 0 为重根（平方自由分解已排除），防御性拒答。
            if D.is_zero():
                raise PolyError("parameter discriminant is identically zero")
            sign = _classify_discriminant(D)
            return [("atan", fm, pm, pc, D, sign)]
        if D > 0:
            return [("atan", fm, pm, pc, D, "pos")]
    fp = p.deriv(x)
    C = qa_div(f, fp, p)
    return [("root", C, p, n)]


def _integrate_poly(p, x):
    out = Poly.zero((x,))
    for k, v in p.monos.items():
        e = k[0]
        out = out + Poly((x,), {(e + 1,): v / (e + 1)})
    return out


def _exact_sqrt_term(D):
    """非负有理数 D 的精确平方根项：完全平方折叠为有理数，否则 √D 名词。

    参数判别式（SymRat）保持 √(参数式) 名词（符号验证仍背书 atan 形式）。
    """
    import math

    if isinstance(D, SymRat):
        return T.sqrt(D.to_term())
    f = Fr(D)
    rn = math.isqrt(f.numerator)
    rd = math.isqrt(f.denominator)
    if rn * rn == f.numerator and rd * rd == f.denominator:
        return N(Fr(rn, rd))
    return T.sqrt(N(D))


def _assemble(poly_int, rat_terms, lin_logs, root_logs, x):
    parts = []
    if not poly_int.is_zero():
        parts.append(poly_int.to_term())
    for u, p, kk in rat_terms:
        parts.append(T.div(u.to_term(), T.pw(p.to_term(), N(kk))))
    for lg in lin_logs:
        if lg[0] == "atan":
            _lg, fm, pm, pc, D, sign = lg
            A = fm.monos.get((1,), Fr(0))
            B = fm.monos.get((0,), Fr(0))
            if sign == "neg":
                # D<0 恒负：ln 差实形式 √(-D) 实（避免复 atan）
                # ∫(Ax+B)/p = (A/2)ln(p) + (2B-A·pc)/(2√(-D))·[ln(2x+pc-√(-D)) - ln(2x+pc+√(-D))]
                sd = _exact_sqrt_term(-D)   # √(-D) 名词
                if A != 0:
                    parts.append(T.times(_coef_term(A / 2), T.log(pm.to_term())))
                k = 2 * B - A * pc
                if k != 0:
                    w = T.plus(T.times(N(2), x), _coef_term(pc))
                    half_k = k / 2
                    parts.append(T.times(_coef_term(half_k), T.pw(sd, T.MONE),
                                        T.log(T.plus(w, T.neg(sd)))))
                    parts.append(T.times(_coef_term(-half_k), T.pw(sd, T.MONE),
                                        T.log(T.plus(w, sd))))
            else:
                # pos (D>0) / unknown (符号不定)：atan 通用形式
                sd = _exact_sqrt_term(D)   # 完全平方折叠为有理数，否则保留 √D 名词
                if A != 0:
                    parts.append(T.times(_coef_term(A / 2), T.log(pm.to_term())))
                k = 2 * B - A * pc
                if k != 0:
                    arg = T.div(T.plus(T.times(N(2), x), _coef_term(pc)), sd)
                    parts.append(T.times(_coef_term(k), T.pw(sd, T.MONE), T.atan(arg)))
            continue
        c, p = lg[1], lg[2]
        parts.append(T.times(_coef_term(c), T.log(p.to_term())))
    for C, p, n in root_logs:
        for j in range(1, n + 1):
            beta = RootOf(p, j)
            c_term = _qa_to_term(C, beta)
            u = T.plus(x, T.neg(beta.to_term()))
            parts.append(T.times(c_term, T.log(u)))
    if not parts:
        return T.ZERO
    if len(parts) == 1:
        return parts[0]
    return T.mk(S("Plus"), tuple(parts))


def _verify(poly_int, rat_terms, lin_logs, root_logs, P, Q, x):
    """符号验证：D(Σ 项) == P/Q（精确 ℚ 运算）。"""
    num = poly_int.deriv(x)
    den = Poly.one((x,))
    for u, p, m in rat_terms:
        n2 = u.deriv(x) * p - u * p.deriv(x).scalar(m)
        d2 = p ** (m + 1)
        num, den = num * d2 + n2 * den, den * d2
    for lg in lin_logs:
        if lg[0] == "atan":
            # d(atan 实形式 / ln 差实形式) = f/p 恒等（代数验证：√D 或 √(-D)
            # 系数恰消去），贡献与 f/p 通分同形——sign 不影响验证等式。
            _tg, fm, pm, _pc, _D, _sign = lg
            num, den = num * pm + fm * den, den * pm
            continue
        c, p = lg[1], lg[2]
        num, den = num * p + den * p.deriv(x).scalar(c), den * p
    for C, p, n in root_logs:
        deg = p.degree(x)
        cs = coefs(p, x)
        trCb = [tr_eval(p, C, t) for t in range(deg)]
        nco = {}
        for r in range(deg):
            acc = Fr(0)
            for t in range(r + 1):
                e_rt = (-1) ** (r - t) * cs[r - t]
                acc += (-1) ** t * e_rt * trCb[t]
            if acc != 0:
                nco[(deg - 1 - r,)] = (-1) ** r * acc
        Np = Poly((x,), nco)
        num, den = num * p + Np * den, den * p
    return (num * Q).monos == (P * den).monos


def integrate_rational(P, Q, x):
    """∫ P/Q dx → (term, verified, provisos)。P, Q 单变量，Q 非零。"""
    q_poly, r = P.udivmod(Q)
    poly_int = _integrate_poly(q_poly, x)
    rat_terms = []
    lin_logs = []
    root_logs = []
    _, terms = apart(r, Q)
    for nn, dd, k in terms:
        if dd.degree(x) == 1:
            lc = dd.lc(x)
            c = nn.const_val()
            if k == 1:
                lin_logs.append(("lin", c / lc, dd.scalar(Fr(1) / lc)))
            else:
                rat_terms.append((Poly.const((x,), c / ((1 - k) * lc)), dd, k - 1))
        else:
            herm, f1, k1 = _hermitte_power(nn, dd, k, x)
            rat_terms.extend(herm)
            for lg in _log_terms(f1, dd, x):
                if lg[0] in ("lin", "atan"):
                    lin_logs.append(lg)
                else:
                    root_logs.append((lg[1], lg[2], lg[3]))
    term = _assemble(poly_int, rat_terms, lin_logs, root_logs, x)
    verified = _verify(poly_int, rat_terms, lin_logs, root_logs, P, Q, x)
    # 参数判别式符号不定（unknown）的 atan 项：atan 公式仅在 D≠0 成立，
    # 平方自由分解已排除重根，但 D 作为参数式可能取 0 → 输出 proviso [D≠0]。
    provisos = []
    for lg in lin_logs:
        if lg[0] == "atan" and lg[5] == "unknown":
            Dt = lg[4].to_term()
            prov = T.mk(S("Ne"), (Dt, T.ZERO))
            if prov not in provisos:
                provisos.append(prov)
    return term, verified, provisos


_USUB_DEPTH = [0]   # 换元递归深度守卫（模块级，integrate 链共享）


def _term_size(t):
    """节点数（换元候选排序用；显式栈不递归）。"""
    n = 0
    stack = [t]
    while stack:
        u = stack.pop()
        n += 1
        if isinstance(u, T.Expr):
            stack.extend(u.args)
        elif isinstance(u, T.Bound):
            stack.append(u.body)
    return n


def _try_usub(t, x):
    """自动正向换元：t = h(g(x))·g'(x) -> ∫h(u)du 代回 u=g(x)。

    代回用 g 本身，不需逆函数（与定积分正向换元同源）。探测与 defint_auto 同款：
    g' 整除 t（负幂拍平助消去）且商仅为 g 的函数。返回
    (F, ok, g, h, H)；无可行候选返 None。裸符号候选殿后（平凡换元）。
    """
    from cas.diff import d
    from cas.simplify import expand

    cands = []
    fallback = []
    for p in T.all_paths(t):
        try:
            g = T.term_at(t, p)
        except IndexError:
            continue
        if not isinstance(g, T.Expr) or g is t or g is x or x not in T.free_vars(g):
            continue
        (fallback if isinstance(g, Sym) else cands).append(g)
    # 候选按项大小升序：优先内层自然换元（u=x² 优于 u=eˣ²），全候选仍会试遍
    cands.sort(key=_term_size)
    for idx, g in enumerate((cands + fallback)[:24]):
        gp = d(g, x)
        # 商先拍平负幂复合底（mk 不对复合底做 t·t⁻¹ 消去），否则整除验证失效
        q = simplify(_flatten_inv(simplify(T.div(t, gp))))
        if simplify(expand(T.plus(T.times(gp, q), T.neg(t)))) is not T.ZERO:
            continue
        # 每候选新鲜哑元：free_vars 检查与回代往返双重验证“商仅为 g 的函数”
        # （复用固定哑元会被 g 自身含该符号绕过，产出错误原函数）
        z = T.S(f"_usub_z{idx}")
        h = T.subst(q, {g: z})
        if x in T.free_vars(h):
            continue
        if simplify(T.subst(h, {z: g})) is not q:
            continue
        try:
            H, _ok_inner, _m, _prov = integrate(h, z)
        except PolyError:
            continue
        F = T.subst(H, {z: g})
        # 换元是启发式探测：每候选微分回验，未验证继续试下一候选（永不静默错）
        from cas.diff import verify as _verify

        if _verify(F, x, t) != "VERIFIED":
            continue
        return F, True, g, h, H
    return None


def integrate(t, x):
    """∫ t dx（t 为 term，x 为 Sym）→ (term, verified, method, provisos)。

    裸 spec 函数走 anti 表（连续原函数，定积分友好）；
    正向复合 t = h(g(x))·g'(x) 走自动换元（代回不需逆函数）；
    有理函数走 Hermite+RootOf；sin x/cos x 有理式走 t=tan(x/2) 代换。
    method 供策略通道可解释输出（REPL/step log）；provisos 为参数情形的条件声明。
    """
    F0 = _spec_antideriv(t, x)
    if F0 is not None:
        from cas.diff import verify as _verify

        ok = _verify(F0, x, t) == "VERIFIED"
        return F0, ok, "spec antiderivative table", []
    # 三角多项式：多角度基线性化后逐项积分（连续原函数，无 tan-half 分支切）。
    # sin^2 -> (1-cos(2x))/2 类；线性组合经 spec anti 表（含线性复合）逐项原函数。
    tl = _trig_linear_integrand(t, x)
    if tl is not None:
        terms_ = []
        for c, g in tl:
            if g is T.ONE:
                G = x
            else:
                G = _spec_antideriv(g, x)
                if G is None:
                    break
            terms_.append(T.times(c, G))
        else:
            from cas.diff import verify as _verify

            F0 = simplify(T.mk(S("Plus"), tuple(terms_)))
            ok = _verify(F0, x, t) == "VERIFIED"
            return F0, ok, "trig poly: multi-angle linearization + termwise table", []
    if _USUB_DEPTH[0] < 3:
        _USUB_DEPTH[0] += 1
        try:
            us = _try_usub(t, x)
        finally:
            _USUB_DEPTH[0] -= 1
        if us is not None:
            F, ok, g, _h, _H = us
            return F, ok, f"u-substitution u={to_str(g)}", []
    try:
        P, Q = _rat_pair(t, x)
        term, ok, provisos = integrate_rational(P, Q, x)
        return term, ok, "Hermite reduction + RootOf log part", provisos
    except PolyError:
        res = _trig_tan_half(t, x)
        if res is None:
            raise PolyError("unsupported integrand")
        return res[0], res[1], "t = tan(x/2) substitution -> rational integration", res[2]


def _trig_linear_integrand(t, x):
    """三角多项式判定 + 线性化：t 经 trig_reduce 化为 Σ c·f(kx)
    （f ∈ {Sin, Cos, 1}）时返回 [(c, f-term)]，否则 None。

    消费 spec anti 表逐项积分得连续原函数——替代 tan-half 在多项式
    情形的分支切问题（sin^2 的 tan-half 原函数在 x=(2k+1)pi 跳变，
    跨越区间的 NL 代限值错误）。
    """
    from cas.trig import trig_reduce

    try:
        rt = trig_reduce(t, x)
    except Exception:
        return None
    if rt is None:
        return None

    def parts(u, acc):
        if isinstance(u, T.Expr) and u.head.name == "Plus":
            return all(parts(a, acc) for a in u.args)
        if T.is_num(u):
            acc.append((u, T.ONE))
            return True
        if isinstance(u, T.Expr) and u.head.name in ("Sin", "Cos") \
                and len(u.args) == 1:
            acc.append((T.ONE, u))
            return True
        if isinstance(u, T.Expr) and u.head.name == "Times" and len(u.args) == 2:
            a_, b_ = u.args
            if T.is_num(b_):
                a_, b_ = b_, a_
            if T.is_num(a_) and isinstance(b_, T.Expr) \
                    and b_.head.name in ("Sin", "Cos") and len(b_.args) == 1:
                acc.append((a_, b_))
                return True
        return False

    acc = []
    if not parts(rt, acc):
        return None
    return acc


def _spec_antideriv(t, x):
    """裸 spec 函数（参数恰为 x）或其线性复合 f(a·x+b) -> 简单原函数。

    线性复合：d/dx anti(a x+b) = f(a x+b)·a，故 ∫f(a x+b) = anti(a x+b)/a。
    """
    from cas import spec as _spec
    from cas.solve import _linear_split

    if not isinstance(t, T.Expr) or len(t.args) != 1:
        return None
    sp = _spec.get(t.head.name)
    if sp is None or sp.anti is None:
        return None
    arg = t.args[0]
    if arg is x:
        return sp.anti(x)
    split = _linear_split(arg, x)
    if split is None:
        return None   # 非线性复合（如 exp(-x^2)）：spec 线性反导表不覆盖
    a_, b_ = split
    if not T.is_num(a_) or T.num_val(a_) == 0 or not T.is_num(b_):
        return None
    if x not in T.free_vars(arg):
        return None
    return T.div(sp.anti(arg), T.N(T.num_val(a_)))


def _trig_check(t, x):
    """t 是否为 sin x / cos x 的有理式（无裸 x、无其他函数头）。"""
    if isinstance(t, T.Expr):
        n = t.head.name
        if n in ("Sin", "Cos"):
            return len(t.args) == 1 and t.args[0] is x
        if n in ("Plus", "Times"):
            return all(_trig_check(a, x) for a in t.args)
        if n == "Power":
            b, e = t.args
            return isinstance(e, T.Int) and _trig_check(b, x)
        return False
    if T.is_num(t):
        return True
    return False


def _trig_sub(t, x, tv):
    """sin x → 2t/(1+t²)，cos x → (1−t²)/(1+t²)。"""
    if isinstance(t, T.Expr):
        n = t.head.name
        if n == "Sin":
            return T.div(T.times(N(2), tv), T.plus(N(1), T.pw(tv, N(2))))
        if n == "Cos":
            return T.div(T.plus(N(1), T.neg(T.pw(tv, N(2)))), T.plus(N(1), T.pw(tv, N(2))))
        if n in ("Plus", "Times", "Power"):
            return T.mk(S(n), tuple(_trig_sub(a, x, tv) for a in t.args))
    return t


def _trig_tan_half(t, x):
    """∫ R(sin x, cos x) dx：t = tan(x/2) 代换 -> M1 有理积分 -> 代回。"""
    if not _trig_check(t, x):
        return None
    tv = S("t")
    w = _trig_sub(t, x, tv)
    w = T.times(w, T.div(N(2), T.plus(N(1), T.pw(tv, N(2)))))
    try:
        P, Q = _rat_pair(w, tv)
    except PolyError:
        return None
    G, ok, provisos = integrate_rational(P, Q, tv)
    F = T.subst(G, {tv: T.tan(T.div(x, N(2)))})
    return F, ok, provisos


# ---------------------------------------------------------------------------
# 定积分（M3）：Newton-Leibniz + 奇点拆分 + 端点极限 + 数值采样交叉核对
# ---------------------------------------------------------------------------


def _parity_normalize(t):
    """按 spec.parity 声明折叠函数参数负号：f(-x) -> f(x)（even）/ -f(x)（odd）。

    奇偶规则在 auto 通道，普通 simplify 不应用；对称性预检需要显式的
    声明式消费（读 spec 注册表，非函数清单硬编码）。
    """
    from cas import spec as _spec

    if not isinstance(t, T.Expr):
        return t
    args = tuple(_parity_normalize(a) for a in t.args)
    tt = t if all(a is b for a, b in zip(args, t.args)) else T.mk(t.head, args)
    sp = _spec.get(t.head.name)
    if sp is not None and sp.parity and len(args) == 1:
        u = args[0]
        if isinstance(u, T.Expr) and u.head.name == "Times" and T.MONE in u.args:
            rest = T.mk(T.S("Times"), tuple(a for a in u.args if a is not T.MONE))
            inner = T.mk(t.head, (rest,))
            return T.neg(inner) if sp.parity == "odd" else inner
    return tt


def _defint_reflect(t, x, lo, hi, lo_f, hi_f):
    """反射对称（任意区间，关于中点 m=(lo+hi)/2）：phi(x) = lo+hi-x。

    f(phi(x)) == -f(x)（关于 m 奇）-> I = 0；
    f(phi(x)) == f(x)（关于 m 偶）-> I = 2*∫_start^m（内层 _no_sym：
    常数等函数关于任意中点都偶，无旗标会无限折半直至空区间截断出错值）。
    [-a,a] 只是 lo+hi=0 的实例；关系判定走 equivalent 管线且要求严格 YES
    （采样 PROBABLE 不触发——对称归零是强断言）。返回 None = 不适用。
    """
    from cas.decide import equivalent, T3

    phi = simplify(T.plus(T.plus(lo, hi), T.neg(x)))
    refl = _parity_normalize(simplify(T.subst(t, {x: phi})))
    if equivalent(refl, T.neg(t)) is T3.YES:
        return T.ZERO, "VERIFIED", "odd about interval midpoint (reflection)"
    if equivalent(refl, t) is T3.YES:
        mid = simplify(T.div(T.plus(lo, hi), N(2)))
        start = lo if hi_f >= lo_f else hi
        v, st, note = defint(t, x, start, mid, _no_sym=True)
        if v is None:
            return None
        val = simplify(T.times(N(2), v))
        if hi_f < lo_f:
            val = T.neg(val)
        return val, st, "even about interval midpoint: 2*" + note
    return None


def _period_candidates(t):
    """周期候选：t 中出现的 spec.period 函数头（去重，声明原样）。"""
    from cas import spec as _spec

    out = []
    for p in T.all_paths(t):
        u = T.term_at(t, p)
        if isinstance(u, T.Expr) and len(u.args) == 1:
            sp = _spec.get(u.head.name)
            if sp is not None and sp.period is not None \
                    and all(h != u.head.name for h, _ in out):
                out.append((u.head.name, sp.period))
    return out


def _absorb_shift(t, P):
    """周期偏移吸收：h(w+P) -> h(w)（h 声明周期恰为 P）。

    声明即定理（spec.period 与 deriv/anti 同信任级）：h 的参数顶层加法
    边缘含 +P 时可剥离——仅限参数顶层（Sin((x+P)^2) 不吸收，平方内偏移
    不可消）。其余结构原样重建；成败由调用方指针比对裁决（残余 +P 必然
    不等）。非周期因子（裸 x 等）因此自然拒绝折叠。
    """
    from cas import spec as _spec

    if not isinstance(t, T.Expr):
        return t
    sp = _spec.get(t.head.name)
    if sp is not None and sp.period is not None and len(t.args) == 1 \
            and str(sp.period) == str(P):
        u = t.args[0]
        if isinstance(u, T.Expr) and u.head.name == "Plus":
            args = list(u.args)
            for i, a in enumerate(args):
                if a is P:
                    del args[i]
                    w = T.mk(T.S("Plus"), tuple(args)) if len(args) > 1 else args[0]
                    return T.mk(t.head, (w,))
        return t   # 参数顶层无 +P：原样保留（残余由指针比对裁决）
    return T.mk(t.head, tuple(_absorb_shift(a, P) for a in t.args))


def _defint_period_fold(t, x, lo, hi, lo_f, hi_f):
    """周期折叠：spec.period 声明供候选、偏移吸收做结构证明。

    f(x+P) 经逐头吸收后指针还原 f(x)（驻留 O(1) 比对）且区间长为
    P 的正整数倍 n 时，I = n*∫_start^{start+P}（直接折到单周期，
    单周期内部照常走 NL+交叉核对，无递归风险）。
    返回 None = 不适用。
    """
    from cas.evalnum import eval_approx

    span = abs(hi_f - lo_f)
    for _head, P in _period_candidates(t):
        shifted = T.subst(t, {x: T.plus(x, P)})
        if _absorb_shift(shifted, P) is not t:
            continue
        try:
            pf = eval_approx(P, {})
        except Exception:
            continue
        if pf is None or pf <= 0:
            continue
        n = int(round(span / pf))
        if n < 2 or abs(span - n * pf) > 1e-9 * max(1.0, span):
            continue
        start = lo if hi_f >= lo_f else hi
        # 折到单周期（内层 span=P -> 不再触发折叠，无递归）
        end = simplify(T.plus(start, P))
        v, st, note = defint(t, x, start, end)
        if v is None:
            return None
        val = simplify(T.times(N(n), v))
        if hi_f < lo_f:
            val = T.neg(val)
        return val, st, f"period fold ({n} periods): " + note
    return None


def defint(t, x, lo, hi, _no_sym=False):
    """∫_lo^hi t dx -> (值项 | None, 状态, 方法/原因说明)。

    状态：VERIFIED / UNVERIFIED（原函数验证态区分）/ DIVERGES / UNKNOWN / unsupported。
    管线：不定积分 -> dom_condition 定奇点（有理根精确；无理根位置不可判则拒答）
    -> 拆区间 -> 单侧极限求值（发散即 DIVERGES）-> 数值采样交叉核对（永不静默错）。
    支持：Piecewise 被积函数（分支点拆分 + 中点选支）；±∞ 限反常积分（判敛）。
    """
    from cas.limits import limit as _limit
    from cas.evalnum import eval_approx, EvalNumError
    from cas.simplify import simplify

    if isinstance(t, T.Expr) and t.head.name == "Piecewise" and len(t.args) % 2 == 0:
        return _defint_piecewise(t, x, lo, hi)
    if _is_inf(lo) or _is_inf(hi):
        # 方向健全性：lo 只可 -∞，hi 只可 +∞（反序翻转留给有限限路径）
        if (_is_inf(lo) and not _is_neg_inf(lo)) or (_is_inf(hi) and not _is_pos_inf(hi)):
            return None, "unsupported", "invalid infinite bound orientation"
        return _defint_improper(t, x, lo, hi)
    try:
        lo_f = eval_approx(lo, {})
        hi_f = eval_approx(hi, {})
    except EvalNumError:
        return None, "unsupported", "bounds not numerically comparable"
    if abs(hi_f - lo_f) < 1e-12:
        return T.ZERO, "VERIFIED", "empty interval"
    # 区间自同构对称预检（通用框架，非特判清单；[-a,a] 只是中点反射的实例）：
    # 反射 phi=lo+hi-x 的奇/偶关系 + spec.period 周期折叠。关系判定全部走
    # equivalent 管线（严格 YES），声明只供候选不充当证明。
    if not _no_sym:
        sym = _defint_reflect(t, x, lo, hi, lo_f, hi_f)
        if sym is not None:
            return sym
        fold = _defint_period_fold(t, x, lo, hi, lo_f, hi_f)
        if fold is not None:
            return fold
    sign = 1
    if hi_f < lo_f:
        lo, hi = hi, lo
        lo_f, hi_f = hi_f, lo_f
        sign = -1
    try:
        F, ok, _method, _prov = integrate(t, x)
    except PolyError:
        return None, "unsupported", "no antiderivative method"
    if F is None:
        # 无初等原函数（如 exp(-x^2)）：诚实拒答，绝不解包崩溃（永不静默错）
        return None, "unsupported", "no antiderivative method"
    splits = _sing_points(t, x, lo_f, hi_f)
    if splits is None:
        return None, "UNKNOWN", "singularity locations undecidable"
    pts = [lo] + [N(Fr(s)) for s in splits] + [hi]
    pts_f = [lo_f] + [float(s) for s in splits] + [hi_f]
    acc = T.ZERO
    for i in range(len(pts) - 1):
        ll = _limit(F, x, pts[i], "+")
        lr = _limit(F, x, pts[i + 1], "-")
        if ll is None or lr is None:
            return None, "UNKNOWN", f"endpoint limit undecidable"
        if _is_inf(ll) or _is_inf(lr):
            return None, "DIVERGES", f"improper integral diverges at segment {i}"
        acc = T.plus(acc, lr, T.neg(ll))
    val = simplify(acc)
    cross = _numeric_cross(t, x, pts_f, acc)   # 核对用正向区间值（翻转前）
    if sign < 0:
        val = T.neg(val)
    if cross is False:
        return None, "UNKNOWN", "numeric cross-check mismatch (result withheld)"
    status = "VERIFIED" if ok else "UNVERIFIED"
    note = "Newton-Leibniz + singularity split + endpoint limits"
    return val, status, note


def _flatten_inv(t):
    """Power(Times, 负整数) -> 因子逆之积（generic 语义，同构造器 x·x⁻¹->1）。

    拍平后 mk 的同底幂合并才能完成消去（mk 不对复合底做 t·t⁻¹ 消去）。
    """
    if isinstance(t, T.Expr):
        name = t.head.name
        if name == "Power":
            b, e = t.args
            b2 = _flatten_inv(b)
            if isinstance(e, T.Int) and e.v < 0 and isinstance(b2, T.Expr) and b2.head.name == "Times":
                parts = tuple(_flatten_inv(T.pw(f, e)) for f in b2.args)
                return T.mk(T.S("Times"), parts)
            return T.pw(b2, e) if b2 is not b else t
        args = tuple(_flatten_inv(a) for a in t.args)
        if all(a is b for a, b in zip(args, t.args)):
            return t
        return T.mk(t.head, args)
    return t


def defint_auto(t, x, lo, hi, _depth=0):
    """定积分（自动正向换元探测）：被积函数 = h(g(x))·g'(x) 时取 u=g(x)，
    新限 = g(lo)、g(hi) 正向求值（全程不求逆）；探测失败回退普通 defint。
    候选序：裸符号最后试（平凡换元留给嵌套递归兑底）；深度限 3 防递归环。"""
    from cas.diff import d

    if _depth >= 3:
        return defint(t, x, lo, hi)
    if _is_inf(lo) or _is_inf(hi):
        return defint(t, x, lo, hi)   # 无穷限直走反常积分管线（新限正向求值不适用）

    cands = []
    fallback = []
    for p in T.all_paths(t):
        try:
            g = T.term_at(t, p)
        except IndexError:
            continue
        if not isinstance(g, T.Expr) or g is t or g is x or x not in T.free_vars(g):
            continue
        (fallback if isinstance(g, Sym) else cands).append(g)
    cands.sort(key=_term_size)   # 优先内层自然换元（与 _try_usub 同款序）
    for g in (cands + fallback)[:24]:
        gp = d(g, x)
        # 商：负幂拍平后 mk 同底幂合并完成消去；整除与否由后续“h 不含 x”+
        # defint 内部梯形法交叉核对双重把关（错换元必被核对扣留，永不静默错）
        q = simplify(_flatten_inv(T.div(t, gp)))
        z = T.S("_usub_z")
        h = T.subst(q, {g: z})   # e^a 已由构造器规范为 Exp，替换自然命中
        if x in T.free_vars(h):
            continue   # 商仍含 x：不是 g 的函数，换元不成立
        new_lo = simplify(T.subst(g, {x: lo}))
        new_hi = simplify(T.subst(g, {x: hi}))
        val, st, note = defint_auto(h, z, new_lo, new_hi, _depth + 1)   # 递归支持嵌套换元
        if val is not None:
            tag = "u-substitution u=" + to_str(g)
            note = tag if note.startswith("Newton-Leibniz") else f"{tag} -> {note}"
            return val, st, note
    return defint(t, x, lo, hi)


def _is_inf(v):
    if v is T.INFINITY:
        return True
    return isinstance(v, T.Expr) and T.INFINITY in v.args


def _is_pos_inf(v):
    return v is T.INFINITY


def _is_neg_inf(v):
    # Times 规范序下 Special 排前（Infinity * -1），判定与顺序无关
    return (isinstance(v, T.Expr) and v.head.name == "Times" and len(v.args) == 2
            and T.INFINITY in v.args and T.MONE in v.args)


def _sing_points_half(t, x, a_f, right):
    """半直线 (a, +∞)（right=True）或 (-∞, a) 上的奇点（精确有理根）；
    无理根位置不可判 -> None（诚实拒答）。"""
    from cas.domain import dom_condition
    from cas.simplify import expand
    from cas.factor import factor
    from cas.sturm import isolate_real_roots

    pts = set()
    for c in dom_condition(t):
        if not (isinstance(c, T.Expr) and c.head.name in ("Ne", "Gt", "Ge")):
            continue
        b = c.args[0]
        if x not in T.free_vars(b):
            continue
        try:
            p = Poly.from_term(expand(b), (x,))
        except PolyError:
            return None
        if p.degree(x) <= 0:
            continue
        _cst, facs = factor(p)
        for g, _mult in facs:
            if g.degree(x) == 1:
                r = -g.const_val() / g.lc(x)
                if (right and float(r) > a_f) or ((not right) and float(r) < a_f):
                    pts.add(r)
            else:
                for a_, b_ in isolate_real_roots(g):
                    if (right and float(b_) > a_f) or ((not right) and float(a_) < a_f):
                        return None
    return sorted(pts)


def _defint_improper(t, x, lo, hi):
    """±∞ 限反常积分：原函数 + 无穷端极限（有限即收敛，判敛由此而来）。

    双端无穷在 0 处拆为两个单端反常积分。无穷区间不做梯形法核对
    （有限截断无普遍意义），状态依原函数验证态，note 明言。
    """
    from cas.limits import limit as _limit
    from cas.evalnum import eval_approx, EvalNumError

    if _is_inf(lo) and _is_inf(hi):
        v1, s1, n1 = _defint_improper(t, x, lo, N(0))
        v2, s2, n2 = _defint_improper(t, x, N(0), hi)
        if v1 is None:
            return None, s1, "split at 0: " + n1
        if v2 is None:
            return None, s2, "split at 0: " + n2
        st = s1 if s1 == s2 else "UNVERIFIED"
        return T.plus(v1, v2), st, "improper both ends, split at 0"
    try:
        F, ok, _method, _prov = integrate(t, x)
    except PolyError:
        return None, "unsupported", "no antiderivative method"
    if F is None:
        # 无初等原函数（如 exp(-x^2)）：诚实拒答，绝不解包崩溃（永不静默错）
        return None, "unsupported", "no antiderivative method"
    right = _is_pos_inf(hi)
    fin = lo if right else hi
    try:
        fin_f = eval_approx(fin, {})
    except EvalNumError:
        return None, "unsupported", "finite bound not numerically evaluable"
    splits = _sing_points_half(t, x, fin_f, right)
    if splits is None:
        return None, "UNKNOWN", "singularity locations undecidable on half-line"
    # 段链：finite -> s1 -> ... -> sk -> ∞（方向由 right 决定；左端反常段贡献取负）
    chain = [fin] + [N(Fr(s)) for s in (splits if right else list(reversed(splits)))]
    acc = T.ZERO
    for i in range(len(chain) - 1):
        a_, b_ = chain[i], chain[i + 1]
        ll = _limit(F, x, a_, "+" if right else "-")
        lr = _limit(F, x, b_, "-" if right else "+")
        if ll is None or lr is None:
            return None, "UNKNOWN", "endpoint limit undecidable"
        if _is_inf(ll) or _is_inf(lr):
            return None, "DIVERGES", f"improper integral diverges at segment {i}"
        if right:
            acc = T.plus(acc, lr, T.neg(ll))
        else:
            acc = T.plus(acc, ll, T.neg(lr))
    # 末段：有限端 -> ±∞（右：F(∞)−F(端)；左：F(端)−F(−∞)）
    last = chain[-1]
    l0 = _limit(F, x, last, "+" if right else "-")
    linf = _limit(F, x, T.INFINITY if right else T.neg(T.INFINITY))
    if l0 is None or linf is None:
        return None, "UNKNOWN", "limit at infinity undecidable"
    if _is_inf(l0) or _is_inf(linf):
        return None, "DIVERGES", "improper integral diverges at infinity"
    if right:
        acc = T.plus(acc, linf, T.neg(l0))
    else:
        acc = T.plus(acc, l0, T.neg(linf))
    status = "VERIFIED" if ok else "UNVERIFIED"
    return simplify(acc), status, "improper integral: antiderivative + limit at infinity"


def _defint_piecewise(t, x, lo, hi):
    """Piecewise 被积函数：条件线性根定分支点，段内中点代入 decide 选支，
    逐段递归 defint（分支选择只是结构判定，结果仍走符号验证/交叉核对）。"""
    from cas.context import Context
    from cas.decide import decide, T3
    from cas.evalnum import eval_approx, EvalNumError
    from cas.solve import _linear_split

    try:
        lo_f = eval_approx(lo, {})
        hi_f = eval_approx(hi, {})
    except EvalNumError:
        return None, "unsupported", "bounds not numerically comparable"
    if lo_f > hi_f:
        lo, hi, lo_f, hi_f = hi, lo, hi_f, lo_f
        flip = True
    else:
        flip = False
    if abs(hi_f - lo_f) < 1e-12:
        return T.ZERO, "VERIFIED", "empty interval"
    branches = [(t.args[i], t.args[i + 1]) for i in range(0, len(t.args), 2)]
    # 分支点：条件化 cmp(expr, 0) 后取 expr 关于 x 的线性根
    splits = set()
    for _v, c in branches:
        if isinstance(c, T.BVal):
            continue
        if not (isinstance(c, T.Expr) and c.head.name in ("Lt", "Le", "Gt", "Ge")):
            return None, "UNKNOWN", "non-comparison condition undecidable"
        expr = T.plus(c.args[0], T.neg(c.args[1]))
        expr = simplify(expr)
        a_, b_ = _linear_split(expr, x)
        if not T.is_num(a_) or T.num_val(a_) == 0:
            return None, "UNKNOWN", "nonlinear branch condition undecidable"
        r = -T.num_val(b_) / T.num_val(a_)
        if lo_f < float(r) < hi_f:
            splits.add(r)
    pts = [lo] + [N(Fr(s)) for s in sorted(splits)] + [hi]
    pts_f = [lo_f] + [float(s) for s in sorted(splits)] + [hi_f]

    def pick(m):
        mv = T.N(Fr(m).limit_denominator(10 ** 9))
        for v, c in branches:
            if c is T.TRUE or (isinstance(c, T.BVal) and c.val):
                return v
            r = decide(T.subst(c, {x: mv}), Context())
            if r is T3.YES:
                return v
            if r is not T3.NO:
                return None
        return None

    acc = T.ZERO
    worst = "VERIFIED"
    for i in range(len(pts) - 1):
        mid = (pts_f[i] + pts_f[i + 1]) / 2
        branch = pick(mid)
        if branch is None:
            return None, "UNKNOWN", f"branch undecidable on segment {i}"
        v, st, _n = defint(branch, x, pts[i], pts[i + 1])
        if v is None:
            return None, st, f"segment {i}: " + _n
        acc = T.plus(acc, v)
        if st != "VERIFIED":
            worst = st
    val = simplify(acc)
    if flip:
        val = T.neg(val)
    return val, worst, "piecewise: branch split + midpoint selection"


def _sing_points(t, x, lo_f, hi_f):
    """开区间内的奇点（精确有理根）；无理根位置不可判 -> None（诚实拒答）。"""
    from cas.domain import dom_condition
    from cas.simplify import expand
    from cas.factor import factor
    from cas.sturm import isolate_real_roots

    pts = set()
    for c in dom_condition(t):
        if not (isinstance(c, T.Expr) and c.head.name in ("Ne", "Gt", "Ge")):
            continue
        b = c.args[0]
        if x not in T.free_vars(b):
            continue
        try:
            p = Poly.from_term(expand(b), (x,))
        except PolyError:
            return None
        if p.degree(x) <= 0:
            continue
        _cst, facs = factor(p)
        for g, _mult in facs:
            if g.degree(x) == 1:
                r = -g.const_val() / g.lc(x)
                if lo_f < float(r) < hi_f:
                    pts.add(r)
            else:
                for a_, b_ in isolate_real_roots(g):
                    if float(b_) <= lo_f or float(a_) >= hi_f:
                        continue
                    # 无理根落在区间内：精确位置不可判 -> 拒答
                    return None
    return sorted(pts)


def _numeric_cross(t, x, pts_f, val):
    """梯形法采样交叉核对：True=一致，None=不可核（端点奇异/求值失败），False=矛盾。

    探测通道：只用于扣留可疑结果（False -> UNKNOWN），不作为证明。
    梯形法误差 O(m^-2)；端点不可求值（反常积分）时跳过核对不硬判。
    """
    from cas.evalnum import eval_approx, EvalNumError

    try:
        vf = eval_approx(val, {})
    except EvalNumError:
        return None
    total = 0.0
    m = 200
    for a, b in zip(pts_f, pts_f[1:]):
        try:
            fa = eval_approx(t, {x: Fr(a).limit_denominator(10 ** 9)})
            fb = eval_approx(t, {x: Fr(b).limit_denominator(10 ** 9)})
        except (EvalNumError, OverflowError, ValueError):
            return None   # 端点奇异：反常积分，跳过核对
        ssum = (fa + fb) / 2
        for j in range(1, m):
            xv = a + (b - a) * j / m
            try:
                ssum += eval_approx(t, {x: Fr(xv).limit_denominator(10 ** 9)})
            except (EvalNumError, OverflowError, ValueError):
                return None
        total += ssum * (b - a) / m
    scale = max(1.0, abs(vf), abs(total))
    if abs(total - vf) <= 1e-4 * scale + 1e-9:
        return True
    return False