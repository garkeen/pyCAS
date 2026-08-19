"""有理函数不定积分：Hermite 分解 + 对数部分（线性闭式 / RootOf）+ 符号验证通道。"""

from fractions import Fraction as Fr

from cas.errors import PolyError
from cas.poly import Poly, ugcd
from cas.apart import apart
from cas.algnum import RootOf, qa_div, qa_mul, qa_inv, tr_power_sums, tr_eval, coefs
from cas.simplify import simplify
from cas.pprint import to_str
from cas import term as T
from cas.term import S, N, Sym


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
            parts.append(N(v))
        elif r == 1:
            parts.append(T.times(N(v), b))
        else:
            parts.append(T.times(N(v), T.pw(b, N(r))))
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


def _log_terms(f, p, x):
    """∫ f/p（p 不可约，deg f < deg p）→ 对数/反正切项列表：
    ('lin', c, p)：c·ln(p)；('atan', f, p, pc, D)：二次负判别式实形式；
    ('root', C, p, n)：Σ C(β_j)·ln(x − β_j)。"""
    n = p.degree(x)
    if n == 1:
        lc = p.lc(x)
        if lc != 1:
            p = p.scalar(Fr(1) / lc)
        return [("lin", f.const_val(), p)]
    if n == 2:
        # 实形式（判别式有理可判）：x²+pc·x+q 且 D=4q−pc²>0 时
        # ∫(Ax+B)/p = (A/2)ln(p) + (2B−A·pc)/√D · atan((2x+pc)/√D)
        lc = p.lc(x)
        pm = p.scalar(Fr(1) / lc) if lc != 1 else p
        fm = f.scalar(Fr(1) / lc) if lc != 1 else f
        pc = pm.monos.get((1,), Fr(0))
        qc = pm.monos.get((0,), Fr(0))
        D = 4 * qc - pc * pc
        if D > 0:
            return [("atan", fm, pm, pc, D)]
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
    """非负有理数 D 的精确平方根项：完全平方折叠为有理数，否则 √D 名词。"""
    import math

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
            _lg, fm, pm, pc, D = lg
            A = fm.monos.get((1,), Fr(0))
            B = fm.monos.get((0,), Fr(0))
            sd = _exact_sqrt_term(D)   # 完全平方折叠为有理数，否则保留 √D 名词
            if A != 0:
                parts.append(T.times(N(A / 2), T.log(pm.to_term())))
            k = 2 * B - A * pc
            if k != 0:
                arg = T.div(T.plus(T.times(N(2), x), N(pc)), sd)
                parts.append(T.times(N(k), T.pw(sd, T.MONE), T.atan(arg)))
            continue
        c, p = lg[1], lg[2]
        parts.append(T.times(N(c), T.log(p.to_term())))
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
            # d(atan 实形式) = f/p 恒等（代数验证：√D 系数恰消去），
            # 贡献与 f/p 通分同形
            _tg, fm, pm, _pc, _D = lg
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
    """∫ P/Q dx → (term, verified)。P, Q 单变量，Q 非零。"""
    q_poly, r = P.udivmod(Q)
    poly_int = _integrate_poly(q_poly, x)
    rat_terms = []
    lin_logs = []
    root_logs = []
    _, terms = apart(r, Q)
    for nn, dd, k in terms:
        if dd.degree(x) == 1:
            c = nn.const_val()
            if k == 1:
                lin_logs.append(("lin", c, dd))
            else:
                rat_terms.append((Poly.const((x,), c / (1 - k)), dd, k - 1))
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
    return term, verified


def integrate(t, x):
    """∫ t dx（t 为 term，x 为 Sym）→ (term, verified, method)。

    裸 spec 函数走 anti 表（连续原函数，定积分友好）；
    有理函数走 Hermite+RootOf；sin x/cos x 有理式走 t=tan(x/2) 代换。
    method 供策略通道可解释输出（REPL/step log）。
    """
    F0 = _spec_antideriv(t, x)
    if F0 is not None:
        from cas.diff import verify as _verify

        ok = _verify(F0, x, t) == "VERIFIED"
        return F0, ok, "spec antiderivative table"
    try:
        P, Q = _rat_pair(t, x)
        term, ok = integrate_rational(P, Q, x)
        return term, ok, "Hermite reduction + RootOf log part"
    except PolyError:
        res = _trig_tan_half(t, x)
        if res is None:
            raise PolyError("unsupported integrand")
        return res[0], res[1], "t = tan(x/2) substitution -> rational integration"


def _spec_antideriv(t, x):
    """裸 spec 函数（参数恰为 x）-> 简单原函数（声明式 anti 表）。"""
    from cas import spec as _spec

    if not isinstance(t, T.Expr) or len(t.args) != 1 or t.args[0] is not x:
        return None
    sp = _spec.get(t.head.name)
    if sp is None or sp.anti is None:
        return None
    return sp.anti(x)


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
    G, ok = integrate_rational(P, Q, tv)
    F = T.subst(G, {tv: T.tan(T.div(x, N(2)))})
    return F, ok


# ---------------------------------------------------------------------------
# 定积分（M3）：Newton-Leibniz + 奇点拆分 + 端点极限 + 数值采样交叉核对
# ---------------------------------------------------------------------------


def defint(t, x, lo, hi):
    """∫_lo^hi t dx -> (值项 | None, 状态, 方法/原因说明)。

    状态：VERIFIED / UNVERIFIED（原函数验证态区分）/ DIVERGES / UNKNOWN / unsupported。
    管线：不定积分 -> dom_condition 定奇点（有理根精确；无理根位置不可判则拒答）
    -> 拆区间 -> 单侧极限求值（发散即 DIVERGES）-> 数值采样交叉核对（永不静默错）。
    """
    from cas.limits import limit as _limit
    from cas.evalnum import eval_approx, EvalNumError
    from cas.simplify import simplify

    try:
        lo_f = eval_approx(lo, {})
        hi_f = eval_approx(hi, {})
    except EvalNumError:
        return None, "unsupported", "bounds not numerically comparable"
    if abs(hi_f - lo_f) < 1e-12:
        return T.ZERO, "VERIFIED", "empty interval"
    sign = 1
    if hi_f < lo_f:
        lo, hi = hi, lo
        lo_f, hi_f = hi_f, lo_f
        sign = -1
    try:
        F, ok, _method = integrate(t, x)
    except PolyError:
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