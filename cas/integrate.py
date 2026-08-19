"""有理函数不定积分：Hermite 分解 + 对数部分（线性闭式 / RootOf）+ 符号验证通道。"""

from fractions import Fraction as Fr

from cas.errors import PolyError
from cas.poly import Poly, ugcd
from cas.apart import apart
from cas.algnum import RootOf, qa_div, qa_mul, qa_inv, tr_power_sums, tr_eval, coefs
from cas import term as T
from cas.term import S, N


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
    """∫ f/p（p 不可约，deg f < deg p）→ 对数项列表：
    ('lin', c, p)：c·ln(p)；('root', C, p, n)：Σ_{j=1..n} C(β_j)·ln(x − β_j)。"""
    n = p.degree(x)
    if n == 1:
        lc = p.lc(x)
        if lc != 1:
            p = p.scalar(Fr(1) / lc)
        return [("lin", f.const_val(), p)]
    fp = p.deriv(x)
    C = qa_div(f, fp, p)
    return [("root", C, p, n)]


def _integrate_poly(p, x):
    out = Poly.zero((x,))
    for k, v in p.monos.items():
        e = k[0]
        out = out + Poly((x,), {(e + 1,): v / (e + 1)})
    return out


def _assemble(poly_int, rat_terms, lin_logs, root_logs, x):
    parts = []
    if not poly_int.is_zero():
        parts.append(poly_int.to_term())
    for u, p, kk in rat_terms:
        parts.append(T.div(u.to_term(), T.pw(p.to_term(), N(kk))))
    for c, p in lin_logs:
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
    for c, p in lin_logs:
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
                lin_logs.append((c, dd))
            else:
                rat_terms.append((Poly.const((x,), c / (1 - k)), dd, k - 1))
        else:
            herm, f1, k1 = _hermitte_power(nn, dd, k, x)
            rat_terms.extend(herm)
            for lg in _log_terms(f1, dd, x):
                if lg[0] == "lin":
                    lin_logs.append((lg[1], lg[2]))
                else:
                    root_logs.append((lg[1], lg[2], lg[3]))
    term = _assemble(poly_int, rat_terms, lin_logs, root_logs, x)
    verified = _verify(poly_int, rat_terms, lin_logs, root_logs, P, Q, x)
    return term, verified


def integrate(t, x):
    """∫ t dx（t 为 term，x 为 Sym）→ (term, verified)。
    有理函数走 Hermite+RootOf；sin x/cos x 有理式走 t=tan(x/2) 代换。"""
    try:
        P, Q = _rat_pair(t, x)
        return integrate_rational(P, Q, x)
    except PolyError:
        res = _trig_tan_half(t, x)
        if res is None:
            raise PolyError("unsupported integrand")
        return res


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
    """∫ R(sin x, cos x) dx：t = tan(x/2) 代换 → M1 有理积分 → 代回。"""
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