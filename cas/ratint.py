"""有理函数不定积分核（自 cas/integrate.py 拆出）：Hermite 分解 +
对数部分（线性闭式 / RootOf / atan 实形式）+ AN 隔离区间精确符号 +
根式与非常数项的局部参数化收集。

上层入口见 cas/intcore.py（不定积分）与 cas/defint.py（定积分）；
cas/integrate.py 为三者的兼容门面。
"""

from fractions import Fraction as Fr

from cas.errors import PolyError
from cas.risch import RischNonElementary, RischUnsupported
from cas.poly import Poly, SymRat, ugcd
from cas.apart import apart
from cas.algnum import RootOf, qa_div, qa_mul, qa_inv, tr_power_sums, tr_eval, coefs
from cas import term as T
from cas.term import S, N, Sym, IU
from cas.scalarutil import (rf_const_ga, ga_den, lcm2,
                            ga_vec_to_ints, mk_zero_like,
                            leaf_has_ga, symrat_has_ga,
                            coef_zero, coef_re_im, poly_re_im)


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
    leaves = list(num.monos.values()) + list(den.monos.values())
    if any(not isinstance(c, (Fr, SymRat)) for c in leaves) \
            or any(isinstance(c, SymRat) and symrat_has_ga(c)
                   for c in leaves):
        # M5.3.1 ℚ(i) / M5.4-c ℚ(i,params) 混合：跳过 gcd（ugcd 的伪除
        # 对内嵌 Ga 的分数塔会指数爆炸——实测挂死）。不约分不影响正确性，
        # 只增大次数；混合拆分在 _ga_rational_split 统一处理。
        return num, den
    g = ugcd(num, den)
    if not g.is_zero():
        num = num.udivmod(g)[0]
        den = den.udivmod(g)[0]
    return num, den


def _is_named_const(t):
    """命名常数节点（pi/e/gamma）。"""
    from cas.term import Const
    return isinstance(t, Const) and getattr(t, "name", "") in \
        ("pi", "e", "gamma")


_CONST_FUNCT_HEADS = ("Sin", "Cos", "Tan", "Atan", "Exp", "Log",
                      "Sinh", "Cosh", "Tanh")


def _collect_const_params(t, x):
    """M5.6#1：非有理常数项 -> 局部参数符号映射（统一规则）。

    收集判定（极大子项，不含积分变量）：
    - 命名常数（pi/e/gamma）-> 收
    - 函数头复合项（sin(1)、e^2、atan(1/2)、嵌套根式 sqrt(1+sqrt(2))
      类）-> 整体收
    - Power 非整指数 -> 收（数值底=根式；其他底整体收）
    - Plus/Times/整幂 -> 不收，下降到子项各自判定
    环可构造形态由 Poly._build 原生支持；收集仅覆盖构造不了的部分。
    Richardson 安全性与 Log(常量) 参数化同源：互相超越独立假设
    只可能保守拒绝。返回 {const_term: Sym}。
    """
    out = {}

    def _collectible(u):
        if x in T.free_vars(u):
            return False
        if _is_named_const(u):
            return True
        if isinstance(u, T.Expr):
            n = u.head.name
            if n in _CONST_FUNCT_HEADS:
                return True
            if n == "Power":
                e_ = u.args[1]
                return not isinstance(e_, T.Int)
            return False
        return False

    stack = [t]
    while stack:
        u = stack.pop()
        if _collectible(u) and not any(u is k for k in out):
            _RC_COUNTER[0] += 1
            out[u] = Sym(f"_rc{_RC_COUNTER[0]}")
            continue                     # 极大整叶替换
        if isinstance(u, T.Expr):
            stack.extend(u.args)
    return out


def _collect_rad_params(t):
    """数值底有理指数幂叶 -> 局部参数符号映射（M5.4-c 有理通道投影）。

    与 risch._collect_radical 的本质差别：纯局部映射，不登记全局
    ALG_MODULI/ALG_RELATIONS——有理通道全程把 α 当互相超越独立的
    不透明参数（形式恒等 ⇒ 一致特化下成立：只可能少化简，不可能
    错），出口由 QxStruct.retract 回代还原根式形态。
    返回 {rad_term: Sym}（同形幂共享符号）；无根式叶返回 {}。
    """
    out = {}
    stack = [t]
    while stack:
        u = stack.pop()
        if isinstance(u, T.Expr):
            if u.head.name == "Power":
                b, e = u.args
                if isinstance(e, T.Rat) and e.f.denominator != 1 \
                        and T.is_num(b) and T.num_val(b) > 0 \
                        and not any(u is k for k in out):
                    # 全局唯一编号：跨调用不复用（残留区间表只冗余不致错）
                    _RC_COUNTER[0] += 1
                    out[u] = Sym(f"_rc{_RC_COUNTER[0]}")
                    continue          # 整叶替换，不再深入
            stack.extend(u.args)
    return out


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

    A2 通道优先：若判别式的全部自由符号都在本调用作用域的代数常数
    隔离区间表（AN_INTERVALS）中，则做精确区间求值——端点全为 Fr、
    四则向外取界，结果区间不跨零即为穷举证明（这是隔离判定而非数值
    采样，不违反"采样永不进 YES 通道"纪律）。
    否则走 decide 区间通道（平方和+常数等结构显然情形可判；
    自由符号一般情形诚实返回 unknown）。
    """
    sig = _an_interval_sign(D)
    if sig is not None:
        return sig
    from cas.decide import decide, T3
    from cas.context import Context

    ctx = Context()
    Dt = D.to_term()
    if decide(T.mk(S("Gt"), (Dt, T.ZERO)), ctx) is T3.YES:
        return "pos"
    if decide(T.mk(S("Lt"), (Dt, T.ZERO)), ctx) is T3.YES:
        return "neg"
    return "unknown"


AN_INTERVALS = {}
AN_RELATIONS = {}            # _rc 符号 -> monic 极小多项式（A3 作用域登记）
_RC_COUNTER = [0]


def _radical_bracket(bv, pn, qd):
    """正有理底 b 的 pn/qd 次幂的严格隔离区间 [lo, hi]（Fr 端点）。

    v = b^(pn/qd) > 0：整数缩放后二分求 floor(v·M)，区间宽 1/M。
    """
    from math import isqrt

    M = 10 ** 14
    bn, bd = bv.numerator, bv.denominator
    if pn < 0:
        bn, bd = bd, bn
        pn = -pn
    # v^qd = bn^pn / bd^pn；floor(v·M)：解 k^qd ≤ bn^pn·M^qd/bd^pn < (k+1)^qd
    num = bn ** pn * M ** qd
    den = bd ** pn
    target = num // den
    k = int(round(target ** (1.0 / qd)))
    while k > 0 and k ** qd > target:
        k -= 1
    while (k + 1) ** qd <= target:
        k += 1
    return Fr(k, M), Fr(k + 1, M)


def _iv_mul(a, b):
    (a0, a1), (b0, b1) = a, b
    ps = (a0 * b0, a0 * b1, a1 * b0, a1 * b1)
    return min(ps), max(ps)


def _poly_interval_sign(p, env):
    """Poly 在变量区间环境下的精确符号：'pos'/'neg'/None（跨零）。"""
    tot_lo, tot_hi = Fr(0), Fr(0)
    for k, c in p.monos.items():
        if not isinstance(c, Fr):
            return None
        iv = (Fr(1), Fr(1))
        for v, e in zip(p.vars, k):
            if e == 0:
                continue
            if v not in env:
                return None
            for _ in range(e):
                iv = _iv_mul(iv, env[v])
        lo, hi = iv
        if c >= 0:
            tot_lo += c * lo
            tot_hi += c * hi
        else:
            tot_lo += c * hi
            tot_hi += c * lo
    if tot_lo > 0:
        return "pos"
    if tot_hi < 0:
        return "neg"
    return None


def _an_interval_sign(D):
    """SymRat 判别式的 AN 区间精确符号：'pos'/'neg'/None。"""
    if not isinstance(D, SymRat):
        return None
    ns = _poly_interval_sign(D.num, AN_INTERVALS)
    if ns is None:
        return None
    ds = _poly_interval_sign(D.den, AN_INTERVALS)
    if ds is None:
        return None
    if ds == "pos":
        return ns
    return "neg" if ns == "pos" else ("pos" if ns == "neg" else None)


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
                raise RischUnsupported("parameter discriminant is identically zero")
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


def _poly_eq_relaware(A, B):
    """多项式恒等判定（AN 关系感知，M5.4-c A3 配套）。

    纯 Fr 时退化为结构相等；含 AN 符号时结构相等过强——1/(2α) 与
    α/4 语义同、结构异（关系约简不改变分数形态），差值叶系数经
    模约简后判零才是精确等词。"""
    D = A - B
    if D.is_zero():
        return True
    from cas.poly import _reduce_alg_var, ALG_MODULI
    regs = {**ALG_MODULI, **AN_RELATIONS}
    if not regs:
        return False
    out = {}
    for k, c in D.monos.items():
        if isinstance(c, SymRat):
            n_, d_ = c.num, c.den
            for v, m in regs.items():
                if v in n_.vars:
                    n_ = _reduce_alg_var(n_, v, m)
                if v in d_.vars:
                    d_ = _reduce_alg_var(d_, v, m)
            if not n_.is_zero():
                out[k] = SymRat(n_, d_)
        elif isinstance(c, Fr):
            if c != 0:
                out[k] = c
        else:
            return False
    return not out


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
    return _poly_eq_relaware(num * Q, P * den)


def _ga_rational_split(P, Q, x):
    """ℚ(i)/ℚ(i,params) 有理函数共轭展开实虚拆分（M5.3.1 + A4 泛化）。

    系数级规范化：P,Q 逐系数取 (re, im) 对——SymRat 内嵌 Ga 分母
    有理化，全部化为纯参数叶。Q̄=(Qre,-Qim) ⟹ Q·Q̄=Qre²+Qim² 实；
    P·Q̄ = (Pre·Qre+Pim·Qim) + i·(Pim·Qre-Pre·Qim)，两通道各走完整
    纯参数链（Hermite + atan/RootOf log）。答案为实形态（log(x²+1)+
    i·atan 类）。"""
    pre, pim = poly_re_im(P)
    qre, qim = poly_re_im(Q)
    den = qre * qre + qim * qim
    if den.is_zero():
        raise PolyError("zero denominator after conjugate expansion")
    num_re = pre * qre + pim * qim
    num_im = pim * qre - pre * qim
    v1, ok1, pv1 = integrate_rational(num_re, den, x)
    if num_im.is_zero():
        return v1, ok1, pv1
    v2, ok2, pv2 = integrate_rational(num_im, den, x)
    return T.plus(v1, T.times(IU, v2)), ok1 and ok2, pv1 + pv2


def integrate_rational(P, Q, x, structured=False):
    """∫ P/Q dx → (term, verified, provisos)。P, Q 单变量，Q 非零。

    structured=True 时额外返回 (rat_term, extra_term)：
    rat_term = 纯有理部分（poly + 有理式项），extra_term = log/atan/
    RootOf 对数项之和（M5.2 primitive 层逐阶剥离用）。
    """
    coeffs = list(P.monos.values()) + list(Q.monos.values())
    if any(not isinstance(c, (Fr, SymRat)) for c in coeffs) \
            or any(isinstance(c, SymRat) and symrat_has_ga(c)
                   for c in coeffs):
        # ℚ(i) / ℚ(i,params) 混合（M5.3.1 + A4）：共轭展开实虚拆分
        # 归约纯参数链。旧 "pending" 诚实拒绝退役。
        return _ga_rational_split(P, Q, x)
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
    if structured:
        rp = []
        if not poly_int.is_zero():
            rp.append(poly_int.to_term())
        for u, p, kk in rat_terms:
            rp.append(T.div(u.to_term(), T.pw(p.to_term(), N(kk))))
        rat_term = T.mk(S("Plus"), tuple(rp)) if len(rp) > 1 else (rp[0] if rp else T.ZERO)
        extra = _assemble(Poly.zero((x,)), [], lin_logs, root_logs, x)
        return term, verified, provisos, rat_term, extra
    return term, verified, provisos
