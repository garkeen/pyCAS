"""定积分（自 cas/integrate.py 拆出）：Newton-Leibniz + 奇点拆分 +
端点极限 + 数值采样交叉核对；±∞ 反常判敛；Piecewise 分段；
中点反射对称与 spec.period 周期折叠。

不定积分入口见 cas/intcore.py（有理核见 cas/ratint.py）。
"""

from fractions import Fraction as Fr

from cas.errors import PolyError
from cas.risch import RischNonElementary, RischUnsupported
from cas.poly import Poly
from cas.intcore import integrate, _flatten_inv, _term_size
from cas.pprint import to_str
from cas.simplify import simplify
from cas import term as T
from cas.term import S, N, Sym


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
    except RischNonElementary:
        # Risch 证明不可初等：定积分无初等原函数，诚实拒答（带证明标记）
        return None, "unsupported", "no elementary antiderivative (proved)"
    except (PolyError, RischUnsupported):
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
    except RischNonElementary:
        # Risch 证明不可初等：定积分无初等原函数，诚实拒答（带证明标记）
        return None, "unsupported", "no elementary antiderivative (proved)"
    except (PolyError, RischUnsupported):
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
