"""不定积分入口与快速通道（自 cas/integrate.py 拆出）：自动换元、
spec anti 表、三角多项式线性化、tan-half 代换、特殊函数出口、
SOLVERS 总表瀑布。有理核见 cas/ratint.py；定积分见 cas/defint.py。
"""

from cas.errors import PolyError
from cas.risch import RischNonElementary, RischUnsupported
from cas.ratint import _rat_pair, integrate_rational
from cas.simplify import simplify, expand
from cas.pprint import to_str
from cas import term as T
from cas.term import S, N, Sym


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
        except RischNonElementary:
            continue   # 内层证明无初等原函数=该候选不适用（外层继续）
        except RischUnsupported:
            continue   # 内层超界（如代数相关守卫）=放弃候选，非终局
        F = T.subst(H, {z: g})
        # 换元是启发式探测：每候选微分回验，未验证继续试下一候选（永不静默错）
        from cas.diff import verify as _verify

        if _verify(F, x, t) != "VERIFIED":
            continue
        return F, True, g, h, H
    return None


def integrate(t, x, principal=None):
    """∫ t dx（外层）：EF 收缩 + 各通道结果统一过参数分母 proviso 扫描。

    EF 收缩（FriCAS iiilog 同款）：Exp(k·Log(u)) -> u^k（k∈ℤ 精确）——
    ln(e^{2ln x}-(x-1)^2) 类伪装式先收缩为 ln(2x-1) 再入管线。
    M5.6#4 阶段一：generic 答案在参数退化点（e^{ax}/a 的 a=0 类）
    无定义而原函数存在——静默输出即撒谎，此处强制声明成立条件。
    """
    # 变量名归一：字符串入参必须折算为驻留 Sym——塔覆盖检查与
    # free_vars 全靠指针同一，裸字符串曾致 e^x 建层后残留检查误判
    # "not covered"（诚实性缺陷：错拒载体伪装成超界说明）
    if isinstance(x, str):
        x = T.S(x)
    from cas.structure import run_pre_passes

    t, a = run_pre_passes(t, x)
    F, ok, method, provisos = _integrate_core(t, x, a,
                                              principal=principal)
    from cas.risch import _param_provisos
    for p in _param_provisos(F, x):
        if p not in provisos:
            provisos.append(p)
    return F, ok, method, provisos


def _symbol_power_antideriv(t, x):
    """∫u^a dx（a 为不含 x 的符号指数）：u^(a+1)/((a+1)·slope)。

    M5.6 退化分支：generic 公式在 a=-1 处无定义而原函数（ln u/slope）
    存在——静默输出即撒谎，proviso 强制声明 [a+1≠0]。数值指数
    （含 -1）不走此通道（spec 表/既有有理幂通道已覆盖）。
    """
    if not (isinstance(t, T.Expr) and t.head.name == "Power"):
        return None
    u, e = t.args
    if x in T.free_vars(e):
        return None
    if T.is_num(e):
        return None
    from cas.solve import _linear_split
    sp = _linear_split(u, x)
    if sp is None:
        return None
    slope, _intercept = sp
    new_e = T.plus(e, N(1))
    F = T.div(T.pw(u, new_e), T.times(new_e, slope))
    proviso = T.mk(S("Ne"), (new_e, T.ZERO))
    return F, proviso


def _power_antideriv(t, x):
    """有理幂单项式 f(u)^q（q∈ℚ 非整，u 线性）：代数诚实路线。

    ∫ u^q dx = u^{q+1}/(a(q+1))——答案保持根式/幂形态（不折算
    exp-log 通道，代数核追踪留给 M7a）。"""
    if not (isinstance(t, T.Expr) and t.head.name == "Power"
            and len(t.args) == 2):
        return None
    u, e = t.args
    if not isinstance(e, T.Rat) or e.f.denominator == 1:
        return None
    from cas.solve import _linear_split
    sp = _linear_split(u, x)
    if sp is None:
        return None
    a_, b_ = sp
    if T.is_num(a_) and T.num_val(a_) == 0:
        return None
    new_e = e.f + 1
    F = T.div(T.pw(u, N(new_e)), T.times(a_ if not T.is_num(a_)
                                         else T.N(T.num_val(a_)), N(new_e)))
    return F


def _integrate_core(t, x, a=None, principal=None):
    """∫ t dx（t 为 term，x 为 Sym）→ (term, verified, method, provisos)。

    裸 spec 函数走 anti 表（连续原函数，定积分友好）；
    正向复合 t = h(g(x))·g'(x) 走自动换元（代回不需逆函数）；
    有理函数走 Hermite+RootOf；sin x/cos x 有理式走 t=tan(x/2) 代换。
    method 供策略通道可解释输出（REPL/step log）；provisos 为参数情形的条件声明。
    """
    F0 = _spec_antideriv(t, x)
    if F0 is not None:
        from cas.diff import verify as _verify

        ok = _verify(F0, x, t,
                     principal=principal) == "VERIFIED"
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
    pw_ = _power_antideriv(t, x)
    if pw_ is not None:
        from cas.diff import verify as _verify

        ok = _verify(pw_, x, t,
                     principal=principal) == "VERIFIED"
        return pw_, ok, "rational power rule (algebraic form)", []
    spw = _symbol_power_antideriv(t, x)
    if spw is not None:
        from cas.diff import verify as _verify

        F_sp, proviso = spw
        ok = _verify(F_sp, x, t,
                     principal=principal) == "VERIFIED"
        return F_sp, ok, "symbolic power rule (generic form)", [proviso]
    # SOLVERS 总表（N2 兑现 v3 设计）：头部快速通道 + Struct 三段式
    # 统一为声明式数据。attempt 协议：
    #   ('hit', F, method, provisos[, ok])   ok 缺省=已自验 True；
    #                                        ok=None => 管线统一验证
    #   ('miss', reason)                     不适用，原因入聚合
    # RischNonElementary（证明性拒答）在条目内部走完特殊函数出口后
    # 原样上抛——绝不吞。
    from cas.structs import SOLVERS
    from cas.diff import verify as _verify

    last_reason = ""
    for s in SOLVERS:
        verdict = s.attempt(t, x)
        if verdict[0] == "miss":
            if verdict[1]:
                last_reason = verdict[1]
            continue
        if len(verdict) == 5:
            _tag, term, method, provisos, ok = verdict
            if ok is None:                 # 塔通道：管线统一验证
                ok = _verify(term, x, t,
                             principal=principal) == "VERIFIED"
        else:
            _tag, term, method, provisos = verdict
            ok = True
        return term, ok, method, provisos
    raise RischUnsupported("unsupported integrand"
                    + (": " + last_reason if last_reason else ""))


def _special_output(t, x):
    """M5.5：特殊函数出口（结构化候选族 + verify 背书）。

    Risch 证明不可积后，按形状匹配生成候选原函数；每个候选必须过
    diff.verify（导数塌缩回初等域后精确判等）——未验证的候选绝不
    出门（启发式探测必须回验裁决纪律）。

    候选族（FriCAS rdeefx ei_int primpart 形态的产品级对应）：
    - Si 族：sin(x)/x -> Si(x)
    - Ei 线性族：e^(ax+b)/(cx+d) -> (c/a)·e^(b-ad/c)·Ei((a/c)(cx+d))
    - li 族：1/Log(x) -> Li(x)；1/Log(cx+d) -> Li(cx+d)/c
    - Ci 族：cos(x)/x -> Ci(x)
    - erf 族：e^(-x^2) -> sqrt(pi)/2 · erf(x)（sqrt(pi) 经命名常数幂
      参数化进塔零判定，验证链精确归零）
    """
    from cas.diff import verify as _vf

    def _mk(name, arg):
        return T.mk(S(name), (arg,))

    def _is_inv(t_):
        """t_ 是否形如 u^(-1)，返回 u 或 None。"""
        if isinstance(t_, T.Expr) and t_.head.name == "Power" \
                and isinstance(t_.args[1], T.Int) and t_.args[1].v == -1:
            return t_.args[0]
        return None

    def _lin_split(u):
        from cas.solve import _linear_split as _ls

        return _ls(u, x)

    cands = []

    # --- Si / Ci 族：sin(x)/x、cos(x)/x ---
    if t == T.div(T.sin(x), x):
        cands.append(_mk("Si", x))
    if t == T.div(T.cos(x), x):
        cands.append(_mk("Ci", x))

    # --- li 族：1/Log(u) ---
    inv = _is_inv(t)
    if inv is not None and isinstance(inv, T.Expr) \
            and inv.head.name == "Log":
        sp = _lin_split(inv.args[0])
        if sp is not None:
            c_, d_ = sp
            c_v = T.num_val(c_) if T.is_num(c_) else None
            if c_v is not None and c_v != 0:
                F = T.div(_mk("Li", inv.args[0]),
                          N(c_v) if c_v.denominator != 1 or True else c_)
                cands.append(F)

    # --- erf 族：e^(-x^2)（含常数倍）---
    if t == T.exp(T.neg(T.pw(x, N(2)))):
        cands.append(T.times(T.div(T.sqrt(T.PI), N(2)), _mk("Erf", x)))

    # --- Ei 线性族：num/den 形，num 含 e^(ax+b)、den 线性 ---
    num_t, den_t = None, None
    inv2 = _is_inv(t)
    if inv2 is not None:
        den_t, num_t = inv2, N(1)
    elif isinstance(t, T.Expr) and t.head.name == "Times":
        nums = []
        dens = []
        for fac in t.args:
            d3 = _is_inv(fac)
            if d3 is not None:
                dens.append(d3)
            else:
                nums.append(fac)
        if len(dens) == 1:
            den_t = dens[0]
            num_t = T.mk(S("Times"), tuple(nums)) if len(nums) > 1 \
                else (nums[0] if nums else N(1))
    if den_t is not None:
        inner = None
        coef = N(1)
        if isinstance(num_t, T.Expr) and num_t.head.name == "Exp":
            inner = num_t.args[0]
        elif isinstance(num_t, T.Expr) and num_t.head.name == "Times":
            exps = [f_ for f_ in num_t.args
                    if isinstance(f_, T.Expr) and f_.head.name == "Exp"]
            rest = [f_ for f_ in num_t.args
                    if not (isinstance(f_, T.Expr) and f_.head.name == "Exp")]
            if len(exps) == 1:
                inner = exps[0].args[0]
                coef = T.mk(S("Times"), tuple(rest)) if rest else N(1)
        if inner is not None:
            sp_n = _lin_split(inner)
            sp_d = _lin_split(den_t)
            if sp_n is not None and sp_d is not None:
                a_, b_ = sp_n
                c_, d_ = sp_d
                a_v = T.num_val(a_) if T.is_num(a_) else None
                c_v = T.num_val(c_) if T.is_num(c_) else None
                if a_v is not None and a_v != 0 \
                        and c_v is not None and c_v != 0:
                    k = T.div(a_, c_)
                    phase = T.plus(b_, T.neg(T.times(k, d_)))
                    # 相位因子保持 Exp 核形式：塔内坍缩（线性 arg 拆分）
                    # 同样生成 Exp 字面核；若此处改用命名原子 E，两面孔
                    # 在塔叶键中不可消去 ⟹ verify 失败（ei 族回归钉实证）
                    # d(C·Ei(k(cx+d))) = C·c·e^(k(cx+d))/(cx+d)
                    # => 需 C·c·e^(kd)=e^b => C = e^(b-kd)/c
                    F = T.times(coef, T.div(N(1), c_), T.exp(phase),
                                _mk("Ei", T.times(k, den_t)))
                    cands.append(F)

    for F in cands:
        try:
            if _vf(F, x, t) == "VERIFIED":
                return F, True, "special function output", []
        except Exception:
            continue
    return None


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
    斜率 a 放宽为任意不含 x 的非零常量项（M5.6#1：符号/命名常数斜率
    γ、π、a+1 类；退化点由外层参数分母扫描声明 [a≠0]）。
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
    if x in T.free_vars(a_):
        return None
    if T.is_num(a_):
        if T.num_val(a_) == 0:
            return None
        a_div = T.N(T.num_val(a_))
    else:
        a_div = a_
    if x not in T.free_vars(arg):
        return None
    return T.div(sp.anti(arg), a_div)


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
