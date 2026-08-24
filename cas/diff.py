from cas import term as T
from cas.term import S, N, Expr, Sym, Int, plus, times, pw, neg, ONE, MONE, TWO
from cas import spec as _spec


def d(t, x):
    if isinstance(t, Sym):
        return T.ONE if t is x else T.ZERO
    if T.is_num(t) or isinstance(t, (T.Const, T.Special, T.DB, T.BVal, T.PatVar, T.PatSeq)):
        return T.ZERO
    if isinstance(t, T.Bound):
        return T.mk(S("D"), (t, x))
    name = t.head.name
    if name == "Plus":
        return plus(*[d(a, x) for a in t.args])
    if name == "Times":
        parts = []
        for i, a in enumerate(t.args):
            rest = tuple(b for j, b in enumerate(t.args) if j != i)
            parts.append(times(d(a, x), *rest))
        return plus(*parts)
    if name == "Power":
        b, e = t.args
        if isinstance(e, Int):
            if e.v == 0:
                return T.ZERO
            return times(e, pw(b, N(e.v - 1)), d(b, x))
        return times(t, plus(times(d(e, x), T.fn("Log")(b)), T.div(times(e, d(b, x)), b)))
    if name == "Quote":
        return T.mk(S("D"), (t, x))
    if name == "Piecewise" and len(t.args) % 2 == 0:
        # 结构头（同 Plus/Times 类别）：逐分支求导，条件照抄；边界连续性不判
        new = []
        for i in range(0, len(t.args), 2):
            new.extend([d(t.args[i], x), t.args[i + 1]])
        return T.mk(S("Piecewise"), tuple(new))
    # 导数表来自 FunctionSpec 注册表（反硬编码：新函数在 spec.py 注册即可）
    sp = _spec.get(name)
    if sp is not None and sp.deriv is not None and len(t.args) == sp.arity == 1:
        return times(sp.deriv(t.args[0]), d(t.args[0], x))
    return T.mk(S("D"), (t, x))


def _tower_zero(a, b, x):
    """a − b 在 exp/log 微分塔上是否恒零（塔内表示唯一性，M5 结构定理）。

    build_extension 成功（被积式覆盖 by 塔）时分子 is_zero 即精确 YES；
    塔外（三角/代数依赖/嵌套）返回 False——交回通用管线结论。
    """
    from cas.risch import build_extension, RischUnsupported

    try:
        from cas.risch import (trigs_to_exp, _norm_const_base_powers,
                           _parametrize_const_logs)
        d0 = plus(a, neg(b))
        if d0 is T.ZERO:
            return True
        if T.is_num(d0) and T.num_val(d0) == 0:
            return True   # 防御：环规范化产出的非常驻数值零
        # 与 integrate_exp_tower 同款入口归一（M5.6）：数值底幂 -> 复
        # 指数、Log(常量) -> 独立超越参数——两侧同一常量集按同一排序
        # 编号，替换一致；恒等式在 ℚ(c₁..)(tower) 上判定，对真实
        # 超越值特化仍成立（独立性假设只会保守拒绝，不产生误证）
        # M5.5：入口先 expand+simplify——链式法则产物含 Exp(c)·Exp(u)
        # 双层积与未提取的常数分母，未经环规范折叠会让塔构建拒绝
        from cas.simplify import simplify as _simp, expand as _exp
        d0 = _simp(_exp(d0))
        d0 = trigs_to_exp(_norm_const_base_powers(d0, x))
        d0, _bs = _parametrize_const_logs(d0, x)
        # N1 根治后：系数域总算术（SymRat∘Ga 规范形 Ga(SymRat,·) +
        # 域泛化 ugcd/mgcd），build_extension 原生接受混合系数——
        # 旧版含 IU 预拆与混合域回退特判已删
        _de, na, nd = build_extension(d0, x)
        return na.is_zero()
    except Exception:
        return False


def verify(F, x, f, budget=100000, principal=None):
    """N2：验证管线 = equivalent 短路 + VERIFY_STAGES 声明式序列。

    旧版内联的 ratpow_merge/atomize 块迁入 structure.VERIFY_STAGES
    （needs 门控统一走 Stage.gated 的 principal 承诺位）。principal
    显式入参 = 调用方临时覆盖策略位（管线期间生效，退出还原）。"""
    from cas.decide import equivalent, T3
    from cas.structure import (VERIFY_STAGES, BRANCH_POLICY,
                               run_verify_stages)

    dF = d(F, x)
    r = equivalent(dF, f, budget=budget)
    if r is T3.YES:
        return "VERIFIED"
    if r is T3.NO:
        return "FAILED"
    d0 = T.plus(dF, T.neg(f))
    if principal is None:
        ok, _dg = run_verify_stages(d0, x)
    else:
        saved = BRANCH_POLICY.get("principal", False)
        BRANCH_POLICY["principal"] = bool(principal)
        try:
            ok, _dg = run_verify_stages(d0, x)
        finally:
            BRANCH_POLICY["principal"] = saved
    if ok:
        return "VERIFIED"
    if r is T3.PROBABLE:
        return "PROBABLE"   # 数值采样支持，非符号证明
    return "UNVERIFIED"


# ---------------------------------------------------------------------------
# 判等阶段注册（Step 4 收官）：塔零判定与分数幂合并进入 equivalent()
# 的声明式阶段序列——三处重复分派的最后一份消除。
# ---------------------------------------------------------------------------


def _eq_has_elfold(t):
    stack = [t]
    while stack:
        u = stack.pop()
        h = getattr(u, "head", None)
        if h is None:
            continue
        if h.name in ("Exp", "Log"):
            return True
        stack.extend(getattr(u, "args", ()) or ())
    return False


def _eq_single_var(r):
    from cas import term as T
    vs = T.free_vars(r)
    return vs[0] if len(vs) == 1 else None


def _eq_stage_tower(r, a, b, ctx):
    """形式塔零判定：两侧投影进同一核分式做精确零判定（Risch 结构定理）。"""
    from cas import term as T
    from cas.decide import T3
    if not _eq_has_elfold(r):
        return None
    xv = _eq_single_var(r)
    if xv is None:
        return None
    return T3.YES if _tower_zero(r, T.ZERO, xv) else None


def _eq_stage_ratpow(r, a, b, ctx):
    """分数幂合并（principal 承诺门控，P4 语义）。"""
    from cas import term as T
    from cas.decide import T3
    from cas.structure import principal_branch, _merge_ratpow
    if not principal_branch():
        return None
    m = _merge_ratpow(r)
    if m is r:
        return None
    if m is T.ZERO or (T.is_num(m) and T.num_val(m) == 0):
        return T3.YES
    xv = _eq_single_var(m)
    if xv is None:
        return None
    return T3.YES if _tower_zero(m, T.ZERO, xv) else None


from cas.decide import register_eq_stage

register_eq_stage("tower_zero", _eq_stage_tower, prepend=True)
register_eq_stage("ratpow_merge", _eq_stage_ratpow, prepend=True)
