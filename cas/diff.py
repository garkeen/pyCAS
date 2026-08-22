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
        from cas.risch import (trigs_to_exp, _norm_num_powers,
                               _parametrize_const_logs)
        d0 = plus(a, neg(b))
        if d0 is T.ZERO:
            return True
        if T.is_num(d0) and T.num_val(d0) == 0:
            return True   # mk 规范化折叠出的数值零（如 exp(x·log2)−2^x）
        # 与 integrate_exp_tower 同款入口归一（M5.6）：数值底幂 -> 复
        # 指数、Log(常量) -> 独立超越参数——两侧同一常量集按同一排序
        # 编号，替换一致；恒等式在 ℚ(c₁..)(tower) 上判定，对真实
        # 超越值特化仍成立（独立性假设只会保守拒绝，不产生误证）
        d0 = trigs_to_exp(_norm_num_powers(d0, x))
        d0, _bs = _parametrize_const_logs(d0)
        _de, na, nd = build_extension(d0, x)
        return na.is_zero()
    except Exception:
        return False


def verify(F, x, f, budget=100000):
    from cas.decide import equivalent, T3

    r = equivalent(d(F, x), f, budget=budget)
    if r is T3.YES:
        return "VERIFIED"
    if r is T3.NO:
        return "FAILED"
    # 塔上精确通道：exp/log 塔内零等价可判定（Risch 结构定理）
    tz = _tower_zero(d(F, x), f, x)
    if tz:
        return "VERIFIED"
    if r is T3.PROBABLE:
        return "PROBABLE"   # 数值采样支持，非符号证明
    return "UNVERIFIED"
