"""定积分反向换元（x = h(t)，教科书三角代换通道）。

与正向换元（defint_auto，新限正向求值）互补：反向换元需要解界方程
h(t) = lo / h(t) = hi，走 spec.inv 主支逆（sin -> arcsin 等），
新限落在主支单调窗口内。根号脱壳：√(cos²t)、|cos t| 在新限区间
落于三角非负窗口时替换为 cos t（声明式窗口表，非数值猜测）。
"""

from fractions import Fraction as Fr

from cas import term as T
from cas.term import Expr
from cas.pprint import to_str
from cas.simplify import simplify


# 三角非负窗口（主支闭区间，单位：π 的有理倍数）：
# f(t) >= 0 当且仅当 t 落在 [lo_q*π, hi_q*π]
_POS_WINDOW = {
    "Sin": (Fr(0), Fr(1)),
    "Cos": (Fr(-1, 2), Fr(1, 2)),
    "Tan": (Fr(0), Fr(1, 2)),
}


def _pi_coef(t):
    """项 -> π 的有理倍数系数（q*π -> q）；非此形态 -> None（诚实不判）。"""
    if T.is_num(t):
        v = T.num_val(t)
        return Fr(0) if v == 0 else None
    if t is T.PI:
        return Fr(1)
    if isinstance(t, Expr) and t.head.name == "Times" and len(t.args) == 2:
        a, b = t.args
        if b is T.PI and T.is_num(a):
            return T.num_val(a)
        if a is T.PI and T.is_num(b):
            return T.num_val(b)
    return None


def _resolve_sqrt_trig(w, tvar, tlo, thi):
    """新限区间整体落于非负窗口时：√(f²) 与 |f| 脱壳为 f（f ∈ sin/cos/tan）。

    窗口包含判定要求两端点均为 π 的有理倍数；判不动保持原形（永不静默错）。
    """
    lo_q = _pi_coef(tlo)
    hi_q = _pi_coef(thi)
    if lo_q is None or hi_q is None:
        return w
    if lo_q > hi_q:
        lo_q, hi_q = hi_q, lo_q

    def _good(name):
        if name not in _POS_WINDOW:
            return False
        wlo, whi = _POS_WINDOW[name]
        return lo_q >= wlo and hi_q <= whi

    changed = True
    while changed:
        changed = False
        for p in T.all_paths(w):
            try:
                u = T.term_at(w, p)
            except IndexError:
                continue
            repl = None
            if isinstance(u, Expr) and u.head.name == "Abs" and len(u.args) == 1:
                a = u.args[0]
                if (isinstance(a, Expr) and a.head.name in _POS_WINDOW
                        and len(a.args) == 1 and a.args[0] is tvar and _good(a.head.name)):
                    repl = a
            elif (isinstance(u, Expr) and u.head.name == "Power"
                  and isinstance(u.args[1], T.Rat) and u.args[1].f == Fr(1, 2)):
                b = u.args[0]
                if (isinstance(b, Expr) and b.head.name == "Power"
                        and isinstance(b.args[1], T.Int) and b.args[1].v == 2):
                    a = b.args[0]
                    if (isinstance(a, Expr) and a.head.name in _POS_WINDOW
                            and len(a.args) == 1 and a.args[0] is tvar and _good(a.head.name)):
                        repl = a
            if repl is not None:
                w = T.replace_at(w, p, repl)
                changed = True
                break
    return w


def _auto_rewrite(w, rules, budget=40):
    """受限 auto 重写：全式遍历子项找命中，只跑 auto 规则，已见集防振荡。"""
    from cas.rules import apply_rule

    seen = {w._h}
    for _ in range(budget):
        moved = False
        for p in T.all_paths(w):
            try:
                sub = T.term_at(w, p)
            except IndexError:
                continue
            for r in rules.for_term(sub):
                if not r.auto:
                    continue
                res = apply_rule(r, w, p, None, 10000)
                if res.guard == "YES" and res.term is not w and res.term._h not in seen:
                    w = res.term
                    seen.add(w._h)
                    moved = True
                    break
            if moved:
                break
        if not moved:
            break
    return w


def _contains_imag(t):
    """term 是否含虚数单位 i（主支解带复根即无实原像）。"""
    stack = [t]
    while stack:
        u = stack.pop()
        if u is T.IU:
            return True
        if isinstance(u, Expr):
            stack.extend(u.args)
    return False


def bsub_defint(t, x, lo, hi, h, tvar, rules=None):
    """∫_lo^hi t dx 经 x = h(tvar) -> (值项 | None, 状态, 说明)。

    新限 = 主支逆解 h(tvar) = lo/hi；被积函数 f(h)·h' 化简后委托 defint。
    rules 给定时先跑受限 auto 重写（1−sin² -> cos² 类恒等式为脱根号铺路）。
    """
    from cas.diff import d as dd
    from cas.integrate import defint
    from cas.solve import solve

    def new_bound(c):
        r = solve(T.plus(h, T.neg(c)), tvar)
        if r.status != "ok" or not r.solutions:
            return None, "unsolved"
        sol = simplify(r.solutions[0])
        if _contains_imag(sol):
            # 主支逆无实原像：如 x=t² 在 x<0——换元值域不覆盖该限界。
            # 认清问题（域/满射），而非错误归因到限界不可比。
            return None, "no real preimage"
        return simplify(sol), None

    tlo, tnote = new_bound(lo)
    thi, _ = new_bound(hi)
    if tlo is None or thi is None:
        why = ("principal inverse has no real preimage (substitution x="
               f"{to_str(h)} does not cover the endpoint domain)")
        if tnote == "unsolved" or (tlo is None and thi is None and tnote is None):
            why = ("cannot solve substitution bounds via principal inverse "
                   "(need spec.inv coverage)")
        return None, "unsupported", why
    w = simplify(T.times(T.subst(t, {x: h}), dd(h, tvar)))
    if rules is not None:
        w = simplify(_auto_rewrite(w, rules))
    w = _resolve_sqrt_trig(w, tvar, tlo, thi)
    val, status, note = defint(w, tvar, tlo, thi)
    return val, status, f"backward substitution x={to_str(h)}: {note}"
