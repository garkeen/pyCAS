# -*- coding: utf-8 -*-
"""内核命令处理器（自 cas/session.py 拆出）：`!`/`:` 前缀命令的模块级
handler 函数 + 惰性形式求值助手。

约定：handler 只经 duck typing 调用 Session 能力（s.verify / s._kernel_step
等），不导入 Session 类——依赖单向，Session 侧组装门面见 cas/session.py。
"""

from dataclasses import dataclass

from cas import term as T
from cas.parser import parse
from cas.pprint import to_str
from cas.simplify import simplify, expand


@dataclass
class KernelCmd:
    """内核命令注册条目（机械算法黑盒快捷通道）。

    新增内核算法 = 注册一条 KernelCmd，REPL/帮助表自动可见，不再改分发代码。
    """
    help: str
    fn: object   # (session, rest: str) -> str


def _k_verify(s, rest):
    # 从末尾切两次：变量与目标式不含空格时 F 可含空格（% 展开后常见）
    parts = rest.rsplit(None, 2)
    if len(parts) != 3:
        return "usage: !verify <F> <x> <f>"
    return s.verify(*parts)


def _k_solve(s, rest):
    if not rest.strip():
        return "usage: !solve <expr> [var]"
    # 变量名只可能是末尾单个标识符：只从末尾分一次，避免切碎含空格的表达式
    parts = rest.rsplit(None, 1)
    if len(parts) == 2 and parts[1].isidentifier():
        return s.solve(parts[0], parts[1])
    return s.solve(rest.strip(), None)


def _k_factor(s, rest):
    if not rest.strip():
        return "usage: !factor <expr>"
    return s.factor(rest.strip())


def _k_apart(s, rest):
    args = rest.split()
    if len(args) != 2:
        return "usage: :apart <numerator> <denominator>"
    return s.apart(args[0], args[1])


def _k_integrate(s, rest):
    if not rest.strip():
        # 无参数：当前式是惰性积分则求值，否则提示用法
        if (s.current is not None and isinstance(s.current, T.Expr)
                and s.current.head.name == "Integrate"):
            return s.integrate_current()
        return "usage: !integrate <expr> [var]"
    parts = rest.rsplit(None, 1)
    # 当前式是惰性积分且单 token：对当前积分名词求值（∫f dt 的 f 已含换元变量）
    if (len(parts) == 1 and s.current is not None
            and isinstance(s.current, T.Expr) and s.current.head.name == "Integrate"):
        return s.integrate_current()
    if len(parts) == 2 and parts[1].isidentifier():
        return s.integrate(parts[0], parts[1])
    return s.integrate(rest.strip(), None)


def _k_limit(s, rest):
    parts = rest.rsplit(None, 2)
    if len(parts) != 3 or not parts[1].isidentifier():
        return "usage: !limit <expr> <var> <point>"
    return s.mlimit(parts[0], parts[1], parts[2])


def _k_series(s, rest):
    parts = rest.rsplit(None, 3)
    if len(parts) != 4 or not parts[1].isidentifier():
        return "usage: !series <expr> <var> <point> <order>"
    return s.mseries(parts[0], parts[1], parts[2], parts[3])


def _k_isteps(s, rest):
    """积分策略步树（manualintegrate 同款）：推导即数据，不执行计算。"""
    from cas.istrategy import explain, format_steps

    parts = rest.rsplit(None, 1)
    if not parts:
        return "usage: :isteps <expr> [var]"
    t = s._parse_in(parts[0])
    if len(parts) == 2 and parts[1].isidentifier():
        x = T.S(parts[1])
    else:
        vs = sorted(T.free_vars(t), key=lambda v: v.name)
        if len(vs) != 1:
            return "usage: :isteps <expr> <var> (expr has multiple variables)"
        x = vs[0]
    return "\n".join(format_steps(explain(t, x)))


def _k_dsolve(s, rest):
    """ODE 分类求解（题型命名入账，解回代微分回验）。"""
    parts = rest.rsplit(None, 2)
    if len(parts) < 2 or not parts[1].isidentifier():
        return "usage: !dsolve <equation with D(y,x)> <y> [x]"
    eq = s._parse_in(parts[0])
    y = T.S(parts[1])
    x = T.S(parts[2]) if len(parts) == 3 and parts[2].isidentifier() else T.S("x")
    if isinstance(eq, T.Expr) and eq.head.name == "Eq":
        f = T.plus(eq.args[0], T.neg(eq.args[1]))
    else:
        f = eq
    from cas.ode import dsolve

    r = dsolve(f, y, x)
    if r.sol is None:
        return f"unsupported: {r.note}"
    s._kernel_step(f"dsolve[{r.kind}]", r.sol, before=eq)
    if isinstance(r.sol, T.Expr) and r.sol.head.name == "Eq":
        out = to_str(r.sol)
    else:
        out = f"{y.name} = {to_str(r.sol)}"
        s._remember(r.sol)
    tail = f" ({r.note})" if r.note else ""
    return f"{out}   [{r.status}, kind: {r.kind}]{tail}"


def _k_defint(s, rest):
    parts = rest.rsplit(None, 3)
    if len(parts) != 4 or not parts[1].isidentifier():
        return "usage: !defint <expr> <var> <lo> <hi>"
    return s.mdefint(parts[0], parts[1], parts[2], parts[3])


def _k_sum(s, rest):
    """求和/差分（Faulhaber 幂和 + 不定/定界求和，差分回验）。"""
    from cas import summation

    if not rest.strip():
        if (s.current is not None and isinstance(s.current, T.Expr)
                and s.current.head.name == "Sum"):
            return s.value()
        return "usage: !sum <expr> <var> [<lo> <hi>]"
    # 定界：expr var lo hi（从右 rsplit 3 次，含空格的 expr 保留在 parts[0]）
    parts4 = rest.rsplit(None, 3)
    if len(parts4) == 4 and parts4[1].isidentifier():
        f = s._parse_in(parts4[0])
        x = T.S(parts4[1])
        lo = s._parse_in(parts4[2])
        hi = s._parse_in(parts4[3])
        S = summation.indef_sum(f, x)
        if S is None:
            return f"unsupported: {to_str(f)} not summable (polynomial terms only)"
        r = summation.finite_sum(f, x, lo, hi)
        ok = summation.verify_indef(S, f, x)
        before = s.current
        s.current = r
        s._kernel_step("sum[finite]", r, before=before)
        s._remember(r)
        return f"{to_str(r)}   [{'VERIFIED' if ok else 'UNVERIFIED'}, method: Faulhaber power sum]"
    # 不定：expr var
    parts2 = rest.rsplit(None, 1)
    if len(parts2) == 2 and parts2[1].isidentifier():
        f = s._parse_in(parts2[0])
        x = T.S(parts2[1])
        r = summation.indef_sum(f, x)
        if r is None:
            return f"unsupported: {to_str(f)} not summable (polynomial terms only)"
        ok = summation.verify_indef(r, f, x)
        before = s.current
        s.current = r
        s._kernel_step("sum[indef]", r, before=before)
        s._remember(r)
        return f"{to_str(r)}   [{'VERIFIED' if ok else 'UNVERIFIED'}, method: Faulhaber power sum]"
    return "usage: !sum <expr> <var> [<lo> <hi>]"


def _k_bsub(s, rest):
    """定积分反向换元：:bsub x=h(t) <expr> <var> <lo> <hi>（新限主支逆解）。"""
    parts = rest.split(None, 1)
    if len(parts) != 2 or "=" not in parts[0]:
        return "usage: :bsub x=h(t) <expr> <var> <lo> <hi>"
    eq = parse(parts[0])
    if not (isinstance(eq, T.Expr) and eq.head.name == "Eq" and isinstance(eq.args[0], T.Sym)):
        return "usage: :bsub x=h(t) <expr> <var> <lo> <hi>"
    x = eq.args[0]
    h = eq.args[1]
    tvs = T.free_vars(h)
    if len(tvs) != 1:
        return "bsub: substitution must contain exactly one new variable"
    tvar = sorted(tvs, key=lambda v: v.name)[0]
    r = parts[1].rsplit(None, 3)
    if len(r) != 4 or not r[1].isidentifier():
        return "usage: :bsub x=h(t) <expr> <var> <lo> <hi>"
    t = s._parse_in(r[0])
    lo = s._parse_bound(r[2])
    hi = s._parse_bound(r[3])
    from cas.bsub import bsub_defint

    val, status, note = bsub_defint(t, x, lo, hi, h, tvar, rules=s.rules)
    if val is None:
        return f"{status}: {note}"
    s._kernel_step(f"defint[{note}]", val, before=t)
    s._remember(val)
    return f"{to_str(val)}   [{status}, method: {note}]"


def _k_msolve(s, rest):
    idx = rest.find("]] ")
    if idx >= 0:
        spec = rest[: idx + 2]
        rhs = rest[idx + 3:].strip()
        if rhs.startswith("[") and rhs.endswith("]"):
            return s.msolve(spec, rhs)
    return "usage: !msolve [[a,b],[c,d]] [e,f]"


def _k_gsolve(s, rest):
    """!gsolve f1 && f2 && ... for x,y —— Groebner 消元求解多项式方程组。"""
    parts = rest.rsplit(" for ", 1)
    if len(parts) != 2:
        return "usage: !gsolve f1 && f2 && ... for x,y"
    try:
        tree = parse(parts[0].strip())
        vs = [T.S(v.strip()) for v in parts[1].split(",") if v.strip()]
    except Exception as e:
        return f"parse error: {e}"
    if not vs or len(set(id(v) for v in vs)) != len(vs):
        return "usage: !gsolve f1 && f2 && ... for x,y"
    fs = []

    def walk(t):
        if isinstance(t, T.Expr) and t.head.name == "And":
            for a in t.args:   # And 是 n 元头（AC flatten）
                walk(a)
        else:
            fs.append(t)

    walk(tree)
    if not fs:
        return "usage: !gsolve f1 && f2 && ... for x,y"
    from cas.groebner import solve_system

    r = solve_system(fs, tuple(vs))
    if r.status == "identity":
        return "identity: every point is a common zero"
    if r.status == "contradiction":
        return "contradiction: no common zero (1 in ideal)"
    if r.status == "positive-dim":
        return "positive-dimensional: " + r.note
    if r.status == "unsupported":
        return "unsupported: " + r.note
    # 解代回验证（证书：subst 全部原方程判零；Eq 归一 lhs-rhs）
    def _lhs(t):
        if isinstance(t, T.Expr) and t.head.name == "Eq":
            return T.plus(t.args[0], T.neg(t.args[1]))
        return t

    lines = []
    nver = 0
    for sol in r.solutions:
        assign = dict(zip(vs, sol))
        ok = True
        for f in fs:
            e = simplify(expand(T.subst(_lhs(f), assign)))
            if e is not T.ZERO:
                ok = False
                break
        nver += ok
        lines.append("(" + ", ".join(to_str(t) for t in sol) + ")")
    out = "; ".join(lines) if lines else "(no rational solutions enumerated)"
    if r.solutions:
        tag = "VERIFIED" if nver == len(r.solutions) else f"UNVERIFIED ({len(r.solutions)-nver}/{len(r.solutions)} failed)"
        out += f"   [{tag}]"
    if r.note:
        out += "   [note: " + r.note + "]"
    return "solutions (" + ",".join(v.name for v in vs) + "): " + out


def _k_together(s, rest):
    from cas import ops
    from cas.parser import parse as _parse

    if not rest.strip():
        return "usage: :together <expr>"
    return to_str(ops.together(_parse(rest.strip())))


def _k_collect(s, rest):
    from cas import ops
    from cas.parser import parse as _parse

    parts = rest.rsplit(None, 1)
    if len(parts) != 2 or not parts[1].isidentifier():
        return "usage: :collect <expr> <var>"
    return to_str(ops.collect(_parse(parts[0]), T.S(parts[1])))


def _k_num_den(kind):
    def fn(s, rest):
        from cas import ops
        from cas.parser import parse as _parse

        if not rest.strip():
            return f"usage: :{kind} <expr>"
        t = _parse(rest.strip())
        return to_str(ops.numerator(t) if kind == "numerator" else ops.denominator(t))
    return fn


def _k_coefficient(s, rest):
    from cas import ops
    from cas.parser import parse as _parse

    parts = rest.split()
    if len(parts) < 2:
        return "usage: :coefficient <expr> <var> [k]"
    k = int(parts[2]) if len(parts) > 2 else 1
    expr_s = " ".join(parts[:1])
    return to_str(ops.coefficient(_parse(expr_s), T.S(parts[1]), k))


def _k_mulfrac(kind):
    def fn(s, rest):
        from cas import ops
        from cas.domain import dom_condition
        from cas.decide import decide, T3
        from cas.parser import parse as _parse

        parts = rest.rsplit(None, 1)
        if len(parts) != 2:
            return f"usage: :{kind} <expr> <factor>"
        expr = _parse(parts[0])
        fac = _parse(parts[1])
        # 因子域检查：同乘检查 fac 域，同除检查 1/fac 域（含 fac≠0）。
        # NO 拒绝（域空，借用项恒无定义）；UNKNOWN 记 proviso（域收紧声明，
        # generic 不阻塞，事后可作答或验证）；YES 无条件。
        check = fac if kind == "mulfrac" else T.div(T.ONE, fac)
        provs = []
        for c in dom_condition(check):
            r = decide(c, s.ctx)
            if r is T3.NO:
                return (f"domain empty: factor {to_str(fac)} requires "
                        f"{to_str(c)} (contradicted)")
            if r is T3.UNKNOWN:
                if not any(c is p for p in provs):
                    provs.append(c)
        res = ops.mul_frac(expr, fac) if kind == "mulfrac" else ops.div_frac(expr, fac)
        s._kernel_step(kind, res, before=expr)
        out = to_str(res)
        if provs:
            out += "   [proviso: " + " && ".join(to_str(c) for c in provs) + "]"
        return out
    return fn


def _k_solveineq(s, rest):
    from cas.ineq import solve_poly_ineq
    from cas.parser import parse as _parse

    parts = rest.rsplit(None, 1)
    if len(parts) != 2 or not parts[1].isidentifier():
        return "usage: !solveineq <expr> <op> 0 <var>   (e.g. !solveineq x^2-1 > 0 x)"
    f = _parse(parts[0])
    if not (isinstance(f, T.Expr) and f.head.name in ("Gt", "Ge", "Lt", "Le")):
        return "need a comparison like x^2-1 > 0"
    if f.args[1] is not T.ZERO:
        return "right side must be 0"
    # Step 3：域守卫——Sturm 链假设 Fr 系数，超域结构化拒绝而非崩溃
    from cas.structure import analyze, CoeffBase
    _a = analyze(f.args[0], T.S(parts[1]))
    if _a.coeff is not CoeffBase.Q:
        return (f"solveineq: coefficient domain {_a.coeff} not supported "
                "(Sturm chain requires Q; parametric inequalities need "
                "CAD/VTS, pending M7d)")
    _ivs, out = solve_poly_ineq(f.args[0], f.head.name, T.S(parts[1]))
    return f"{parts[1]} in {out}"


def _k_solveset(s, rest):
    """解集一等结构：方程 -> FiniteSet，不等式 -> 区间并（solveset 形态）。"""
    from cas import sets as _sets

    parts = rest.rsplit(None, 1)
    if len(parts) != 2 or not parts[1].isidentifier():
        return "usage: !solveset <expr> <var>   (e.g. !solveset x^2 = 1 x / !solveset x^2-1 > 0 x)"
    f = s._parse_in(parts[0])
    var = T.S(parts[1])
    if isinstance(f, T.Expr) and f.head.name in ("Lt", "Le", "Gt", "Ge"):
        if f.args[1] is not T.ZERO:
            f = T.mk(T.S(f.head.name), (T.plus(f.args[0], T.neg(f.args[1])), T.ZERO))
        st, note = _sets.ineq_set(f.args[0], f.head.name, var)
        if st is None:
            return f"honest refusal: {note}"
        return f"{parts[1]} in {to_str(st)}"
    try:
        st, provisos = _sets.solve_set(f, var)
    except ValueError as e:
        return f"unsupported: {e}"
    out = f"{parts[1]} in {to_str(st)}"
    if provisos:
        out += "   [provisos: " + ", ".join(to_str(p) for p in provisos) + "]"
    return out


def _eval_inert(t, budget):
    """单树求值惰性头（Quote 脱壳、惰性 Integrate 实算、D 名词微分）-> (新项, changed)。

    求值失败（如不可积）的惰性头保持名词（诚实）。value() 全式遍历用它，
    value_at() 单点复用——整体操作与子项操作同一套语义。
    """
    from cas.diff import d as dd
    from cas.integrate import integrate as zz_int
    from cas.errors import PolyError
    from cas.risch import RischUnsupported

    changed = False
    order = []
    stack = [t]
    while stack:
        u = stack.pop()
        order.append(u)
        if isinstance(u, T.Expr):
            stack.extend(u.args)
        elif isinstance(u, T.Bound):
            stack.append(u.body)
    val = {}
    for u in reversed(order):
        if isinstance(u, T.Bound):
            val[u] = T._mk_bound_canon(u.hint, val[u.body])
            continue
        if not isinstance(u, T.Expr):
            val[u] = u
            continue
        args = tuple(val[a] for a in u.args)
        name = u.head.name
        r = None
        if name == "Quote":
            r = args[0]
        elif name == "Integrate" and len(args) == 1 and isinstance(args[0], T.Bound):
            x, body = T.open_bound(args[0])
            try:
                r = zz_int(body, x)[0]
            except (PolyError, RischUnsupported):
                r = None   # 不可积：保持名词
        elif name == "Sum" and len(args) == 1 and isinstance(args[0], T.Bound):
            from cas import summation
            x, body = T.open_bound(args[0])
            r = summation.indef_sum(body, x)
        elif name == "D" and len(args) == 2:
            r = dd(args[0], args[1])
        if r is not None:
            val[u] = r
            changed = True
        elif any(a is not b for a, b in zip(args, u.args)):
            val[u] = T.mk(u.head, args)
        else:
            val[u] = u
    return val[t], changed


def _quotient_cancel(num, den):
    """num/den：顶层乘法因子按驻留指针消去（不展开乘积、不做多项式除法）。

    整数指数幂拆到底（(a*b)^n 因子化），同名因子指数相抵，数值因子有理折叠。
    存在理由：mk 不拆 (a*b)^-1（非整数指数分支切割安全），直接 T.div 会留
    (g'(x))^-1 残渣导致换元探测失败（:usub 精确微分分解依赖此消去）。
    """
    from fractions import Fraction

    def flat(t, mul=1, acc=None):
        if acc is None:
            acc = []
        if isinstance(t, T.Expr) and t.head.name == "Times":
            for a in t.args:
                flat(a, mul, acc)
        elif isinstance(t, T.Expr) and t.head.name == "Power" \
                and isinstance(t.args[1], T.Int):
            acc.append((t.args[0], mul * t.args[1].v))
        else:
            acc.append((t, mul))
        return acc

    nf, df = flat(num), flat(den)
    cval = Fraction(1)
    for f, e in nf:
        if T.is_num(f):
            cval *= T.num_val(f) ** e
    for f, e in df:
        if T.is_num(f):
            cval /= T.num_val(f) ** e
    cnt = {}
    for f, e in nf:
        if not T.is_num(f):
            cnt[f] = cnt.get(f, 0) + e
    for f, e in df:
        if not T.is_num(f):
            cnt[f] = cnt.get(f, 0) - e
    parts = []
    if cval != 1:
        parts.append(T.N(cval))
    for f, e in cnt.items():
        if e == 0:
            continue
        parts.append(f if e == 1 else T.pw(f, T.N(e)))
    if not parts:
        return T.ONE
    return T.mk(T.S("Times"), tuple(parts))


def _neg_pow_of(t, f):
    """t 中是否存在底恰为 f 的负整数幂（整除性残留检测）。"""
    stack = [t]
    while stack:
        u = stack.pop()
        if isinstance(u, T.Expr):
            if (u.head.name == "Power" and u.args[0] is f
                    and isinstance(u.args[1], T.Int) and u.args[1].v < 0):
                return True
            stack.extend(u.args)
        elif isinstance(u, T.Bound):
            stack.append(u.body)
    return False


def _const_exact(v):
    """纯常数项（数字+虚单位）精确折叠为规范项；含自由变量返回 None。

    msolve 解分量规范化用——ℚ(i) 常数分量 2*i/(-2*i) -> -1 类。"""
    import cas.term as T
    from cas.gaussian import Ga

    if T.free_vars(v):
        return None
    try:
        g = Ga.from_term_val(v)
        return g.to_term()
    except Exception:
        return None
