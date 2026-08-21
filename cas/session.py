import os

from dataclasses import dataclass, field

from cas import term as T
from cas import context as context_mod
from cas.decide import (
    eval_guard as _eval_guard,
    decide as _decide_fn,
    contradicted as _contradicted_fn,
    equivalent as _equivalent_fn,
    T3,
)
from cas.context import Context
from cas.parser import parse
from cas.pprint import to_str
from cas.rules import Rule, RuleSet, Step, apply_rule
from cas.simplify import simplify, cost, expand
from cas.errors import BudgetExceeded, ParseError
from cas import loader
from cas import spec as _spec


@dataclass
class Obligation:
    oid: int
    question: T.Term
    affects: list
    note: str = ""
    pending: list = field(default_factory=list)


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
            except PolyError:
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


class Session:
    def __init__(self, budget=100000):
        self.current = None
        self.log = []
        self.obligations = []
        self.ctx = Context()
        self.rules = RuleSet()
        self.budget = budget
        self.locked = None
        self.load_error = None
        self.history = []   # 产出过的表达式（%N 复用，REPL 交互标配）
        self.transcript = []  # 命令转录（DSL：可保存/可回放，计算可复现的地基）
        self.defs = {}      # 用户定义：头名/变量名 -> (参数元组, 体)；空参 = 变量
        self._sid = 0
        self._oid = 0
        rules_dir = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "rules")
        if os.path.isdir(rules_dir):
            try:
                loader.load_dir(rules_dir, self.rules)
            except Exception as e:
                # 不静默吞错：记录并在 REPL 报告（永不静默错原则）
                self.load_error = f"{e.__class__.__name__}: {e}"
        # FunctionSpec 自动生成的规则（奇偶性等，origin='spec'）
        _spec.gen_rules(self.rules)
        # 手动算法命令（: 前缀；用户主动触发，结果入账可撤销）
        self.kernel = {
            "apart": KernelCmd("apart <num> <den>", _k_apart),
            "isteps": KernelCmd("isteps <expr> [var] (strategy step tree)", _k_isteps),
            "bsub": KernelCmd("backward sub: :bsub x=h(t) <expr> <var> <lo> <hi>", _k_bsub),
            "together": KernelCmd("together <expr> (common denominator)", _k_together),
            "collect": KernelCmd("collect <expr> <var>", _k_collect),
            "numerator": KernelCmd("numerator <expr>", _k_num_den("numerator")),
            "denominator": KernelCmd("denominator <expr>", _k_num_den("denominator")),
            "mulfrac": KernelCmd("mulfrac <expr> <factor> (multiply num&den)", _k_mulfrac("mulfrac")),
            "divfrac": KernelCmd("divfrac <expr> <factor> (divide num&den)", _k_mulfrac("divfrac")),
            "coefficient": KernelCmd("coefficient <expr> <var> [k]", _k_coefficient),
        }
        # 自动求解命令（! 前缀；算法黑盒直出，verify 背书）
        self.solver = {
            "verify": KernelCmd("verify <F> <x> <f>", _k_verify),
            "solve": KernelCmd("solve <expr> [var]", _k_solve),
            "factor": KernelCmd("factor <expr>", _k_factor),
            "integrate": KernelCmd("integrate <expr> [var] (var required for multi-variable expr)", _k_integrate),
            "dsolve": KernelCmd("dsolve <eq with D(y,x)> <y> [x]", _k_dsolve),
            "limit": KernelCmd("limit <expr> <var> <point> (point may be +/-inf)", _k_limit),
            "series": KernelCmd("series <expr> <var> <point> <order> (Taylor + O term)", _k_series),
            "defint": KernelCmd("defint <expr> <var> <lo> <hi>", _k_defint),
            "sum": KernelCmd("sum <expr> <var> [<lo> <hi>] (Faulhaber power sum + diff verify)", _k_sum),
            "mat": KernelCmd("show matrix [[a,b],[c,d]]", lambda s, r: s.mat(r.strip())),
            "mdet": KernelCmd("determinant [[a,b],[c,d]]", lambda s, r: s.mdet(r.strip())),
            "mrank": KernelCmd("rank [[a,b],[c,d]]", lambda s, r: s.mrank(r.strip())),
            "minv": KernelCmd("inverse [[a,b],[c,d]]", lambda s, r: s.minv(r.strip())),
            "msolve": KernelCmd("solve system: !msolve [[a,b],[c,d]] [e,f]", _k_msolve),
            "charpoly": KernelCmd("charpoly [[a,b],[c,d]] = det(lam*I - M)", lambda s, r: s.mcharpoly(r.strip())),
            "eigenvalues": KernelCmd("eigenvalues [[a,b],[c,d]]", lambda s, r: s.meigenvalues(r.strip())),
            "eigenvectors": KernelCmd("eigenvectors [[a,b],[c,d]]", lambda s, r: s.meigenvectors(r.strip())),
            "solveineq": KernelCmd("solveineq <expr> <op> 0 <var>", _k_solveineq),
            "solveset": KernelCmd("solveset <expr> <var> (set-valued solutions)", _k_solveset),
        }

    def _check_locked(self):
        if self.locked:
            raise ValueError(f"session locked: {self.locked} (ex falso; undo or start over)")

    def feed(self, s):
        self._check_locked()
        self.current = self._expand_defs(parse(s), bare_ok=True)
        self._remember(self.current)
        return self.current

    # ---------------- 用户定义（交互式 CAS 标配：f(x) := 体 / a := 体） ----------------

    # Protected 属性（mathics attributes.py 同款）：内建头一律拒绝覆盖。
    # 清单纪律：新增结构头/绑定词头时必须同步加入（代码评审验收点）。
    _RESERVED = {"Plus", "Times", "Power", "Eq", "Ne", "Lt", "Le", "Gt", "Ge",
                 "And", "Or", "Not", "Bound", "Quote", "D", "Attr", "Piecewise",
                 "Integrate", "Sum", "Product", "Limit", "Conjugate", "RootOf",
                 "Infinity", "Undefined", "FiniteSet", "Interval", "Union", "O"}
    # Sqrt 由 parser 直重写为 Power，无此头

    def _check_def_name(self, name):
        from cas.spec import SPECS

        # 裸符号不capitalize（Sym 保持原名），但函数头会首字母大写——
        # 两种形态都不得与保留头/spec 头冲突
        cap = name[0].upper() + name[1:] if len(name) > 1 else name
        if name in self._RESERVED or cap in self._RESERVED or name in SPECS or cap in SPECS:
            raise ParseError(f"cannot redefine built-in: {name}")

    def define(self, sig_s, body_s):
        """函数定义 f(x, y) := 体：feed 时对 f(...) 出现做宏展开（参数代入）。"""
        sig = parse(sig_s)
        if not (isinstance(sig, T.Expr) and sig.args and all(isinstance(a, T.Sym) for a in sig.args)):
            raise ParseError("usage: name(x, y) := expr")
        name = sig.head.name
        self._check_def_name(name)
        self.defs[name] = (tuple(sig.args), parse(body_s))
        return f"defined: {name}({', '.join(a.name for a in sig.args)})"

    def assign(self, name_s, body_s):
        """变量定义 a := 体：feed 时对同名符号全局代入（宏语义，非方程）。"""
        v = parse(name_s)
        if not isinstance(v, T.Sym):
            raise ParseError("usage: name := expr")
        self._check_def_name(v.name)
        self.defs[v.name] = ((), parse(body_s))
        return f"assigned: {v.name}"

    def undef(self, name_s):
        v = parse(name_s)
        nm = v.head.name if isinstance(v, T.Expr) else getattr(v, "name", None)
        if nm in self.defs:
            del self.defs[nm]
            return f"undefined: {nm}"
        return f"no definition: {name_s}"

    def _subst_defs(self, t):
        """单遍定义展开（显式栈后序重建）：函数头按参数代入，变量直接替换。

        保指针重建：子项无变化时复用原节点（Bound 不驻留，每次重建都生新指针，
        不复用会导致不动点判等失效）。
        """
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
            if isinstance(u, T.Expr):
                new_args = tuple(val[a] for a in u.args)
                d_ = self.defs.get(u.head.name)
                if d_ is not None and len(d_[0]) == len(new_args):
                    val[u] = T.subst(d_[1], dict(zip(d_[0], new_args)))
                elif all(na is oa for na, oa in zip(new_args, u.args)):
                    val[u] = u
                else:
                    val[u] = T.mk(u.head, new_args)
            elif isinstance(u, T.Bound):
                nb = val[u.body]
                val[u] = u if nb is u.body else T._mk_bound_canon(u.hint, nb)
            else:
                d_ = self.defs.get(u.name, None) if isinstance(u, T.Sym) else None
                val[u] = d_[1] if d_ is not None and d_[0] == () else u
        return val[t]

    def _expand_defs(self, t, bare_ok=False):
        """定义展开到不动点；轮数上限兼防递归定义死循环（永不静默错）。

        bare_ok=False 时裸符号不展开（内核参数位，变量名作主语优先）；
        feed 交互输入 bare_ok=True（变量定义求值语义，函数定义仍需调用才展开）。
        """
        if not self.defs or (isinstance(t, T.Sym) and not bare_ok):
            return t
        for _ in range(20):
            nxt = self._subst_defs(t)
            if nxt is t:
                return t
            t = nxt
        raise BudgetExceeded(message="definition expansion too deep (recursive definition?)")

    def _remember(self, t):
        if isinstance(t, T.Term) and t not in (T.ZERO, T.ONE):
            self.history.append(t)

    def expand_history(self, line):
        """%N 引用第 N 个历史产出，裸 % 引用最近一个（Mathematica %/%% 同款最小版）。

        插入位置上下文未知，按最高优先级渲染补括号（多和项嵌入乘法不破语义）。"""
        import re

        def rep(m):
            n = m.group(1)
            if not n:
                if not self.history:
                    raise ParseError("no history yet")
                t = self.history[-1]
            else:
                i = int(n)
                if not (1 <= i <= len(self.history)):
                    raise ParseError(f"no history %{i} (have {len(self.history)})")
                t = self.history[i - 1]
            return to_str(t, prec=99, src=True)

        return re.sub(r"%(\d*)", rep, line)

    def _parse_in(self, s):
        """会话内输入统一入口：解析 + 用户定义展开。

        裸符号豁免：内核参数位裸符号常作主语（如 !integrate f 的积分变量），
        变量名优先于宏语义。
        """
        return self._expand_defs(parse(s), bare_ok=False)

    def _guard_eval(self, guard, sub):
        return _eval_guard(guard, sub, self.ctx)

    def suggest(self, path=None):
        if self.current is None:
            return []
        paths = [tuple(path)] if path is not None else list(T.all_paths(self.current))
        out = []
        for p in paths:
            tgt = T.term_at(self.current, p)
            for r in self.rules.for_term(tgt):
                res = apply_rule(r, self.current, p, self._guard_eval)
                if res.guard in ("YES", "UNKNOWN"):
                    out.append((r.id, res.guard, p))
        return out

    def apply(self, rid, path=None):
        """应用规则。path=None 时自动全式搜索首个匹配位置（规则主路径，
        不再要求用户手工指定路径）。返回新项；不适用时返回说明字符串。"""
        self._check_locked()
        r = self.rules.rules.get(rid)
        if r is None:
            return f"no rule {rid}"
        if path is None:
            if self.current is None:
                return "empty session"
            found = None
            for p in T.all_paths(self.current):
                res = apply_rule(r, self.current, p, self._guard_eval, self.budget)
                if res.guard != "NOMATCH":
                    found = (p, res)
                    break
            if found is None:
                return f"rule {rid} does not match anywhere"
            path, res = found
        else:
            res = apply_rule(r, self.current, path, self._guard_eval, self.budget)
        if res.guard == "NOMATCH":
            return f"rule {rid} does not match at {path}"
        if res.guard == "UNKNOWN":
            self._oid += 1
            q = T.instantiate(r.guard, res.subst)
            obl = Obligation(self._oid, q, [self._sid + 1], note=f"guard of {rid}")
            obl.pending.append({"rule": rid, "path": tuple(path)})
            self.obligations.append(obl)
            return f"guard UNKNOWN: {to_str(q)}  (obligation #{self._oid} created; answer then :ans {self._oid} <fact>)"
        return self._commit(r, path, res)

    def _commit(self, r, path, res):
        """提交一次已计算好的规则应用（res 必须是在 self.current 上算出的）。

        提交后 remember 当前式：规则应用也产出可引用表达式（% 指向最近推导结果，
        而非 feed 时的原始式；Mathematica Out 语义同款）。
        """
        self._sid += 1
        before = self.current
        self.current = res.term
        st = Step(self._sid, r.id, tuple(path), before, self.current, res.guard, cost(res.term) - cost(before))
        self.log.append(st)
        self._remember(self.current)
        if r.guard is not None:
            g = T.instantiate(r.guard, res.subst)
            cst, _ = self.ctx.check_and_assume(g, origin=f"step{self._sid}", kind="guard")
            if cst is T3.NO:
                self.locked = f"contradiction after step {self._sid}"
        return self.current

    def _eq_rewrite_step(self):
        """等式即规则：账本等式双向替换，仅接受 cost 严格下降（防循环）。"""
        for e in self.ctx.entries:
            f = e.fact
            if not (isinstance(f, T.Term) and isinstance(f, T.Expr) and f.head.name == "Eq"):
                continue
            u, v = f.args
            for pat, rep in ((u, v), (v, u)):
                nxt = T.subst(self.current, {pat: rep})
                if nxt is self.current:
                    continue
                if cost(nxt) < cost(self.current):
                    self._sid += 1
                    self.log.append(Step(
                        self._sid, f"eq[{e.origin}]", (), self.current, nxt, "YES",
                        cost(nxt) - cost(self.current),
                    ))
                    self.current = nxt
                    return True
        return False

    def auto(self):
        """自动重写：构造器规范化 + 账本等式 + auto 规则，cost 不增才接受，每步入 step log。

        停机保证：cost 单调不增（等式替换严格下降）+ 已见项集合防振荡 + 轮数上限。
        """
        self._check_locked()
        if self.current is None:
            return None
        auto_rules = sorted(
            (r for r in self.rules.rules.values() if r.auto),
            key=lambda r: r.priority,
        )
        seen = {self.current._h}
        for _ in range(10):
            s0 = simplify(self.current, self.budget)
            if s0 is not self.current:
                self._sid += 1
                self.log.append(Step(
                    self._sid, "norm", (), self.current, s0, "YES",
                    cost(s0) - cost(self.current),
                ))
                self.current = s0
                seen.add(s0._h)
            if self._eq_rewrite_step():
                seen.add(self.current._h)
                continue
            changed = False
            for p in T.all_paths(self.current):
                try:
                    T.term_at(self.current, p)
                except IndexError:
                    continue
                for r in auto_rules:
                    res = apply_rule(r, self.current, p, self._guard_eval, self.budget)
                    if res.guard != "YES":
                        continue
                    if res.term._h in seen:
                        continue
                    if cost(res.term) <= cost(self.current):
                        self._commit(r, p, res)
                        seen.add(res.term._h)
                        changed = True
                        break
                if changed:
                    break
            if not changed:
                break
        return self.current

    def assume(self, s):
        f = self._parse_in(s)
        st, why = self.ctx.check_and_assume(f, origin="user")
        if st is T3.NO:
            if why == "domain":
                return f"domain empty: {to_str(f)} is not defined on the real line"
            self.locked = f"contradiction: {to_str(f)} vs ledger"
            return f"CONTRADICTION LOCKED: {self.locked}"
        return f"assumed: {to_str(f)}"

    def declare(self, var_s, prop):
        """声明变量属性（属性入 ledger，kind='attr'，decide 区间通道消费）。

        符号类属性（positive/negative/nonnegative/nonpositive）映射为不等式事实；
        离散类属性（integer/even/odd/real）存为 Attr 条目（even/odd 隐含 integer）。
        """
        v = T.S(var_s)
        prop = prop.lower()
        sign_map = {
            "positive": T.gt(v, T.ZERO),
            "negative": T.lt(v, T.ZERO),
            "nonnegative": T.ge(v, T.ZERO),
            "nonpositive": T.le(v, T.ZERO),
        }
        if prop in sign_map:
            return self._assume_fact(sign_map[prop])
        if prop in ("integer", "real", "even", "odd"):
            props = ["integer", prop] if prop in ("even", "odd") else [prop]
            for p in props:
                st, why = self.ctx.check_and_assume(
                    T.mk(T.S("Attr"), (v, T.S(p))), origin="user", kind="attr"
                )
                if st is T3.NO:
                    return f"declaration rejected ({why}): {var_s} {p}"
            return f"declared: {var_s} {prop}"
        return f"unknown property: {prop}"

    def _assume_fact(self, f):
        st, why = self.ctx.check_and_assume(f, origin="user")
        if st is T3.NO:
            if why == "domain":
                return f"domain empty: {to_str(f)} is not defined on the real line"
            self.locked = f"contradiction: {to_str(f)} vs ledger"
            return f"CONTRADICTION LOCKED: {self.locked}"
        return f"assumed: {to_str(f)}"

    def answer(self, oid, s):
        self._check_locked()
        f = self._parse_in(s)
        obl = next((o for o in self.obligations if o.oid == oid), None)
        if obl is None:
            return f"no obligation #{oid}"
        st, why = self.ctx.check_and_assume(f, origin=f"obl{oid}", kind="answer")
        if st is T3.NO:
            if why == "domain":
                return f"domain empty: {to_str(f)} is not defined on the real line"
            return f"answer rejected: {to_str(f)} contradicts ledger"
        pending = list(obl.pending)
        for p in pending:
            rid = p["rule"]
            r = self.rules.rules.get(rid)
            if r is None:
                obl.pending.remove(p)
                continue
            # 重放用全式搜索（旧 path 可能因期间变换失效）
            found = None
            for path in T.all_paths(self.current):
                res = apply_rule(r, self.current, path, self._guard_eval, self.budget)
                if res.guard != "NOMATCH":
                    found = (path, res)
                    break
            if found is None:
                obl.pending.remove(p)
                continue
            path, res = found
            if res.guard == "YES":
                self._commit(r, path, res)
                obl.pending.remove(p)
        if not obl.pending:
            if obl in self.obligations:
                self.obligations.remove(obl)
            return f"answered #{oid}: {to_str(f)}"
        return f"answered #{oid} (assumed); obligation kept: still undecidable"

    def undo(self, n=1):
        for _ in range(n):
            if not self.log:
                return
            st = self.log.pop()
            self.current = st.before
            self.ctx.drop_origin(f"step{st.sid}")
            # 撤掉引发矛盾锁的那一步 -> 解锁
            if self.locked and f"step {st.sid}" in self.locked:
                self.locked = None
        return self.current

    def replay(self, from_sid=0):
        steps = [s for s in self.log if s.sid > from_sid]
        base = next((s.before for s in self.log if s.sid == from_sid), None)
        if base is None and from_sid == 0:
            base = self.log[0].before if self.log else None
        if base is None:
            return "nothing to replay"
        # 清旧 step 账本条目（重放会重新入账，防陈旧事实累积）
        self.ctx.entries = [
            e for e in self.ctx.entries
            if not (isinstance(e.origin, str) and e.origin.startswith("step"))
        ]
        self.current = base
        for st in steps:
            if st.rule_id.startswith("kernel:"):
                # 内核算法步：不可规则重放，直接恢复其输出（正确性由 verify 背书）
                self.current = st.after
                continue
            r = self.rules.rules.get(st.rule_id)
            if r is None:
                return f"replay stuck at {st.rule_id}"
            res = apply_rule(r, self.current, st.path, self._guard_eval, self.budget)
            if res.guard != "YES":
                return f"replay diverged at step {st.sid} ({res.guard})"
            self._commit(r, st.path, res)
        return self.current

    def verify(self, Fs, xs, fs):
        from cas.diff import verify

        F = self._parse_in(Fs)
        x = parse(xs)
        f = self._parse_in(fs)
        return verify(F, x, f, self.budget)

    def solve(self, fs, vs=None):
        from cas.solve import solve, check_solution

        f = self._parse_in(fs)
        if vs:
            var = T.S(vs)
        else:
            var = None
            for p in T.all_paths(f):
                t = T.term_at(f, p)
                if isinstance(t, T.Sym) and t.name not in ("e", "pi"):
                    var = t
                    break
        if var is None:
            return "no variable to solve for"
        r = solve(f, var, self.budget)
        if r.status == "identity":
            return "identity: 0 = 0 for all " + var.name
        if r.status == "contradiction":
            return "contradiction: no solution"
        if r.status == "unsupported":
            return "unsupported: " + (r.note or "cannot solve")
        out = ", ".join(to_str(s_) for s_ in r.solutions) or "(none)"
        # 解代回验证（check_solution 接入管线——此前存在但未被调用）
        tag = None
        if r.solutions:
            checks = [check_solution(f, sol, var) for sol in r.solutions]
            if all(c == "VERIFIED" for c in checks):
                tag = "VERIFIED"
            else:
                bad = sum(1 for c in checks if c != "VERIFIED")
                tag = f"UNVERIFIED ({bad}/{len(checks)} solutions failed substitution)"
        if r.provisos:
            out += "   [proviso: " + " && ".join(to_str(g) for g in r.provisos) + "]"
        if tag:
            out += f"   [{tag}]"
        return var.name + " = " + out

    def mat(self, spec):
        from cas.matrix import Matrix

        return Matrix.parse(spec).show()

    def mdet(self, spec):
        from cas.matrix import Matrix
        from cas.pprint import to_str

        return to_str(Matrix.parse(spec).det())

    def mrank(self, spec):
        from cas.matrix import Matrix

        return str(Matrix.parse(spec).rank())

    def minv(self, spec):
        from cas.matrix import Matrix

        m = Matrix.parse(spec)
        inv_m = m.inv()
        if inv_m is None:
            return "singular"
        # 证书检查：M·M^-1 == I（逐项指针比对，驻留免费）
        prod = m.mul(inv_m)
        n = len(m.rows)
        ok = all(prod.rows[i][j] is (T.ONE if i == j else T.ZERO)
                 for i in range(n) for j in range(n))
        return inv_m.show() + f"   [{'VERIFIED' if ok else 'UNVERIFIED'}, M*M^-1 = I]"

    def msolve(self, spec, rhs):
        from cas.matrix import Matrix
        from cas.parser import parse
        from cas.pprint import to_str

        b = [parse(c.strip()) for c in rhs.strip()[1:-1].split(",")]
        m = Matrix.parse(spec)
        r = m.solve(b)
        if r.unique is not None:
            # 证书检查：M·x == b（逐行内积代回）
            ok = True
            for i, row in enumerate(m.rows):
                acc = T.ZERO
                for cell, v in zip(row, r.unique):
                    acc = T.plus(acc, T.times(cell, v))
                if simplify(acc) is not b[i]:
                    ok = False
                    break
            out = ", ".join(
                f"x{i + 1} = {to_str(v)}" for i, v in enumerate(r.unique)
            )
            return out + f"   [{'VERIFIED' if ok else 'UNVERIFIED'}, M*x = b]"
        if r.particular is None:
            return "no solution"
        parts = ", ".join(f"x{i + 1} = {to_str(v)}" for i, v in enumerate(r.particular))
        basis = "; ".join(
            "(" + ", ".join(to_str(v) for v in vec) + ")" for vec in r.null_basis
        )
        return f"infinite: {parts}  + t*({basis})"

    def mcharpoly(self, spec):
        from cas.matrix import Matrix

        t, lam = Matrix.parse(spec).charpoly()
        return f"{to_str(t)}   (in {lam.name})"

    def meigenvalues(self, spec):
        from cas.matrix import Matrix

        m = Matrix.parse(spec)
        t, lam = m.charpoly()
        r = m.eigenvalues()
        if r.status == "ok":
            # 证书检查：charpoly(lambda_i) == 0（逐个代回 + 展开归零）
            ok = all(
                simplify(expand(T.subst(t, {lam: val}))) is T.ZERO
                for val in r.solutions
            )
            out = ", ".join(to_str(v) for v in r.solutions) or "(none)"
            if r.provisos:
                out += "   [proviso: " + " && ".join(to_str(g) for g in r.provisos) + "]"
            return out + f"   [{'VERIFIED' if ok else 'UNVERIFIED'}, charpoly(lambda) = 0]"
        return "unsupported: " + (r.note or r.status)

    def meigenvectors(self, spec):
        from cas.matrix import Matrix, MatrixError

        try:
            pairs = Matrix.parse(spec).eigenvectors()
        except MatrixError as e:
            return str(e)
        lines = []
        for v, basis in pairs:
            vecs = "; ".join("(" + ", ".join(to_str(c) for c in b) + ")" for b in basis)
            lines.append(f"lam = {to_str(v)}: {vecs or '(none found)'}")
        return "\n".join(lines)

    def _pick_var(self, t):
        for p in T.all_paths(t):
            v = T.term_at(t, p)
            if isinstance(v, T.Sym) and v.name not in ("e", "pi"):
                return v
        return None

    def factor(self, s):
        """因式分解 + 乘回验证（证书检查：展开积与原式归零比对，比重算更廉价）。"""
        from cas.factor import factor as zz_factor
        from cas.poly import Poly

        t = self._parse_in(s)
        x = self._pick_var(t)
        if x is None:
            return "no variable"
        p = Poly.from_term(t, (x,))
        c, factors = zz_factor(p)
        prod = T.N(c) if c != 1 else T.ONE
        for g, m in factors:
            base = g.to_term()
            for _ in range(m):
                prod = T.times(prod, base)
        ok = simplify(expand(prod)) is t or \
            simplify(T.plus(expand(prod), T.neg(t))) is T.ZERO
        out = []
        if c != 1:
            out.append(str(c))
        for g, m in factors:
            s_ = str(g)
            if "+" in s_ or "-" in s_[1:]:
                s_ = f"({s_})"
            out.append(f"{s_}^{m}" if m > 1 else s_)
        body = " * ".join(out) if out else str(c)
        return f"{body}   [{'VERIFIED' if ok else 'UNVERIFIED'}, method: Zassenhaus]"

    def apart(self, num_s, den_s):
        from cas.poly import Poly
        from cas.apart import apart as zz_apart, apart_term, find_atom
        from cas.pprint import to_str as ps

        t1 = self._parse_in(num_s)
        t2 = self._parse_in(den_s)
        atom = find_atom(t1, t2)
        if atom is not None:
            # 复合项作原子变量（如 Log(x)）：多项式除法推广到非多项式头
            res = apart_term(t1, t2, atom)
            self._kernel_step("apart[composite-atom]", res, before=T.div(t1, t2))
            return ps(res)
        x = self._pick_var(t1) or self._pick_var(t2)
        if x is None:
            return "no variable"
        f = Poly.from_term(t1, (x,))
        g = Poly.from_term(t2, (x,))
        q, terms = zz_apart(f, g)
        out = []
        if not q.is_zero():
            out.append(str(q))
        for nn, dd, k in terms:
            s_ = f"({nn})/({dd})"
            out.append(f"{s_}^{k}" if k > 1 else s_)
        return " + ".join(out) if out else "0"

    def _kernel_step(self, algo, result, before=None):
        """内核算法调用入账：单算法调用不做微观步骤解释（正确性由 verify 背书），
        只记算法名 + 输入/输出 + 验证态（可解释性的最小诚实单位）。
        命令结果同时成为当前表达式（公式区展示，可继续交互）。"""
        self._sid += 1
        self.log.append(Step(
            self._sid, "kernel:" + algo, (), before, result, "YES", 0,
            note=f"algorithm={algo}",
        ))
        self._remember(result)
        self.current = result

    def integrate_current(self):
        """对当前惰性积分名词求值（∫f dt 的 f 已含换元变量；等价 :value 的积分分支）。

        与 !integrate <expr> 区分：<expr> 指被积式；此处求值 current 本身。
        """
        from cas.integrate import integrate as zz_int
        from cas.pprint import to_str as ps

        if not (isinstance(self.current, T.Expr) and self.current.head.name == "Integrate"
                and len(self.current.args) == 1 and isinstance(self.current.args[0], T.Bound)):
            return "integrate: current is not an inert integral"
        x, body = T.open_bound(self.current.args[0])
        try:
            res, ok, method, provisos = zz_int(body, x)
        except Exception as e:
            return f"integrate: {type(e).__name__}: {e}"
        self._kernel_step(f"integrate[{method}]", res, before=self.current)
        tag = "VERIFIED" if ok else "UNVERIFIED"
        out = f"{ps(res)}   [{tag}, method: {method}]"
        if provisos:
            out += "   [proviso: " + " && ".join(to_str(g) for g in provisos) + "]"
        return out

    def integrate(self, s, var_s=None):
        from cas.integrate import integrate as zz_int
        from cas.pprint import to_str as ps

        t = self._parse_in(s)
        if var_s:
            x = T.S(var_s)
            if x not in T.free_vars(t):
                return f"integrate: variable {var_s} not in expression"
        else:
            vs = sorted(T.free_vars(t), key=lambda v: v.name)
            if len(vs) != 1:
                n = str(len(vs)) if vs else "no"
                return f"integrate: specify the integration variable (expr has {n} free variable)"
            x = vs[0]
        res, ok, method, provisos = zz_int(t, x)
        self._kernel_step(f"integrate[{method}]", res, before=t)
        out = ps(res)
        tag = "VERIFIED" if ok else "UNVERIFIED"
        out = f"{out}   [{tag}, method: {method}]"
        if provisos:
            out += "   [proviso: " + " && ".join(to_str(g) for g in provisos) + "]"
        return out

    def _limit_probe(self, t, x, pt, claimed):
        """极限数值探针（仅验证/抽查通道，只产一致/未知，绝不产否证）。

        检验收敛趋势（极限定义的数值形态）：双侧误差 |f(a±d)-L| 随 d 缩小
        而缩小。±inf/复杂点不覆盖（返回 False，输出诚实标 UNVERIFIED）。
        """
        import math

        from cas.evalnum import eval_approx

        if T.is_num(pt):
            ptv = float(T.num_val(pt))
        elif isinstance(pt, T.Const) and pt.name in ("pi", "e"):
            ptv = math.pi if pt.name == "pi" else math.e
        elif pt is T.INFINITY or (isinstance(pt, T.Expr) and pt.head.name == "Times"
                                  and any(a is T.INFINITY for a in pt.args)):
            # 无穷远点：大样本收敛趋势（x -> ±大数，误差须缩小）
            sgn = -1.0 if isinstance(pt, T.Expr) and T.MONE in pt.args else 1.0
            try:
                lv2 = eval_approx(claimed, {})
            except Exception:
                return False
            if lv2 is None:
                return False
            errs = []
            for d in (1000.0, 4000.0):
                try:
                    fv = eval_approx(t, {x: sgn * d})
                except Exception:
                    fv = None
                if fv is not None:
                    errs.append(abs(fv - lv2))
            return len(errs) == 2 and errs[1] <= max(errs[0] / 2, 1e-9)
        else:
            return False
        try:
            lv = eval_approx(claimed, {})
        except Exception:
            return False
        if lv is None:
            return False
        agree = 0
        for sgn in (1.0, -1.0):
            errs = []
            for d in (0.125, 0.03125):
                try:
                    fv = eval_approx(t, {x: ptv + sgn * d})
                except Exception:
                    fv = None
                if fv is None:
                    continue
                errs.append(abs(fv - lv))
            if len(errs) == 2 and errs[1] <= max(errs[0] / 2, 1e-9):
                agree += 1
        return agree >= 2

    def mlimit(self, expr_s, var_s, point_s):
        """!limit 入口：三值诚实（UNKNOWN 直接显示，永不静默错）；point 可为 ±inf。

        有限极限附数值探针背书（PROBABLE——采样支持非证明）；探针不覆盖
        或不一致时诚实标 UNVERIFIED。发散结论（±Infinity）无廉价证书，裸输出。
        """
        from cas.limits import limit

        t = self._parse_in(expr_s)
        ps = point_s.strip().lower()
        if ps in ("inf", "+inf", "infinity", "+infinity"):
            pt = T.INFINITY
        elif ps in ("-inf", "-infinity"):
            pt = T.neg(T.INFINITY)
        else:
            pt = parse(point_s)
        r = limit(t, T.S(var_s), pt)
        if r is None:
            return "UNKNOWN"
        self._remember(r)
        out = to_str(r)
        is_inf = r is T.INFINITY or (isinstance(r, T.Expr) and r.head.name == "Times"
                                     and any(a is T.INFINITY for a in r.args))
        if is_inf:
            return out
        if self._limit_probe(t, T.S(var_s), pt, r):
            return out + "   [PROBABLE, numeric probe]"
        return out + "   [UNVERIFIED]"

    def mseries(self, expr_s, var_s, point_s, order_s):
        """!series 入口：Taylor 展开为截断多项式 + O 项（O 为一等项头）。

        独立验证通道：前若干系数与逐阶导数（diff 引擎）交叉核对——
        级数引擎与微分引擎是两条独立路径，系数 c_k 应等于 f^(k)(a)/k!。
        """
        from cas.series import series, series_term, SeriesError
        from cas.diff import d as _d
        from math import factorial

        t = self._parse_in(expr_s)
        x = T.S(var_s)
        a = parse(point_s)
        n = int(order_s)
        try:
            r = series_term(t, x, a, n)
            k0, coeffs = series(t, x, a, n)
        except SeriesError as e:
            return f"honest refusal: {e}"
        # 交叉核对（最多前 3 个系数，控制成本）
        # 注意：series() 返回的 coeffs 已是 Taylor 系数 c_k = f^(k)(a)/k!，
        # 与 diff 引擎的 f^(k)(a)/k! 直接比对（勿重复除阶乘）
        ok = True
        try:
            for idx, ck in enumerate(coeffs[:3]):
                dk = t
                for _ in range(k0 + idx):
                    dk = _d(dk, x)
                expect = simplify(T.div(T.subst(dk, {x: a}), T.N(factorial(k0 + idx))))
                got = simplify(T.N(ck))
                if simplify(T.plus(expect, T.neg(got))) is not T.ZERO:
                    ok = False
                    break
        except Exception:
            ok = False   # 验证通道自身失败：诚实 UNVERIFIED，不静默
        self._remember(r)
        kmax = k0 + min(3, len(coeffs)) - 1
        return to_str(r) + f"   [{'VERIFIED' if ok else 'UNVERIFIED'}, coeff check k <= {kmax}]"

    def _parse_bound(self, s):
        """限字面量：inf/-inf -> ±Infinity 项，其余按表达式解析。"""
        ps = s.strip().lower()
        if ps in ("inf", "+inf", "infinity", "+infinity"):
            return T.INFINITY
        if ps in ("-inf", "-infinity"):
            return T.neg(T.INFINITY)
        return parse(s)

    def mdefint(self, expr_s, var_s, lo_s, hi_s):
        """!defint 入口：自动正向换元探测 + Newton-Leibniz + 奇点拆分 + 数值交叉核对。"""
        from cas.integrate import defint_auto

        t = self._parse_in(expr_s)
        val, status, note = defint_auto(t, T.S(var_s), self._parse_bound(lo_s), self._parse_bound(hi_s))
        if val is not None:
            self._kernel_step(f"defint[{note}]", val, before=t)
            return f"{to_str(val)}   [{status}, method: {note}]"
        return f"{status}: {note}"

    def steps(self):
        """可解释步骤文本：规则步 = 逐条推导（规则名/位置/守卫/前后式/cost 变化）；
        算法步 = 算法名 + 验证态（单算法调用无微观步骤可讲，verify 背书即解释）。"""
        if not self.log:
            return ["(no steps)"]
        out = []
        for st in self.log:
            if st.rule_id.startswith("kernel:"):
                src = to_str(st.before) + " " if st.before is not None else ""
                out.append(f"#{st.sid} [algorithm] {src}-> {to_str(st.after)}   ({st.note})")
            else:
                at = f" at {st.path}" if st.path else ""
                note = f"  ({st.note})" if st.note else ""
                out.append(
                    f"#{st.sid} [rule {st.rule_id}]{at}  "
                    f"{to_str(st.before)}  ->  {to_str(st.after)}   "
                    f"(guard={st.guard}, dcost={st.dcost}){note}"
                )
        return out

    def show(self):
        return to_str(self.current) if self.current is not None else "(empty)"

    # ---------------- 转录 DSL（计算可复现/可保存/可回放） ----------------

    # 只读命令不入转录；变更类命令（:rule/:value/:refine/:assume 等）必须入录，
    # 否则回放无法重建推导（转录即 DSL 立场）。
    _NO_RECORD = {":help", ":log", ":steps", ":hist", ":ctx", ":obls", ":defs",
                  ":q", ":quit", ":save", ":replay", ":rules", ":latex", ":tree"}

    def rules_fingerprint(self):
        """规则集指纹：回放确定性校验用（规则变了回放即失效，永不静默错）。

        只覆盖非会话规则：origin='session' 的 :rule 内联定义由转录自身重建，
        不计入指纹（否则保存后回放必被自己的新规则拒死）。
        """
        import hashlib

        h = hashlib.sha1()
        for rid in sorted(self.rules.rules):
            r = self.rules.rules[rid]
            if r.origin == "session":
                continue
            h.update(f"{rid}|{to_str(r.pattern)}|{to_str(r.template)}|{r.priority}".encode())
        return h.hexdigest()[:12]

    def handle(self, line):
        """分发一条命令/表达式，返回输出文本（None = 无输出）。

        REPL 与回放共用同一入口——转录即 DSL，重放转录即重建推导。
        """
        line = line.strip()
        if not line:
            return None
        first = line.split(None, 1)[0]
        try:
            out = self._dispatch(line)
        except (BudgetExceeded, ParseError) as e:
            out = f"error: {e}"
        except Exception as e:
            out = f"error: {e.__class__.__name__}: {e}"
        if first not in self._NO_RECORD:
            self.transcript.append(line)
        return out

    def save_transcript(self, path):
        """保存转录（头部含规则指纹，回放时校验）。"""
        lines = ["# pyCAS transcript v1", f"# rules: {self.rules_fingerprint()}"]
        lines.extend(self.transcript)
        with open(path, "w", encoding="utf-8") as fh:
            fh.write("\n".join(lines) + "\n")
        return f"saved {len(self.transcript)} commands to {path}"

    def replay_file(self, path):
        """回放转录文件：跳注释头，逐条走 handle（与 REPL 完全同路径）。"""
        with open(path, "r", encoding="utf-8") as fh:
            raw = fh.readlines()
        cmds = []
        fp = None
        for ln in raw:
            ln = ln.rstrip("\n")
            if ln.startswith("# rules: "):
                fp = ln.split(": ", 1)[1].strip()
            elif not ln.startswith("#"):
                cmds.append(ln)
        if fp is not None and fp != self.rules_fingerprint():
            return (f"refused: rules fingerprint mismatch "
                    f"(file={fp}, session={self.rules_fingerprint()})")
        outs = []
        for c in cmds:
            if not c.strip():
                continue
            o = self.handle(c)
            if o:
                outs.append(o)
        return f"replayed {len(cmds)} commands\n" + "\n".join(outs)

    def commands(self):
        out = {
            ":s": "suggest [path]",
            ":a": "apply <rule-id> [path]",
            ":u": "undo [n]",
            ":auto": "core simplify",
            ":tree": "show subterm tree with paths (selection for path commands)",
            ":set": "subterm surgery: :set <path> <expr> (equivalent-checked)",
            ":rsub": "structural replace-all: :rsub <old>=<new>",
            ":add_both": "equation: add <t> to both sides",
            ":sub_both": "equation: subtract <t> from both sides",
            ":mul_both": "equation: multiply both sides by <t>",
            ":div_both": "equation: divide both sides by <t> (t != 0 gate)",
            ":neg_both": "equation: negate both sides",
            ":swap": "equation: swap sides",
            ":zero_form": "equation: rewrite L = R as L - R = 0",
            ":apply_both": "equation: apply unary fn to both sides: :apply_both <fn>",
            ":expand": "expand products/powers: :expand [path]",
            ":extract": "factor out common factor: :extract <f> [path]",
            ":separate": "split fraction over sum: (a+b)/c -> a/c+b/c: :separate [path]",
            ":complete_square": "complete square: :complete_square <var> [path]",
            ":usub": "forward substitution on inert integral: :usub t=g(x)",
            ":lhop": "one l'Hopital step on quotient form: :lhop <var> <point>",
            ":intro_eq": "extract chain equation: :intro_eq <lhs|%N> (lhs = current; loop: :intro_eq I)",
            ":fold": "linearity fold: rewrite constant-multiple named integrals (loop setup)",
            ":add_sub": "add-zero borrow: :add_sub <t> (A -> A + t - t, quoted; domain obligation)",
            ":parts": "integration by parts on inert integral: :parts <u> (shows u/dv/du/v)",
            ":subst": "substitute new variable: :subst t=g(x) (handles inert integral dx too)",
            ":solveq": "solve current linear equation for unknown: :solveq <term>",
            ":rule": "define session theorem inline: :rule id = lhs -> rhs [guard ... as ... auto]",
            ":unrule": "remove a session rule",
            ":rules": "list all rules (origin/prio/guard/direction)",
            ":value": "evaluate inert forms (Quote/'integrate/D nouns) in current expr",
            ":refine": "ledger-driven simplification (abs/sqrt/exp-log by assumptions)",
            ":latex": "LaTeX output of current expression",
            ":save": "save command transcript (DSL): :save <path>",
            ":replay": "replay a transcript: :replay <path>",
            ":steps": "explain the derivation (rules step-by-step; algorithms by name)",
            ":hist": "produced expressions (%N to reuse, % = latest)",
            ":defs": "list user definitions (name := expr / f(x) := expr)",
            ":undef": "remove a definition",
            ":assume": "assume <fact>",
            ":ans": "answer <oid> <fact>",
            ":obls": "list obligations",
            ":log": "step log",
            ":ctx": "ledger",
        }
        for name, c in self.kernel.items():
            out[":" + name] = c.help
        for name, c in self.solver.items():
            out["!" + name] = c.help
        out[":load"] = "reload rules dir"
        out[":q"] = "quit"
        return out


    def _dispatch(self, line):
        """全部分支返回文本（不打印）：REPL 与回放共用。分支顺序纪律：
        精确命令 > 内核注册表 > 前缀命令（:steps 被 :s 吞、:save 被 :s 吞的同款 bug 防三次）。"""
        if line == ":help":
            return "\n".join(f"{k:12s} {v}" for k, v in self.commands().items())
        if line == ":steps":
            return "\n".join(self.steps())
        if line == ":hist":
            out = [f"%{i}  {to_str(h)}" for i, h in enumerate(self.history, 1)]
            return "\n".join(out) if out else "(empty)"
        if line == ":defs":
            out = []
            for nm, (ps_, body) in self.defs.items():
                sig = f"{nm}({', '.join(p.name for p in ps_)})" if ps_ else nm
                out.append(f"{sig} := {to_str(body)}")
            return "\n".join(out) if out else "(none)"
        if line.startswith(":save "):
            return self.save_transcript(line[6:].strip())
        if line.startswith(":replay "):
            return self.replay_file(line[8:].strip())
        if line.startswith(":rule "):
            return self.add_rule(line[6:])
        if line.startswith(":unrule "):
            return self.unrule(line[8:].strip())
        if line == ":rules":
            return self.list_rules()
        if line == ":value":
            return self.value()
        if line == ":refine":
            return self.mrefine()
        if line == ":latex":
            return self.mlatex()
        # ! 前缀：自动求解（算法黑盒直出，verify 背书）
        if line.startswith("!") and line.split(None, 1)[0][1:] in self.solver:
            parts = line.split(None, 1)
            name = parts[0][1:]
            rest = self.expand_history(parts[1].strip()) if len(parts) > 1 else ""
            return self.solver[name].fn(self, rest)
        if line.startswith(":") and line.split(None, 1)[0][1:] in self.kernel:
            # 手动算法命令分发（: 前缀；先于前缀匹配，避免 :apart 被 :a 吞掉）
            parts = line.split(None, 1)
            name = parts[0][1:]
            rest = self.expand_history(parts[1].strip()) if len(parts) > 1 else ""
            return self.kernel[name].fn(self, rest)
        # ---- 手动交互扩展（子项手术/等式代数/变形工具箱/微积分战术）----
        # 分支顺序纪律：先于 :s / :u 前缀分支（:set/:swap/:separate 被 :s 吞、
        # :usub 被 :u 吞的同款 bug 防患）
        if line == ":tree":
            return self.tree()
        if line.startswith(":set "):
            parts = line[5:].split(None, 1)
            if len(parts) != 2:
                return "usage: :set <path> <expr>"
            return self.set_at(parts[0], self.expand_history(parts[1]))
        if line.startswith(":rsub "):
            return self.rsub(self.expand_history(line[6:].strip()))
        if line.startswith(":add_both "):
            return self.eq_add_both(line[10:].strip())
        if line.startswith(":sub_both "):
            return self.eq_sub_both(line[10:].strip())
        if line.startswith(":mul_both "):
            return self.eq_mul_both(line[10:].strip())
        if line.startswith(":div_both "):
            return self.eq_div_both(line[10:].strip())
        if line == ":neg_both":
            return self.eq_neg_both()
        if line == ":swap":
            return self.eq_swap()
        if line == ":zero_form":
            return self.eq_zero_form()
        if line.startswith(":apply_both "):
            return self.eq_apply_both(line[12:].strip())
        if line.startswith(":expand"):
            return self.expand_at(line[7:].strip() or None)
        if line.startswith(":extract "):
            parts = line[9:].split()
            path_s = None
            if len(parts) >= 2 and all(seg.isdigit() for seg in parts[-1].split(".")):
                path_s = parts[-1]
                parts = parts[:-1]
            return self.extract(" ".join(parts), path_s)
        if line == ":separate":
            return self.separate_at(None)
        if line.startswith(":separate "):
            return self.separate_at(line[10:].strip() or None)
        if line.startswith(":complete_square "):
            parts = line[17:].split()
            if not parts:
                return "usage: :complete_square <var> [path]"
            return self.complete_square(parts[0], parts[1] if len(parts) > 1 else None)
        if line.startswith(":usub "):
            res = self.usub(line[6:].strip())
            return to_str(res) if isinstance(res, T.Term) else res
        if line.startswith(":lhop "):
            parts = line[6:].split()
            if len(parts) != 2:
                return "usage: :lhop <var> <point>"
            res = self.lhop(parts[0], parts[1])
            return to_str(res) if isinstance(res, T.Term) else res
        if line.startswith(":intro_eq "):
            # %N 先展开：等式链任意节点（历史产出）都可与当前式连等式
            res = self.intro_eq(self.expand_history(line[10:].strip()))
            return to_str(res) if isinstance(res, T.Term) else res
        if line == ":fold":
            return self.fold()
        if line.startswith(":add_sub "):
            res = self.add_sub(line[9:].strip())
            return to_str(res) if isinstance(res, T.Term) else res
        if line.startswith(":parts "):
            res = self.iparts(line[7:].strip(), detail=True)
            return res if isinstance(res, str) else to_str(res)
        if line.startswith(":subst "):
            res = self.subst(line[7:].strip())
            return to_str(res) if isinstance(res, T.Term) else res
        if line.startswith(":solveq "):
            res = self.solveq(line[8:].strip())
            return to_str(res) if isinstance(res, T.Term) else res
        if line.startswith(":s"):
            arg = line[2:].strip()
            path = tuple(int(i) for i in arg.split(".")) if arg else ()
            out = [f"{rid:20s} guard={g:8s} {('dir=' + d) if d else ''}"
                   for rid, g, d in self.suggest(path)]
            return "\n".join(out)
        if line.startswith(":a "):
            parts = line[3:].split()
            rid = parts[0]
            path = tuple(int(i) for i in parts[1].split(".")) if len(parts) > 1 else None
            n0 = len(self.log)
            res = self.apply(rid, path)
            out = [to_str(res) if isinstance(res, T.Term) else res]
            out += ["  " + ln for ln in self.steps()[n0:]]
            return "\n".join(out)
        if line.startswith(":undef "):
            return self.undef(line[7:].strip())
        if line.startswith(":u"):
            n = int(line[2:] or 1)
            return to_str(self.undo(n)) if self.log else "no steps"
        if line == ":auto":
            n0 = len(self.log)
            out = [to_str(self.auto())]
            out += ["  " + ln for ln in self.steps()[n0:]]
            return "\n".join(out)
        if line.startswith(":assume "):
            return self.assume(self.expand_history(line[8:]))
        if line.startswith(":declare "):
            parts = line[9:].split()
            if len(parts) == 2:
                return self.declare(parts[0], parts[1])
            return "usage: :declare <var> <property>"
        if line.startswith(":ans "):
            parts = line[5:].split(None, 1)
            oid = int(parts[0])
            return self.answer(oid, self.expand_history(parts[1]))
        if line == ":obls":
            out = [f"#{o.oid}  {to_str(o.question)}   affects steps {o.affects}"
                   for o in self.obligations]
            return "\n".join(out) if out else "(none)"
        if line == ":log":
            out = [f"#{st.sid} {st.rule_id:18s} at {st.path}  {to_str(st.before)}  ->  {to_str(st.after)}"
                   for st in self.log]
            return "\n".join(out) if out else "(no steps)"
        if line == ":ctx":
            out = [f"[{e.kind}:{e.origin}] {to_str(e.fact)}" for e in self.ctx.entries]
            return "\n".join(out) if out else "(empty ledger)"
        if line == ":load":
            import os

            rd = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "rules")
            return f"loaded {loader.load_dir(rd, self.rules)} rules"
        if ":=" in line:
            # 用户定义：f(x) := 体（函数）/ a := 体（变量），宏展开语义；右侧支持 % 历史
            lhs, rhs = line.split(":=", 1)
            lhs = lhs.strip()
            rhs = self.expand_history(rhs.strip())
            if "(" in lhs:
                return self.define(lhs, rhs)
            return self.assign(lhs, rhs)
        self.feed(self.expand_history(line))
        return self.show()

    # ---------------- 方案命令（人机协作：人选方向，机器算） ----------------

    def subst(self, eq_s):
        """换元（手工通道，通用）。

        :subst t=g(x)：把当前式中 g(x) 全部替换为新变量 t（复合键一次替换）；
        当前式若是惰性积分 Integrate(f, x)，同时把被积式与微分元变换到新变量
        （dx 随换元变换：t=g(x) 经主支逆解 x=h(t)，新被积式 = f(h(t))·h'(t)）。
        反向求逆走 solve 通道（spec.inv 驱动，仿射复合主支逆已支持）。
        正确性由用户后续 !verify 微分回验背书。
        """
        self._check_locked()
        if self.current is None:
            return "empty session"
        from cas.diff import d as _d
        from cas.solve import solve as _solve

        eq = parse(eq_s)
        if not (isinstance(eq, T.Expr) and eq.head.name == "Eq"):
            return "usage: :subst t=g(x)  (e.g. :subst t=tan(x/2))"
        lhs, rhs = eq.args
        # 惰性积分：积分变量 x 参与方向判定（free_vars 会跳过被 Bound 绑定的 x）
        is_integ = (isinstance(self.current, T.Expr) and self.current.head.name == "Integrate"
                    and len(self.current.args) == 1 and isinstance(self.current.args[0], T.Bound))
        fv = T.free_vars(self.current)
        if is_integ:
            x, body = T.open_bound(self.current.args[0])
            oldvars = fv | {x}
        else:
            oldvars = fv
        # 方向判定：新变量 = 裸符号 + 不在当前式 + 对侧含当前式变量
        if isinstance(lhs, T.Sym) and lhs not in fv and (T.free_vars(rhs) & oldvars):
            newvar, gexpr = lhs, rhs
        elif isinstance(rhs, T.Sym) and rhs not in fv and (T.free_vars(lhs) & oldvars):
            newvar, gexpr = rhs, lhs
        else:
            return "subst: 等式一边必须是当前式中未出现的新变量（裸符号）"
        before = self.current
        # 惰性积分：换元变换被积式与微分元
        if is_integ:
            # t = g(x) -> 解 x = h(t)
            r = _solve(T.plus(gexpr, T.neg(newvar)), x)
            if r.status != "ok" or not r.solutions:
                return (f"subst: 无法对 {to_str(gexpr)} 求逆（solve: {r.note or r.status}）；"
                        "请给出可求逆的换元（spec.inv 主支逆）")
            ht = r.solutions[0]
            new_body = T.subst(body, {x: ht})
            dht = _d(ht, newvar)
            new_int = T.mk(T.S("Integrate"), (T.mk_bound(newvar, simplify(T.times(new_body, dht))),))
            repl = new_int
            note = f"substitution {to_str(gexpr)} = {newvar.name} (dx -> {to_str(dht)} dt)"
        else:
            # 普通表达式：把 g(x) 替换为新变量（复合键一次全部替换）
            repl = T.subst(self.current, {gexpr: newvar})
            note = f"substitution {to_str(gexpr)} -> {newvar.name}"
        self.current = repl
        self._sid += 1
        self.log.append(Step(self._sid, "scheme:subst", (), before, self.current, "YES",
                             cost(self.current) - cost(before), note=note))
        self._remember(self.current)
        return self.current

    def iparts(self, u_s, detail=False):
        """分部积分（人工干预通道）：用户选 u，内核算 dv = 体/u、v = ∫dv、du，
        ∫体 -> u·v − ∫v·du。自动搜索当前式中体被 u 整除的惰性积分子项。

        detail=True 返回 u/dv/du/v 明细文本（教学/检查用）；否则返回新项。
        """
        self._check_locked()
        if self.current is None:
            return "empty session"
        from cas.diff import d
        from cas.integrate import integrate as zz_int
        from cas.decide import equivalent
        from cas.errors import PolyError

        u = self._parse_in(u_s)
        found = None
        for p in T.all_paths(self.current):
            try:
                tgt = T.term_at(self.current, p)
            except IndexError:
                continue
            if not (isinstance(tgt, T.Expr) and tgt.head.name == "Integrate"
                    and len(tgt.args) == 1 and isinstance(tgt.args[0], T.Bound)):
                continue
            b = tgt.args[0]
            x, body = T.open_bound(b)   # de Bruijn 体还原为自由符号才可参与环运算
            if not isinstance(x, T.Sym):
                continue
            q = simplify(T.div(body, u))
            if equivalent(T.times(u, q), body) is not T3.YES:
                continue
            try:
                v, _ok, _m, _prov = zz_int(q, x)
            except PolyError:
                continue
            du = d(u, x)
            cand = T.times(v, du)
            # 常数符号拉出绑定体：∫(-f) = -∫f（线性，generic 安全）。
            # 指针收敛：循环再现的积分名词与链首驻留同一（:intro_eq/:solveq 可命中，
            # 循环检测可行）。不拉出则 -号留在 Bound 内，名词指针分裂。
            flip = False
            if isinstance(cand, T.Expr) and cand.head.name == "Times" \
                    and T.MONE in cand.args:
                rest = T.mk(T.S("Times"),
                            tuple(a for a in cand.args if a is not T.MONE))
                cand = rest
                flip = True
            new_int = T.mk(T.S("Integrate"), (T.mk_bound(x, cand),))
            core = T.times(u, v)
            repl = T.plus(core, new_int) if flip else T.plus(core, T.neg(new_int))
            found = (p, repl,
                     {"u": u, "dv": q, "du": du, "v": v})
            break
        if found is None:
            return f"parts: no inert integral subterm with body divisible by {to_str(u)}"
        p, repl, det = found
        before = self.current
        self.current = T.replace_at(self.current, p, repl)
        self._sid += 1
        self.log.append(Step(
            self._sid, f"scheme:parts[u={to_str(u)}]", p, before, self.current, "YES",
            cost(self.current) - cost(before), note="integration by parts",
        ))
        self._remember(self.current)
        if detail:
            lines = [
                f"u  = {to_str(det['u'])}",
                f"dv = {to_str(det['dv'])} dx",
                f"du = {to_str(det['du'])} dx",
                f"v  = {to_str(det['v'])}",
                f"=> {to_str(self.current)}",
            ]
            hint = self._named_loop(self.current)
            if hint:
                lines.append(f"[loop] {hint} recurs - extract equation: "
                             f":intro_eq {hint}, then :solveq {hint}")
            return "\n".join(lines)
        return self.current

    def _named_loop(self, t):
        """循环检测：t 中是否指针再现某个已命名的惰性积分名词 -> 名字或 None。

        驻留使指针判等 O(1)；iparts 的符号拉出保证循环再现时名词同一。
        """
        named = [(name, body) for name, (params, body) in self.defs.items()
                 if not params and isinstance(body, T.Expr)
                 and body.head.name == "Integrate"]
        if not named:
            return None
        stack = [t]
        while stack:
            u = stack.pop()
            for name, body in named:
                if u is body:
                    return name
            if isinstance(u, T.Expr):
                stack.extend(u.args)
            elif isinstance(u, T.Bound):
                stack.append(u.body)
        return None

    def fold(self):
        """:fold：线性折叠——current 中与已命名惰性积分体成数值常数倍的名词，
        改写为 常数·命名名词（∫c·g = c·∫g，线性 generic 安全）。

        用途：倍数/负号起点的循环。I := ∫-f 时循环再现的是 ∫f = -I，
        指针天然不同一；fold 用线性性归一后 :intro_eq/:solveq 的循环消解
        才能命中。这是通用机制（常数倍关系判定），不是针对特定例子的特化。
        """
        self._check_locked()
        if self.current is None:
            return "empty session"
        from fractions import Fraction

        named = [(name, body) for name, (params, body) in self.defs.items()
                 if not params and isinstance(body, T.Expr)
                 and body.head.name == "Integrate"]
        if not named:
            return "fold: no named inert integrals (:name := integrate(...))"
        cur = self.current
        repls = []   # (path, 命名名词体, 倍数)
        seen_nouns = set()
        for p in list(T.all_paths(cur)):
            try:
                sub = T.term_at(cur, p)
            except IndexError:
                continue
            if not (isinstance(sub, T.Expr) and sub.head.name == "Integrate"
                    and len(sub.args) == 1 and isinstance(sub.args[0], T.Bound)):
                continue
            if sub._h in seen_nouns:
                continue
            seen_nouns.add(sub._h)
            xv, body_n = T.open_bound(sub.args[0])
            for name, body in named:
                if body is sub:
                    break   # 已是命名名词本身
                xb, body_o = T.open_bound(body.args[0])
                if xv is not xb:
                    continue
                q = _quotient_cancel(body_n, body_o)
                if T.is_num(q):
                    c = T.num_val(q)
                    if c != 0:
                        repls.append((p, body, c))
                        break
        if not repls:
            return f"{to_str(cur)}   [fold: no constant-multiple integrals]"
        # 内层路径先替换（嵌套名词时外层路径索引不变）
        for p, body, c in sorted(repls, key=lambda r: -len(r[0])):
            cur = T.replace_at(cur, p, T.times(T.N(c), body))
        before = self.current
        self.current = simplify(cur)
        if self.current is before:
            return f"{to_str(before)}   [fold: no change]"
        self._sid += 1
        self.log.append(Step(
            self._sid, "scheme:fold", (), before, self.current, "YES",
            cost(self.current) - cost(before),
            note=f"linearity fold of {len(repls)} integral(s)",
        ))
        self._remember(self.current)
        out = to_str(self.current)
        hint = self._named_loop(self.current)
        if hint:
            out += f"\n[loop] {hint} recurs - extract equation: :intro_eq {hint}, then :solveq {hint}"
        return out

    def add_sub(self, t_s):
        """:add_sub <t>：加零凑形 A -> A + t - t（表达式层借用形战术）。

        结构保真：t 以 quote 包裹、和式走纯驻留构造（_intern_expr）——
        否则 mk 的同类项归并当场消掉 +t-t，等式塌成 A=A。
        t 的定义域照常闸门并创建义务：后续 :intro_eq 提取等式时，
        该守卫必须先行结算（硬闸门）——机器知道的守卫不允许蒸发。
        """
        self._check_locked()
        if self.current is None:
            return "empty session"
        if isinstance(self.current, T.Expr) and self.current.head.name == "Eq":
            return "add_sub: current is an equation (use :add_both/:sub_both)"
        t = parse(t_s.strip())
        provs, err = self._term_domain_gate(t, f"borrowing {to_str(t)}")
        if err:
            return err
        qt = T.quote(t)
        nq = T._intern_expr(T.S("Times"), (T.MONE, qt))
        before = self.current
        new = T._intern_expr(T.S("Plus"), (before, qt, nq))
        self.current = new
        self._sid += 1
        self.log.append(Step(
            self._sid, "scheme:add_sub", (), before, new, "YES",
            cost(new) - cost(before),
            note=f"added and subtracted {to_str(t)} (borrowed form)",
        ))
        self._remember(new)
        out = to_str(new)
        return out + self._proviso_suffix(provs)

    def intro_eq(self, lhs_s):
        """:intro_eq <lhs|%N>：等式链提取——把当前式声明为 Eq(lhs, current)。

        计算即等式链：step log 每步的 before->after 都是一条等式；本命令把
        链上节点显式提取为一等方程（循环分部的 I = A - I）。

        守卫结算（硬闸门）：派生等式的守卫 = 链上所有步骤条件的合取。
        规则 guard 已在 commit 时入账本；开放义务（域条件等）未决时拒绝
        建立等式——机器知道的守卫不允许蒸发。先 :ans 作答使条件入账，
        再重试。手写方程（feed 层）不受此限：断言自由但由断言者担责。
        """
        self._check_locked()
        if self.current is None:
            return "empty session"
        if isinstance(self.current, T.Expr) and self.current.head.name == "Eq":
            return "intro_eq: current is already an equation"
        if self.obligations:
            gs = "; ".join(f"#{o.oid} {to_str(o.question)}" for o in self.obligations)
            return (f"intro_eq refused: derivation chain has open guards ({gs}) - "
                    f"the equation holds only under them. Resolve with "
                    f":ans <oid> <fact> first, then retry.")
        lhs = self._expand_defs(parse(lhs_s.strip()), bare_ok=True)
        # 纯驻留构造：mk 会把 current 中的借用形（'t - 't）当场归并塌掉，
        # 等式将失去其守卫载体——Eq 必须原样保结构
        eq = T._intern_expr(T.S("Eq"), (lhs, self.current))
        before = self.current
        self.current = eq
        self._sid += 1
        self.log.append(Step(
            self._sid, "scheme:intro_eq", (), before, eq, "YES",
            cost(eq) - cost(before),
            note=f"chain equation: {to_str(lhs)} = current",
        ))
        self._remember(eq)
        return to_str(eq)

    def solveq(self, unknown_s):
        """把当前等式当线性方程解出指定未知项（未知 → z 提系数）。

        eˣsin x 消循环的关键步：I = A − I -> I = A/2。
        """
        self._check_locked()
        if not (isinstance(self.current, T.Expr) and self.current.head.name == "Eq"):
            return "solveq: current must be an equation"
        from cas.solve import _linear_split, _free

        unknown = self._parse_in(unknown_s)
        # 裸符号且是变量定义 -> 解析为宏体（:solveq I 直接按名字解循环方程）
        if isinstance(unknown, T.Sym) and unknown.name in self.defs \
                and self.defs[unknown.name][0] == ():
            unknown = self.defs[unknown.name][1]
        z = T.S("_solveq_z")
        f = T.subst(T.plus(self.current.args[0], T.neg(self.current.args[1])), {unknown: z})
        f = simplify(expand(f))   # 负号分配/同类项归并（与 solve 同款预处理）
        if z not in T.free_vars(f):
            return "solveq: unknown not found in equation"
        lin = _linear_split(f, z)
        if lin is None:
            return "solveq: only linear equations supported"
        a, b = lin
        if not (_free(a, z) and _free(b, z)):
            return "solveq: only linear equations supported"
        if a is T.ZERO:
            return "solveq: unknown cancels out"
        sol = simplify(T.div(T.neg(b), a))
        before = self.current
        self.current = sol
        self._sid += 1
        self.log.append(Step(
            self._sid, "scheme:solveq", (), before, sol, "YES",
            cost(sol) - cost(before), note=f"solved linear equation for {to_str(unknown)}",
        ))
        self._remember(sol)
        if not T.is_num(a):
            return f"{to_str(sol)}   [proviso: {to_str(T.mk(T.S('Ne'), (a, T.ZERO)))}]"
        return sol

    # ---------------- 手动交互扩展：子项手术 / 等式代数 / 变形工具箱 / 微积分战术 ----------------

    def tree(self):
        """:tree：带路径的子项树（只读）。path 寻址命令的可视化选择器。"""
        if self.current is None:
            return "empty session"
        out = []
        stack = [(self.current, ())]
        while stack:
            t, p = stack.pop()
            out.append((p, t))
            if isinstance(t, T.Expr):
                for i, a in enumerate(t.args):
                    stack.append((a, p + (i,)))
            elif isinstance(t, T.Bound):
                stack.append((t.body, p + (0,)))
        lines = []
        for p, t in sorted(out, key=lambda pt: pt[0]):
            ps = ".".join(str(i) for i in p) or "()"
            lines.append(f"{ps:12s}{'  ' * len(p)}{to_str(t)}")
        return "\n".join(lines)

    def _resolve_target(self, path_s):
        """可选 path 参数 -> (子项, path, None)；path_s 为空取当前式。出错返回错误文本。"""
        if self.current is None:
            return None, None, "empty session"
        if not path_s:
            return self.current, (), None
        try:
            path = tuple(int(i) for i in str(path_s).split("."))
            sub = T.term_at(self.current, path)
        except (ValueError, IndexError):
            return None, None, f"no subterm at path {path_s}"
        return sub, path, None

    @staticmethod
    def _eqv_tag(eqv):
        """equivalent 提交态标注（YES->VERIFIED / PROBABLE；UNKNOWN/NO 由调用方拒绝）。"""
        return {T3.YES: "VERIFIED", T3.PROBABLE: "PROBABLE"}.get(eqv, "UNVERIFIED")

    def _new_domain_conditions(self, old, new):
        """new 相对 old 新引入的定义域约束（:set/:rsub 换入项的域收窄检测）。

        公共域采样只在重叠域上比对等价——换入定义域更窄的项会静默收窄表达式
        的定义范围。恒真约束（decide=YES，如偶次幂非负公理）与 old 已携带的
        约束跳过；其余作为 proviso 显式记账。
        """
        from cas.domain import dom_condition

        old_list = list(dom_condition(old))
        out = []
        for c in dom_condition(new):
            if _decide_fn(c, self.ctx) is T3.YES:
                continue
            if any(c is o for o in old_list):
                continue
            if not any(c is p for p in out):
                out.append(c)
                self._oid += 1
                self.obligations.append(Obligation(
                    self._oid, c, [self._sid + 1],
                    note="domain condition introduced by replacement",
                ))
        return out

    def set_at(self, path_s, expr_s):
        """        :set <path> <expr>：直接子项手术。

        equivalent(旧子项, 新子项) 三态闸门：YES->提交标 VERIFIED /
        PROBABLE->提交标 PROBABLE；UNKNOWN 拒绝（不可验证的篡改不放行——
        先 :assume 事实或定义规则再重试）；NO 拒绝。永不静默错。
        """
        self._check_locked()
        old, path, err = self._resolve_target(path_s)
        if err:
            return err
        new = self._parse_in(expr_s)
        if old is new:
            return "set: replacement identical"
        eqv = _equivalent_fn(old, new, self.ctx)
        if eqv is T3.NO:
            return f"set refused: {to_str(old)} and {to_str(new)} are not equivalent"
        if eqv is T3.UNKNOWN:
            return (f"set refused: cannot verify {to_str(old)} ~ {to_str(new)} "
                    "(UNKNOWN); :assume the fact or define a rule, then retry")
        tag = self._eqv_tag(eqv)
        provs = self._new_domain_conditions(old, new)
        before = self.current
        self.current = T.replace_at(self.current, path, new)
        self._sid += 1
        self.log.append(Step(
            self._sid, "scheme:set", tuple(path), before, self.current, "YES",
            cost(self.current) - cost(before), note=f"subterm replace [{tag}]",
        ))
        self._remember(self.current)
        out = to_str(self.current)
        if tag != "VERIFIED":
            out += f"   [{tag}]"
        return out + self._proviso_suffix(provs)

    def rsub(self, s):
        """        :rsub <old>=<new>：全式结构替换（T.subst 复合键一次命中）。

        equivalent 三态闸门同 :set（YES/PROBABLE 提交，UNKNOWN/NO 拒绝）；
        old 未出现则报 not found。
        """
        self._check_locked()
        if self.current is None:
            return "empty session"
        if "=" not in s:
            return "usage: :rsub <old>=<new>"
        olds, news = s.split("=", 1)
        old = self._parse_in(olds.strip())
        new = self._parse_in(news.strip())
        nxt = T.subst(self.current, {old: new})
        if nxt is self.current:
            return f"rsub: {to_str(old)} not found in current expression"
        eqv = _equivalent_fn(old, new, self.ctx)
        if eqv is T3.NO:
            return f"rsub refused: {to_str(old)} and {to_str(new)} are not equivalent"
        if eqv is T3.UNKNOWN:
            return (f"rsub refused: cannot verify {to_str(old)} ~ {to_str(new)} "
                    "(UNKNOWN); :assume the fact or define a rule, then retry")
        tag = self._eqv_tag(eqv)
        provs = self._new_domain_conditions(old, new)
        before = self.current
        self.current = nxt
        self._sid += 1
        self.log.append(Step(
            self._sid, "scheme:rsub", (), before, self.current, "YES",
            cost(self.current) - cost(before),
            note=f"replace {to_str(old)} -> {to_str(new)} [{tag}]",
        ))
        self._remember(self.current)
        out = to_str(self.current)
        if tag != "VERIFIED":
            out += f"   [{tag}]"
        return out + self._proviso_suffix(provs)

    # 等式双侧操作（Maxima eqnflag / Mathematica 等式算术的显式命令化；
    # mk 保持纯规范化纪律，不引入隐式线程化）

    def _require_eq(self):
        """等式命令前置检查 -> (lhs, rhs, None) 或 (None, None, 错误文本)。"""
        if self.current is None:
            return None, None, "empty session"
        if not (isinstance(self.current, T.Expr) and self.current.head.name == "Eq"):
            return None, None, "current must be an equation (L = R)"
        return self.current.args[0], self.current.args[1], None

    def _commit_eq(self, new_eq, note):
        before = self.current
        self.current = new_eq
        self._sid += 1
        self.log.append(Step(
            self._sid, "scheme:eq", (), before, self.current, "YES",
            cost(self.current) - cost(before), note=note,
        ))
        self._remember(self.current)
        return to_str(self.current)

    @staticmethod
    def _proviso_suffix(provs):
        if not provs:
            return ""
        return "   [proviso: " + " && ".join(to_str(c) for c in provs) + "]"

    def _term_domain_gate(self, t, what):
        """操作数 t 的定义域三态闸门 -> (provisos, None) 或 (None, 错误文本)。

        等式双侧操作引入的项必须在解点有定义，否则解集被静默收窄
        （借用形 +ln(x-k)-ln(x-k) 类操作的核心风险）。NO 拒绝（与账本矛盾，
        ex falso 纪律）/ UNKNOWN 记 proviso 并创建义务（条件显式在案，
        可 :ans 作答——守卫不静默丢失）。
        """
        from cas.domain import dom_condition

        provs = []
        for c in dom_condition(t):
            r = _decide_fn(c, self.ctx)
            if r is T3.NO:
                return None, f"domain empty: {what} requires {to_str(c)} (contradicted)"
            if r is T3.UNKNOWN and not any(c is p for p in provs):
                provs.append(c)
                self._oid += 1
                self.obligations.append(Obligation(
                    self._oid, c, [self._sid + 1],
                    note=f"domain condition of {what}",
                ))
        return provs, None

    def eq_add_both(self, t_s):
        """:add_both <t>：两边加 t。群运算安全，但 t 的定义域约束照常闸门
        （加一个 ln(x-k) 会把解集收窄到 x>k——必须显式记账，绝不静默）。"""
        self._check_locked()
        L, R, err = self._require_eq()
        if err:
            return err
        t = self._parse_in(t_s)
        provs, err = self._term_domain_gate(t, f"adding {to_str(t)}")
        if err:
            return err
        out = self._commit_eq(
            T.mk(T.S("Eq"), (T.plus(L, t), T.plus(R, t))),
            f"added {to_str(t)} to both sides")
        return out + self._proviso_suffix(provs)

    def eq_sub_both(self, t_s):
        """:sub_both <t>：两边减 t（移项 = sub_both + 归一）。域闸门同 add_both。"""
        self._check_locked()
        L, R, err = self._require_eq()
        if err:
            return err
        t = self._parse_in(t_s)
        provs, err = self._term_domain_gate(t, f"subtracting {to_str(t)}")
        if err:
            return err
        out = self._commit_eq(
            T.mk(T.S("Eq"), (T.plus(L, T.neg(t)), T.plus(R, T.neg(t)))),
            f"subtracted {to_str(t)} from both sides")
        return out + self._proviso_suffix(provs)

    def eq_mul_both(self, t_s):
        """:mul_both <t>：两边乘 t。正向蕴含恒成立，t 的定义域约束照常闸门
        （乘一个未定义项使两侧无定义；反向需 t!=0，由求解端回验负责）。"""
        self._check_locked()
        L, R, err = self._require_eq()
        if err:
            return err
        t = self._parse_in(t_s)
        provs, err = self._term_domain_gate(t, f"multiplying by {to_str(t)}")
        if err:
            return err
        out = self._commit_eq(
            T.mk(T.S("Eq"), (T.times(L, t), T.times(R, t))),
            f"multiplied both sides by {to_str(t)}")
        return out + self._proviso_suffix(provs)

    def eq_div_both(self, t_s):
        """:div_both <t>：两边除 t。域闸门三态（含 t!=0 与 t 自身定义域）：
        NO 拒绝（域空）/ UNKNOWN 记 proviso / YES 无条件。"""
        self._check_locked()
        L, R, err = self._require_eq()
        if err:
            return err
        t = self._parse_in(t_s)
        provs, err = self._term_domain_gate(T.div(T.ONE, t),
                                            f"dividing by {to_str(t)}")
        if err:
            return err
        out = self._commit_eq(
            T.mk(T.S("Eq"), (T.div(L, t), T.div(R, t))),
            f"divided both sides by {to_str(t)}")
        return out + self._proviso_suffix(provs)

    def eq_neg_both(self):
        """:neg_both：两边取负。"""
        self._check_locked()
        L, R, err = self._require_eq()
        if err:
            return err
        return self._commit_eq(
            T.mk(T.S("Eq"), (T.neg(L), T.neg(R))), "negated both sides")

    def eq_swap(self):
        """:swap：交换等式两侧。"""
        self._check_locked()
        L, R, err = self._require_eq()
        if err:
            return err
        return self._commit_eq(T.mk(T.S("Eq"), (R, L)), "swapped sides")

    def eq_zero_form(self):
        """:zero_form：L = R -> L - R = 0（喂给 !solveineq/Sturm 前的规范形）。"""
        self._check_locked()
        L, R, err = self._require_eq()
        if err:
            return err
        z = simplify(T.plus(L, T.neg(R)))
        return self._commit_eq(T.mk(T.S("Eq"), (z, T.ZERO)), "moved to zero form")

    def eq_apply_both(self, name_s):
        """:apply_both <fn>：对等式两边应用一元函数。

        域闸门：f(L)/f(R) 的 dom_condition 逐个 decide（NO 拒绝 / UNKNOWN 记 proviso）。
        单射性读 spec.injective 声明：False 提示"仅正向蕴含，后续解须回验"；
        None 提示未声明。sqrt 特例直写 Power(1/2)。
        """
        self._check_locked()
        L, R, err = self._require_eq()
        if err:
            return err
        name = name_s.strip()
        if name == "sqrt":
            fL, fR, inj = T.sqrt(L), T.sqrt(R), None
        else:
            sp = _spec.get(name) or _spec.get(name[0].upper() + name[1:] if len(name) > 1 else name)
            if sp is None or sp.arity != 1:
                return f"apply_both: unknown unary function {name}"
            head = T.S(sp.name)
            fL, fR, inj = T.mk(head, (L,)), T.mk(head, (R,)), sp.injective
        from cas.domain import dom_condition

        provs = []
        for side in (fL, fR):
            for c in dom_condition(side):
                r = _decide_fn(c, self.ctx)
                if r is T3.NO:
                    return f"domain empty: applying {name} requires {to_str(c)} (contradicted)"
                if r is T3.UNKNOWN and not any(c is p for p in provs):
                    provs.append(c)
                    self._oid += 1
                    self.obligations.append(Obligation(
                        self._oid, c, [self._sid + 1],
                        note=f"domain condition of applying {name}",
                    ))
        notes = []
        if inj is False:
            notes.append(f"{name} is not injective: forward implication only, "
                         "later solutions must be re-verified")
        elif inj is None:
            notes.append(f"injectivity of {name} undeclared: proceed with care")
        out = self._commit_eq(T.mk(T.S("Eq"), (fL, fR)), f"applied {name} to both sides")
        out += self._proviso_suffix(provs)
        if notes:
            out += "   [note: " + "; ".join(notes) + "]"
        return out

    # 变形工具箱（反向化简/凑形；ops 层为主实现，命令为薄封装）

    def _reshape_drive(self, name, fn, path_s, args=()):
        """变形命令统一驱动。

        解析目标（可选 path）-> fn(子项, *args) -> (新项, None) 或 (None, 错误文本)。
        目标为等式且未给 path 时对两侧分别应用（Mathematica 等式线程语义），
        任一侧失败即整体拒绝（永不半改）。有变化才提交 scheme:<name> 步。
        """
        self._check_locked()
        sub, path, err = self._resolve_target(path_s)
        if err:
            return err
        if isinstance(sub, T.Expr) and sub.head.name == "Eq" and not path_s:
            targets = [(sub.args[0], path + (0,)), (sub.args[1], path + (1,))]
        else:
            targets = [(sub, path)]
        before = self.current
        cur = self.current
        changed = False
        for tsub, tpath in targets:
            res, msg = fn(tsub, *args)
            if msg:
                return msg
            if res is not tsub:
                cur = T.replace_at(cur, tpath, res)
                changed = True
        if not changed:
            return f"{to_str(before)}   [{name}: no change]"
        self.current = cur
        self._sid += 1
        self.log.append(Step(
            self._sid, f"scheme:{name}", tuple(path), before, cur, "YES",
            cost(cur) - cost(before), note=name,
        ))
        self._remember(cur)
        return to_str(cur)

    def expand_at(self, path_s=None):
        """:expand [path]：展开乘积/幂（暴露 simplify.expand）；等式作用两侧。"""
        return self._reshape_drive("expand", lambda t: (expand(t), None), path_s)

    def extract(self, f_s, path_s=None):
        """:extract <f> [path]：提公因子 ab+ac -> a(b+c)。

        逐项整除（每项经 mk 消去同名因子，负幂残留 = 不可整除的诚实信号），
        以 f·Σq_i 重组；equivalent=YES 背书。仅对和式目标有意义。
        """
        f = self._parse_in(f_s)

        def fn(t):
            if not (isinstance(t, T.Expr) and t.head.name == "Plus"):
                return None, f"extract: {to_str(t)} is not a sum (nothing to factor out of)"
            qs = []
            for a in t.args:
                qa = simplify(T.div(a, f))
                if _neg_pow_of(qa, f):
                    return None, (f"extract refused: {to_str(f)} is not "
                                  f"a common factor of {to_str(t)}")
                qs.append(qa)
            res = T.times(f, T.mk(T.S("Plus"), tuple(qs)))
            if res is t:
                return t, None
            # 构造本身 = 分配律逆（结构可靠），验证接受 PROBABLE
            # （超越因子如 ln(x-k) 的等价判定采样最高只到 PROBABLE）
            if _equivalent_fn(res, t, self.ctx) not in (T3.YES, T3.PROBABLE):
                return None, "extract refused: verification failed"
            return res, None

        return self._reshape_drive("extract", fn, path_s)

    def separate_at(self, path_s=None):
        """:separate [path]：(a+b)/c -> a/c + b/c（ops.separate；:together 的对偶）。"""
        from cas.ops import separate

        return self._reshape_drive("separate", lambda t: (separate(t), None), path_s)

    def complete_square(self, var_s, path_s=None):
        """:complete_square <var> [path]：二次型配方 a x^2+b x+c -> a(x+h)^2+k。

        系数经 ops.coefficient 提取（非多项式诚实拒绝）；该侧无 x^2 项视为
        无变化（等式另一侧可独立配方）；结果构造后 equivalent 背书。
        """
        from cas.ops import coefficient
        from cas.errors import PolyError

        x = T.S(var_s)

        def fn(t):
            try:
                a = coefficient(t, x, 2)
                b = coefficient(t, x, 1)
                c = coefficient(t, x, 0)
            except PolyError:
                return None, f"complete_square: {to_str(t)} is not polynomial in {var_s}"
            if T.is_num(a) and T.num_val(a) == 0:
                return t, None
            h = simplify(T.div(b, T.times(T.N(2), a)))
            k = simplify(T.plus(c, T.neg(T.div(T.pw(b, T.N(2)), T.times(T.N(4), a)))))
            res = T.plus(T.times(a, T.pw(T.plus(x, h), T.N(2))), k)
            if _equivalent_fn(res, t, self.ctx) is T3.NO:
                return None, "complete_square: internal verification failed (refused)"
            return res, None

        return self._reshape_drive("complete_square", fn, path_s)

    # 微积分战术补全

    def usub(self, eq_s):
        """:usub t=g(x)：正向换元（当前式须为惰性积分）。

        两级策略：
        ① 精确微分分解：body/g'(x) 把 g(x)->t 代入后无 x -> 干净换元 ∫f(t)dt
          （defint_auto 的探测逻辑人选版，避免逆函数路线的丑陋形态）；
        ② 退化：主支逆路线 x=h(t) 全代入（与 :subst 同款语义）。
        正确性由用户后续 !verify 微分回验背书。
        """
        self._check_locked()
        if self.current is None:
            return "empty session"
        from cas.diff import d as _d
        from cas.solve import solve as _solve

        eq = parse(eq_s)
        if not (isinstance(eq, T.Expr) and eq.head.name == "Eq"):
            return "usage: :usub t=g(x)  (current must be an inert integral)"
        if not (isinstance(self.current, T.Expr) and self.current.head.name == "Integrate"
                and len(self.current.args) == 1 and isinstance(self.current.args[0], T.Bound)):
            return "usub: current must be an inert integral (integrate(f, x))"
        lhs, rhs = eq.args
        x, body = T.open_bound(self.current.args[0])
        fv = T.free_vars(body) | {x}
        if isinstance(lhs, T.Sym) and lhs not in fv and (T.free_vars(rhs) & fv):
            newvar, gexpr = lhs, rhs
        elif isinstance(rhs, T.Sym) and rhs not in fv and (T.free_vars(lhs) & fv):
            newvar, gexpr = rhs, lhs
        else:
            return "usub: 等式一边必须是当前式中未出现的新变量（裸符号）"
        before = self.current
        gp = _d(gexpr, x)
        # 一级：精确微分分解（顶层因子消去——mk 不拆 (a*b)^-1，直接 div 会留残渣）
        q = _quotient_cancel(body, gp)
        q2 = T.subst(q, {gexpr: newvar})
        if x not in T.free_vars(q2):
            new_int = T.mk(T.S("Integrate"), (T.mk_bound(newvar, q2),))
            note = f"u-substitution {to_str(gexpr)} = {newvar.name} (exact differential)"
        else:
            # 二级：主支逆路线
            r = _solve(T.plus(gexpr, T.neg(newvar)), x)
            if r.status != "ok" or not r.solutions:
                return (f"usub: neither exact differential nor invertible substitution "
                        f"({to_str(gexpr)} = {newvar.name}; solve: {r.note or r.status})")
            ht = r.solutions[0]
            nb = T.subst(body, {x: ht})
            dht = _d(ht, newvar)
            new_int = T.mk(T.S("Integrate"),
                           (T.mk_bound(newvar, simplify(T.times(nb, dht))),))
            note = (f"u-substitution {to_str(gexpr)} = {newvar.name} "
                    f"(inverse route x = {to_str(ht)})")
        self.current = new_int
        self._sid += 1
        self.log.append(Step(self._sid, "scheme:usub", (), before, self.current, "YES",
                             cost(self.current) - cost(before), note=note))
        self._remember(self.current)
        return self.current

    def lhop(self, var_s, point_s):
        """:lhop <var> <point>：手动洛必达一步。

        当前式经 num_den 提取分子分母，在 point 处须为 0/0 或 ±∞/±∞ 不定形
        （limits.limit 判定），否则诚实拒绝并报告两端极限；一步 = D(F)/D(G)。
        """
        self._check_locked()
        if self.current is None:
            return "empty session"
        from cas.ops import num_den
        from cas.limits import limit
        from cas.diff import d as _d

        F, G = num_den(self.current)
        x = T.S(var_s)
        pt = self._parse_bound(point_s)

        def _is_inf(v):
            if v is T.INFINITY:
                return True
            return (isinstance(v, T.Expr) and v.head.name == "Times"
                    and any(a is T.INFINITY for a in v.args))

        lf = limit(F, x, pt)
        lg = limit(G, x, pt)
        zero_zero = lf is T.ZERO and lg is T.ZERO
        inf_inf = _is_inf(lf) and _is_inf(lg)
        if not (zero_zero or inf_inf):
            fmt = lambda v: to_str(v) if v is not None else "UNKNOWN"
            return (f"lhop: not an indeterminate form at {point_s} "
                    f"(numerator -> {fmt(lf)}, denominator -> {fmt(lg)})")
        nf = _d(F, x)
        ng = _d(G, x)
        before = self.current
        self.current = T.div(nf, ng)
        self._sid += 1
        self.log.append(Step(
            self._sid, "scheme:lhop", (), before, self.current, "YES",
            cost(self.current) - cost(before),
            note="l'Hopital 0/0" if zero_zero else "l'Hopital inf/inf",
        ))
        self._remember(self.current)
        return self.current

    # ---------------- 会话规则/名词动词切换/Refine（第一批采购清单） ----------------

    def add_rule(self, text):
        """:rule 内联定理定义（maxima tellsimp 同款）：语法同规则文件行
        （rule id = lhs -> rhs [guard ... as ... prio ... auto]），origin='session'。
        规则库从文件升级为会话参与者；转录自动收录，回放时重建。"""
        self._check_locked()
        body = text.strip()
        if not body.startswith("rule "):
            body = "rule " + body
        r = loader.parse_rule_line(body, origin="session")
        existed = r.id in self.rules.rules
        self.rules.add(r)
        return f"{'redefined' if existed else 'defined'}: {r.id}"

    def unrule(self, rid):
        """删除会话内联规则（文件规则不可删——文件是定理库本体）。"""
        r = self.rules.rules.get(rid)
        if r is None:
            return f"no rule: {rid}"
        if r.origin != "session":
            return f"rule {rid} comes from {r.origin}; only session rules can be removed"
        self.rules.remove(rid)
        return f"removed: {rid}"

    def list_rules(self):
        out = []
        for rid in sorted(self.rules.rules):
            r = self.rules.rules[rid]
            g = f" guard {to_str(r.guard)}" if r.guard is not None else ""
            d = f" as {r.direction}" if r.direction else ""
            a = " auto" if r.auto else ""
            out.append(f"{rid:16s} [{r.origin:10s} prio {r.priority:3d}] "
                       f"{to_str(r.pattern)} -> {to_str(r.template)}{g}{d}{a}")
        return "\n".join(out) if out else "(no rules)"

    def value(self):
        """名词 -> 动词：全式求值惰性形式（Quote 脱壳、惰性 Integrate 实算、D 名词微分）。

        求值失败（如不可积）的惰性头保持名词（诚实）。每次求值入账 kernel 步。
        """
        self._check_locked()
        if self.current is None:
            return "empty session"
        r, changed = _eval_inert(self.current, self.budget)
        if not changed:
            return f"{to_str(self.current)}   [no inert form evaluated]"
        before = self.current
        self.current = r
        self._kernel_step("value", self.current, before=before)
        self._remember(self.current)
        return to_str(self.current)

    def simplify_at(self, path):
        """只化简指定路径的子项，其余子树指针不变（子项操作通道）。"""
        self._check_locked()
        if self.current is None:
            return "empty session"
        sub = T.term_at(self.current, path)
        nxt = simplify(sub, self.budget)
        if nxt is sub:
            return f"{to_str(sub)}   [no simplification at path {path}]"
        before = self.current
        self.current = T.replace_at(self.current, path, nxt)
        self._sid += 1
        self.log.append(Step(
            self._sid, "scheme:simplify_at", tuple(path), before, self.current, "YES",
            cost(self.current) - cost(before), note=f"simplify at path {tuple(path)}",
        ))
        self._remember(self.current)
        return to_str(self.current)

    def auto_at(self, path):
        """对指定路径的子项跑自动重写（simplify 不动点 + auto 规则），其余不动。"""
        self._check_locked()
        if self.current is None:
            return "empty session"
        sub = T.term_at(self.current, path)
        auto_rules = sorted(
            (r for r in self.rules.rules.values() if r.auto),
            key=lambda r: r.priority,
        )
        seen = {sub._h}
        for _ in range(10):
            s0 = simplify(sub, self.budget)
            if s0 is not sub:
                sub = s0
                seen.add(sub._h)
            changed = False
            for p in T.all_paths(sub):
                for r in auto_rules:
                    res = apply_rule(r, sub, p, self._guard_eval, self.budget)
                    if res.guard == "YES" and res.term._h not in seen \
                            and cost(res.term) <= cost(sub):
                        sub = res.term
                        seen.add(sub._h)
                        changed = True
                        break
                if changed:
                    break
            if not changed:
                break
        if sub is T.term_at(self.current, path):
            return f"{to_str(sub)}   [no auto-rewrite at path {path}]"
        before = self.current
        self.current = T.replace_at(self.current, path, sub)
        self._sid += 1
        self.log.append(Step(
            self._sid, "scheme:auto_at", tuple(path), before, self.current, "YES",
            cost(self.current) - cost(before), note=f"auto at path {tuple(path)}",
        ))
        self._remember(self.current)
        return to_str(self.current)

    def value_at(self, path):
        """只求值指定路径子项中的惰性头（Quote/Integrate/D），其余不动。"""
        self._check_locked()
        if self.current is None:
            return "empty session"
        sub = T.term_at(self.current, path)
        r, changed = _eval_inert(sub, self.budget)
        if not changed:
            return f"{to_str(sub)}   [no inert form at path {path}]"
        before = self.current
        self.current = T.replace_at(self.current, path, r)
        self._sid += 1
        self.log.append(Step(
            self._sid, "scheme:value_at", tuple(path), before, self.current, "YES",
            cost(self.current) - cost(before),
            note=f"evaluate inert forms at path {tuple(path)}",
        ))
        self._remember(self.current)
        return to_str(self.current)

    def integrate_at(self, path):
        """对指定路径子项做积分并原地替换，其余不动。

        子项是惰性 Integrate 名词时求值该积分（点选积分号即算它），
        否则对其做不定积分。两个语义都经既有内核算法 + 验证。
        """
        self._check_locked()
        if self.current is None:
            return "empty session"
        from cas.integrate import integrate as zz_int
        from cas.errors import PolyError

        sub = T.term_at(self.current, path)
        if isinstance(sub, T.Expr) and sub.head.name == "Integrate" \
                and len(sub.args) == 1 and isinstance(sub.args[0], T.Bound):
            x, body = T.open_bound(sub.args[0])
            try:
                res, ok, method, provisos = zz_int(body, x)
            except PolyError:
                return f"unsupported integrand at path {path}"
            note = f"evaluate Integrate at path {tuple(path)}"
        else:
            x = self._pick_var(sub)
            if x is None:
                return "no variable in subterm"
            try:
                res, ok, method, provisos = zz_int(sub, x)
            except PolyError:
                return f"unsupported integrand at path {path}"
            note = f"algorithm=integrate[{method}] at path {tuple(path)}"
        before = self.current
        self.current = T.replace_at(self.current, path, res)
        self._sid += 1
        self.log.append(Step(
            self._sid, "kernel:integrate_at", tuple(path), before, self.current, "YES",
            cost(self.current) - cost(before), note=note,
        ))
        self._remember(self.current)
        out = f"{to_str(res)}   [{'VERIFIED' if ok else 'UNVERIFIED'}, method: {method}]"
        if provisos:
            out += "   [proviso: " + " && ".join(to_str(g) for g in provisos) + "]"
        return out

    def mrefine(self):
        """:refine：账本驱动化简（decide 的第二大消费者）——只重写 decide=YES 的结构，
        判不动的保持原样（永不静默错）。"""
        self._check_locked()
        if self.current is None:
            return "empty session"
        from cas.refine import refine as zz_refine

        r, changed = zz_refine(self.current, self.ctx)
        if not changed:
            return f"{to_str(self.current)}   [no refinement: ledger decides nothing more]"
        before = self.current
        self.current = r
        self._sid += 1
        self.log.append(Step(
            self._sid, "scheme:refine", (), before, r, "YES",
            cost(r) - cost(before), note="ledger-driven simplification",
        ))
        self._remember(r)
        return to_str(r)

    def mlatex(self):
        """:latex：当前式的 LaTeX 输出（纯展示层）。"""
        from cas.latex import to_latex

        if self.current is None:
            return "empty session"
        return to_latex(self.current)


def run():
    """REPL：表达式即当前式；%N 复用历史产出；命令转录可保存/回放。
    分发全部走 Session.handle（与回放同路径）。"""
    s = Session()
    print("pyCAS session. :help for commands; expression to make current; %N reuses history.")
    if s.load_error:
        print(f"warning: rules load failed: {s.load_error}")
    while True:
        try:
            line = input(">> ")
        except EOFError:
            break
        if line.strip() in (":q", ":quit"):
            break
        out = s.handle(line)
        if out:
            print(out)


if __name__ == "__main__":
    run()
