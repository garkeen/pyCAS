"""工作流引擎：步骤 DAG + 带类型推导边 + 守卫传播。

步骤不是等式链条——步骤间的逻辑关系由推导类型（derivation）决定：
rewrite 是等价，both-sides 可逆时是等价、不可逆时是蕴含，solve 是
"解集等价"，split 是析取。验证器按推导类型分派到域判定器。

逻辑层 = 命题复合（and3/or3）+ 域特定可判定原子（domain.equal/
decide/dom_condition）。不含运行时量词推理——全称事实是图书馆
引理，按模式匹配实例化。

守卫条件：步骤创建时自动从内容经 dom_condition 提取定义域约束，
存入步骤载荷；BothSides 传播前驱守卫 + 运算元守卫；mul/div 额外
要求运算元 ≠ 0，由 decide 在已积累守卫的上下文中检查。
"""

from dataclasses import dataclass
from fractions import Fraction as Fr

from cas import term as T
from cas.term import Expr, Sym, Int, S, N
from cas.domains.base import T3
from cas.domains import poly_domain, ratfunc_domain
from cas.domains.poly import from_term as poly_from_term
from cas.domains.q import Q_RING
from cas.qarith import fold, eval_exact, EvalNumError
from cas.domain import dom_condition
from cas.context import Context
from cas.decide import decide


# ---------------------------------------------------------------------------
# 推导类型：封闭 ADT 层次
# ---------------------------------------------------------------------------

class Derivation:
    """推导类型。每种类型自带验证规则，分派到域判定器 + 命题复合。"""
    pass


@dataclass(frozen=True, slots=True)
class Claim(Derivation):
    """断言入账——无前驱，守卫自动提取。逻辑地位：假设。"""
    pass


@dataclass(frozen=True, slots=True)
class BothSides(Derivation):
    """等式两边同施加运算。
    可逆（add/sub/mul by ≠0/div by ≠0）⟺ 等价；
    不可逆（mul by 0）⟹ 蕴含且信息丢失。"""
    pred: int              # 前驱步骤 id
    op: str                # "add" | "sub" | "mul" | "div"
    operand: object        # 运算元（Term）


@dataclass(frozen=True, slots=True)
class Rewrite(Derivation):
    """域标准形重写——前驱经 normalize 后等价。"""
    pred: int
    domain: str = ""       # 域名（空=多项式域自动）


@dataclass(frozen=True, slots=True)
class Solve(Derivation):
    """解线性方程——输入等式步骤，输出 var = 解。
    逻辑地位：解集等价（完备时 ⟺）。"""
    pred: int
    var: Sym


@dataclass(frozen=True, slots=True)
class Split(Derivation):
    """条件分支切割——一步析取为多步。"""
    pred: int
    condition: object      # 切割条件（Term）


@dataclass(frozen=True, slots=True)
class Subst(Derivation):
    """代换——前驱中某变量替换为值，纯句法操作。蕴含。"""
    pred: int
    var: Sym
    value: object           # Term


# ---------------------------------------------------------------------------
# 步骤：不可变记录
# ---------------------------------------------------------------------------

@dataclass(frozen=True, slots=True)
class Step:
    id: int
    content: object        # Term（等式 / 表达式 / 不等式）
    derivation: Derivation
    guards: tuple          # (Term, ...) 守卫条件
    status: str = "open"   # "open" | "dead"
    note: str = ""


# ---------------------------------------------------------------------------
# 工作流
# ---------------------------------------------------------------------------

class Workflow:
    """步骤 DAG + 验证器。

    步骤创建时自动提取守卫、验证推导合理性。验证失败标 dead。
    步骤引用前驱用 id（不可变 DAG），不持 Python 对象引用。
    """

    def __init__(self):
        self._steps: dict[int, Step] = {}
        self._next_id = 0

    def get(self, sid: int) -> Step:
        return self._steps[sid]

    def all_steps(self):
        return list(self._steps.values())

    def add(self, content, derivation, note="") -> Step:
        """创建步骤：提取守卫 → 验证 → 存储。"""
        guards = self._extract_guards(content, derivation)
        verdict = self._verify(content, derivation, guards)
        status = "dead" if verdict is T3.NO else "open"
        step = Step(id=self._next_id, content=content,
                    derivation=derivation, guards=guards,
                    status=status, note=note)
        self._steps[self._next_id] = step
        self._next_id += 1
        return step

    # --- 守卫提取 ---

    def _extract_guards(self, content, derivation) -> tuple:
        guards = list(dom_condition(content))
        if isinstance(derivation, BothSides):
            pred = self._steps.get(derivation.pred)
            if pred is not None:
                guards = list(pred.guards) + guards
            guards += list(dom_condition(derivation.operand))
            if derivation.op in ("mul", "div"):
                guards.append(T.mk(S("Ne"), (derivation.operand, T.ZERO)))
        elif isinstance(derivation, (Rewrite, Solve, Split, Subst)):
            pred = self._steps.get(derivation.pred)
            if pred is not None:
                guards = list(pred.guards) + guards
            if isinstance(derivation, Subst):
                guards += list(dom_condition(derivation.value))
        return tuple(guards)

    # --- 验证 ---

    def _verify(self, content, derivation, guards) -> T3:
        if isinstance(derivation, Claim):
            return T3.YES
        if isinstance(derivation, BothSides):
            return self._verify_both_sides(content, derivation, guards)
        if isinstance(derivation, Rewrite):
            return self._verify_rewrite(content, derivation)
        if isinstance(derivation, Solve):
            return self._verify_solve(content, derivation)
        if isinstance(derivation, Split):
            return self._verify_split(content, derivation)
        if isinstance(derivation, Subst):
            return self._verify_subst(content, derivation)
        return T3.UNKNOWN

    def _verify_both_sides(self, content, d: BothSides, guards) -> T3:
        pred = self._steps.get(d.pred)
        if pred is None or not _is_eq(pred.content):
            return T3.NO
        lhs, rhs = pred.content.args
        op = d.op
        if op == "add":
            exp = T.eq(T.plus(lhs, d.operand), T.plus(rhs, d.operand))
        elif op == "sub":
            exp = T.eq(T.plus(lhs, T.neg(d.operand)),
                       T.plus(rhs, T.neg(d.operand)))
        elif op == "mul":
            exp = T.eq(T.times(lhs, d.operand), T.times(rhs, d.operand))
        elif op == "div":
            exp = T.eq(T.times(lhs, T.pw(d.operand, T.N(-1))),
                       T.times(rhs, T.pw(d.operand, T.N(-1))))
        else:
            return T3.NO
        # 内容检查：poly 域判等（多项式方程完全判定）
        if not _eq_equal(content, exp):
            return T3.NO
        # 守卫检查：mul/div 要求运算元 ≠ 0
        if op in ("mul", "div"):
            ctx = Context()
            for g in guards:
                ctx.assume(g)
            r = decide(T.mk(S("Ne"), (d.operand, T.ZERO)), ctx)
            if r is T3.NO:
                return T3.NO          # 运算元为零：变换不可逆，标 dead
            # UNKNOWN 允许——守卫未定，步骤 open 但带条件
        return T3.YES

    def _verify_rewrite(self, content, d: Rewrite) -> T3:
        pred = self._steps.get(d.pred)
        if pred is None:
            return T3.NO
        n = _normalize_eq(pred.content)
        if _eq_equal(content, n):
            return T3.YES
        return T3.NO

    def _verify_subst(self, content, d: Subst) -> T3:
        pred = self._steps.get(d.pred)
        if pred is None:
            return T3.NO
        substituted = _substitute(pred.content, d.var, d.value)
        if _eq_equal(content, substituted):
            return T3.YES
        n = _normalize_eq(substituted)
        if _eq_equal(content, n):
            return T3.YES
        return T3.NO

    def _verify_solve(self, content, d: Solve) -> T3:
        pred = self._steps.get(d.pred)
        if pred is None or not _is_eq(pred.content):
            return T3.NO
        lhs, rhs = pred.content.args
        diff = T.plus(lhs, T.neg(rhs))
        p = poly_from_term(Q_RING, diff, (d.var,))
        if p is None:
            return T3.UNKNOWN
        # 线性：a*x + b = 0 → x = -b/a
        deg = p.deg_in(0)
        if deg != 1:
            return T3.UNKNOWN          # 非线性：demo 不处理
        a = _coef(p, 1)
        b = _coef(p, 0)
        if a == 0:
            return T3.NO
        sol = -b / a
        # 预期内容：var = sol
        exp = T.eq(d.var, N(sol))
        if not _eq_equal(content, exp):
            return T3.NO
        # 回代验证
        try:
            v = eval_exact(diff, {d.var: sol})
            if v != 0:
                return T3.NO
        except EvalNumError:
            pass
        return T3.YES

    def _verify_split(self, content, d: Split) -> T3:
        pred = self._steps.get(d.pred)
        if pred is None:
            return T3.NO
        # split 的验证：条件 + ¬条件 覆盖全空间（排中律）
        # demo：接受任何 split（验证留给上层逻辑复合）
        return T3.YES


# ---------------------------------------------------------------------------
# 谓词助手
# ---------------------------------------------------------------------------

def _is_eq(t) -> bool:
    return isinstance(t, Expr) and t.head.name == "Eq"


def _eq_equal(a, b) -> bool:
    """等式判等：先试 ratfunc 域（K(x) ⊇ K[x]，含除法），退化试 poly。"""
    if not _is_eq(a) or not _is_eq(b):
        return a is b
    la, ra = a.args
    lb, rb = b.args
    da = T.plus(la, T.neg(ra))
    db = T.plus(lb, T.neg(rb))
    vs = sorted(T.free_vars(da) | T.free_vars(db), key=lambda s: s.name)
    if vs:
        rf = ratfunc_domain(*vs)
        r = rf.equal(da, db)
        if r is T3.YES:
            return True
        if r is T3.NO:
            return False
    fa, fb = fold(da), fold(db)
    return fa is fb


def _vars_of(t):
    """从等式提取变量集。"""
    if not _is_eq(t):
        return sorted(T.free_vars(t), key=lambda s: s.name)
    la, ra = t.args
    d = T.plus(la, T.neg(ra))
    return sorted(T.free_vars(d), key=lambda s: s.name)


def _coef(p, power: int) -> Fr:
    """单变量 Poly 的指定幂次系数。"""
    for k, c in p.monos:
        if k[0] == power:
            return c
    return Fr(0)


def _substitute(t, var: Sym, value):
    """树代换：var → value，纯句法。不穿透绑定体（demo 级别）。"""
    if isinstance(t, Sym):
        return value if t is var else t
    if isinstance(t, Expr):
        return T.mk(t.head, tuple(_substitute(a, var, value) for a in t.args))
    return t


def _normalize_eq(t):
    """等式或表达式的域标准形：先试 ratfunc（K(x) ⊇ K[x]），退化试 poly。"""
    if not _is_eq(t):
        vs = sorted(T.free_vars(t), key=lambda s: s.name)
        if vs:
            rf = ratfunc_domain(*vs)
            n = rf.normalize(t)
            if n is not None:
                return n
            dom = poly_domain(*vs)
            n = dom.normalize(t)
            if n is not None:
                return n
        return t
    lhs, rhs = t.args
    d = T.plus(lhs, T.neg(rhs))
    vs = sorted(T.free_vars(d), key=lambda s: s.name)
    if vs:
        rf = ratfunc_domain(*vs)
        n = rf.normalize(d)
        if n is not None:
            return T.eq(n, T.ZERO)
        dom = poly_domain(*vs)
        n = dom.normalize(d)
        if n is not None:
            return T.eq(n, T.ZERO)
    return t
