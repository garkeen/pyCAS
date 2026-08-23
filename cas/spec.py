"""函数内核注册表 FunctionSpec（M2.0 反硬编码地基）。

每个函数头一份声明式知识，消费者全部从注册表读取：
    mk          special 特殊点构造即折叠
    diff        deriv 导数表
    decide      bound 有界性公理
    domain      dom 定义域约束
    pprint      print_name 打印名
    gen_rules   parity 奇偶性规则自动生成

纪律：新增函数只允许在此注册 + 写规则文件；
禁止在任何消费者模块里为新函数加 if 分支（代码评审验收标准）。
"""

from dataclasses import dataclass, field
from fractions import Fraction as Fr
import math

from cas import term as T
from cas.term import S, N, PI, ZERO, ONE, MONE, PV


@dataclass(frozen=True)
class FunctionSpec:
    name: str                     # 项头名（如 "Sin"）
    arity: int                    # 参数个数
    print_name: str = None        # 打印名（pprint）
    parity: str = None            # "odd" / "even"：生成 f(-x) -> ∓f(x) 规则
    deriv: object = None          # callable(arg) -> d f(arg)/d arg（链式由 diff 负责）
    bound: tuple = None           # (lo, hi) Fraction 界：decide 有界公理
    dom: object = None            # callable(term) -> [约束]：dom_condition
    special: dict = field(default_factory=dict)   # {arg 项: 值}：构造即折叠
    numeric: object = None        # callable(*float) -> float：数值求值层（仅验证/抽查通道）
    anti: object = None           # callable(arg) -> 原函数（裸函数简单积分表，定积分友好）
    inv: str = None               # 逆函数头名（主支）：f(x)=c -> x=inv(c)，带主支注释
    injective: bool = None        # 全域单射性声明（:apply_both 诚实分级用；None = 未声明）
    period: object = None         # 实周期声明（term，如 2*pi）：定积分周期折叠的候选源


SPECS = {}


def register(spec):
    SPECS[spec.name] = spec
    return spec


def get(name):
    return SPECS.get(name)


_HALF_PI = T.div(PI, N(2))
_QUARTER_PI = T.div(PI, N(4))

register(FunctionSpec(
    "Sin", 1, print_name="sin", parity="odd",
    deriv=lambda a: T.cos(a),
    bound=(Fr(-1), Fr(1)),
    special={ZERO: ZERO, PI: ZERO, _HALF_PI: ONE},
    numeric=math.sin,
    anti=lambda a: T.neg(T.cos(a)),
    inv="Arcsin",
    injective=False,
    period=T.times(N(2), T.PI),
))
register(FunctionSpec(
    "Cos", 1, print_name="cos", parity="even",
    deriv=lambda a: T.neg(T.sin(a)),
    bound=(Fr(-1), Fr(1)),
    special={ZERO: ONE, PI: MONE, _HALF_PI: ZERO},
    numeric=math.cos,
    anti=lambda a: T.sin(a),
    inv="Arccos",
    injective=False,
    period=T.times(N(2), T.PI),
))
register(FunctionSpec(
    "Tan", 1, print_name="tan", parity="odd",
    deriv=lambda a: T.plus(ONE, T.pw(T.tan(a), N(2))),
    special={ZERO: ZERO, PI: ZERO, _QUARTER_PI: ONE, T.neg(_QUARTER_PI): MONE},
    numeric=math.tan,
    anti=lambda a: T.neg(T.fn("Log")(T.fn("Cos")(a))),
    inv="Atan",
    injective=False,
    period=T.PI,
))
register(FunctionSpec(
    "Exp", 1, print_name="exp",
    deriv=lambda a: T.exp(a),
    special={ZERO: ONE},
    numeric=math.exp,
    anti=lambda a: T.exp(a),
    inv="Log",
    injective=True,
))
register(FunctionSpec(
    "Log", 1, print_name="log",
    deriv=lambda a: T.pw(a, MONE),
    dom=lambda t: [T.mk(S("Gt"), (t.args[0], ZERO))],
    special={ONE: ZERO},
    numeric=math.log,
    inv="Exp",
    injective=True,
    # 分部积分标准结果：d[a*log(a) - a] = log(a)
    anti=lambda a: T.plus(T.times(a, T.log(a)), T.neg(a)),
))
register(FunctionSpec(
    "Abs", 1, print_name="abs",
    numeric=abs,
    injective=False,
))
register(FunctionSpec(
    "Atan", 1, print_name="atan",
    deriv=lambda a: T.div(ONE, T.plus(ONE, T.pw(a, N(2)))),
    special={ZERO: ZERO, ONE: _QUARTER_PI, MONE: T.neg(_QUARTER_PI)},
    numeric=math.atan,
    injective=True,
    # 分部积分标准结果：d[a*atan(a) - ln(1+a^2)/2] = atan(a)
    anti=lambda a: T.plus(T.times(a, T.atan(a)),
                          T.neg(T.div(T.log(T.plus(ONE, T.pw(a, N(2)))), N(2)))),
))
register(FunctionSpec(
    "Arcsin", 1, print_name="arcsin",
    deriv=lambda a: T.div(ONE, T.sqrt(T.plus(ONE, T.neg(T.pw(a, N(2)))))),
    dom=lambda t: [T.mk(S("Ge"), (t.args[0], MONE)), T.mk(S("Le"), (t.args[0], ONE))],
    special={ZERO: ZERO, ONE: _HALF_PI, MONE: T.neg(_HALF_PI)},
    numeric=math.asin,
    injective=True,
))
register(FunctionSpec(
    "Arccos", 1, print_name="arccos",
    deriv=lambda a: T.neg(T.div(ONE, T.sqrt(T.plus(ONE, T.neg(T.pw(a, N(2))))))),
    dom=lambda t: [T.mk(S("Ge"), (t.args[0], MONE)), T.mk(S("Le"), (t.args[0], ONE))],
    special={ONE: ZERO, ZERO: _HALF_PI, MONE: PI},
    numeric=math.acos,
    injective=True,
))
# 双曲函数域（M2 梯队三）：注册即得导数/打印名/奇偶规则/特殊点折叠/数值层，
# 核心代码零改动（FunctionSpec 红利验收）；无界故不声明 bound。
register(FunctionSpec(
    "Sinh", 1, print_name="sinh", parity="odd",
    deriv=lambda a: T.cosh(a),
    special={ZERO: ZERO},
    numeric=math.sinh,
    anti=lambda a: T.cosh(a),
    injective=True,
))
register(FunctionSpec(
    "Cosh", 1, print_name="cosh", parity="even",
    deriv=lambda a: T.sinh(a),
    special={ZERO: ONE},
    numeric=math.cosh,
    anti=lambda a: T.sinh(a),
    injective=False,
))
register(FunctionSpec(
    "Tanh", 1, print_name="tanh", parity="odd",
    deriv=lambda a: T.plus(ONE, T.neg(T.pw(T.tanh(a), N(2)))),
    special={ZERO: ZERO},
    numeric=math.tanh,
    anti=lambda a: T.fn("Log")(T.fn("Cosh")(a)),
    injective=True,
))


def gen_rules(ruleset):
    """从 FunctionSpec 自动生成无条件规则（origin='spec'）。

    当前：奇偶性规则 f(-x) -> -f(x)（odd）/ f(-x) -> f(x)（even），auto 通道。
    """
    from cas.rules import Rule

    for sp in SPECS.values():
        if not sp.parity:
            continue
        u = PV("u")
        pat = T.mk(S(sp.name), (T.neg(u),))
        f_u = T.mk(S(sp.name), (u,))
        tpl = T.neg(f_u) if sp.parity == "odd" else f_u
        ruleset.add(Rule(
            id=f"{sp.name.lower()}_neg",
            pattern=pat,
            template=tpl,
            auto=True,
            origin="spec",
        ))
