# -*- coding: utf-8 -*-
"""初等模块的装配（v4 §7.2 的 `module.py`）。

常数与函数的一切数学语义都在此处声明，经 `install(builder)` 进运行期。
**import 本模块不注册任何东西**——装配只发生在 `bootstrap()` 调用 `install` 时。

准入纪律（不变）：

· 规则只收**无条件**恒等式。带定义域条件的改写（`Log(uv)` 拆分、`√(x²)=|x|`
  类分支破裂者）一律不收，它们将来以带守卫的规则或域层标准形进入，绝不冒充
  无条件真理。
· 导数模板只收无条件成立的导数公式（相对函数自身定义域）。分支破裂者
  （`|x|` 的符号导数）置 None 并写入 `deriv_note`。
  模板语义：`f'(u) = 模板[DB(0) := u]`，链式法则因子由微分层乘上。
"""

from fractions import Fraction as Fr

from cas.syntax import term as T
from cas.syntax.term import S, mk

_U = T.DB_(0)          # 导数模板占位：参数位置


def install(builder) -> None:
    """把初等常数与函数声明装进 builder（bootstrap 按依赖序调用）。"""
    _declare_constants(builder)
    _declare_functions(builder)


# ---------------------------------------------------------------------------
# 常数：性质声明是**引理**（可判定粗界与正性），不是公理废话
# ---------------------------------------------------------------------------

def _declare_constants(builder) -> None:
    builder.declare_constant(name="pi", print_name="π", real=True,
                             positive=True, bounds=(3, 4))
    builder.declare_constant(name="e", print_name="e", real=True,
                             positive=True, bounds=(2, 3))
    builder.declare_constant(name="i", print_name="i", real=False)
    builder.declare_constant(name="gamma", print_name="γ", real=True,
                             positive=True, bounds=(0, 1))


# ---------------------------------------------------------------------------
# 函数：印名 / 元数 / 值域界 / 零点结构 / 规则源 / 导数模板 / 定义域条件
# ---------------------------------------------------------------------------

def _declare_functions(builder) -> None:
    # 定义域条件（函数声明的一部分，随其登记）
    builder.declare_domain_cond("Log",
        lambda t: [mk(S("Gt"), (t.args[0], T.ZERO))])
    builder.declare_domain_cond("Sqrt",
        lambda t: [mk(S("Ge"), (t.args[0], T.ZERO))])

    builder.declare_function(name="Sin", print_name="sin", arity=1,
                             real_on_real=True, bound=(Fr(-1), Fr(1)),
                             deriv=T.cos(_U))
    builder.declare_function(name="Cos", print_name="cos", arity=1,
                             real_on_real=True, bound=(Fr(-1), Fr(1)),
                             deriv=T.times(T.MONE, T.sin(_U)))

    # tan 的定义等式是条件改写（要求 cos ≠ 0），按纪律不进规则，记入 note
    # 由函数结构层消费。导数 1/cos² 在 tan 的定义域内无条件成立。
    builder.declare_function(name="Tan", print_name="tan", arity=1,
                             deriv=T.pw(T.cos(_U), T.N(-2)),
                             note="tan(x) = sin(x)/cos(x)，条件 cos(x)≠0")

    builder.declare_function(name="Sinh", print_name="sinh", arity=1,
                             real_on_real=True, deriv=T.cosh(_U))
    builder.declare_function(name="Cosh", print_name="cosh", arity=1,
                             real_on_real=True, deriv=T.sinh(_U))
    builder.declare_function(name="Tanh", print_name="tanh", arity=1,
                             real_on_real=True, deriv=T.pw(T.cosh(_U), T.N(-2)))

    builder.declare_function(
        name="Exp", print_name="exp", arity=1, real_on_real=True,
        rule_lines=("rule exp_add = exp(?a)*exp(?b) -> exp(?a + ?b) auto",),
        deriv=T.exp(_U),
        note="Exp∘Log 主支恒等属条件改写，未收")

    builder.declare_function(name="Log", print_name="log", arity=1,
                             deriv=T.pw(_U, T.N(-1)),
                             note="定义域 x>0；Log(uv) 拆分为分支破裂改写，未收")

    builder.declare_function(name="Sqrt", print_name="sqrt", arity=1,
                             deriv=T.times(T.N(Fr(1, 2)), T.pw(_U, T.N(Fr(-1, 2)))),
                             note="主支平方根；√(x²)=±x 分支破裂，未收")

    # |x| 非负、零集恰为 {0}：值域界与零点结构作为声明数据，
    # 判定层据此消费，不据函数名硬编码。
    builder.declare_function(
        name="Abs", print_name="abs", arity=1, real_on_real=True,
        bound=(Fr(0), None), zero_iff_arg_zero=True,
        deriv=mk(S("Piecewise"),
                 (T.ONE, mk(S("Gt"), (_U, T.ZERO)),
                  T.MONE, mk(S("Lt"), (_U, T.ZERO)))),
        note="D|x| = piecewise(1 if x>0, -1 if x<0)；x=0 无分支（不可导）")

    builder.declare_function(name="Atan", print_name="atan", arity=1,
                             real_on_real=True,
                             deriv=T.pw(T.plus(T.ONE, T.pw(_U, T.TWO)), T.N(-1)),
                             note="值域 (-π/2, π/2)：含 π 的精确界待常数引理组合后声明")
