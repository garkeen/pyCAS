"""初等函数定义。

准入纪律：rules 只收无条件恒等式；带定义域条件的改写（Log(uv) 拆分、
√(x²)=|x| 类分支破裂者）一律不收——它们将来以带守卫的规则或域层
标准形进入，绝不冒充无条件真理。
"""

from fractions import Fraction as Fr

import library.api as lib
from cas import term as T
from cas.term import S, mk


# 函数定义域条件注册（图书馆声明，内核运行时查——无环）
lib.register_domain_cond("Log",
    lambda t: [mk(S("Gt"), (t.args[0], T.ZERO))])
lib.register_domain_cond("Sqrt",
    lambda t: [mk(S("Ge"), (t.args[0], T.ZERO))])


lib.function(name="Sin", print_name="sin", arity=1, real_on_real=True,
             bound=(Fr(-1), Fr(1)))
lib.function(name="Cos", print_name="cos", arity=1, real_on_real=True,
             bound=(Fr(-1), Fr(1)))

# tan 的定义等式是条件改写（要求 cos ≠ 0），按纪律不进 rules，
# 记入 note 由函数结构层消费。
lib.function(name="Tan", print_name="tan", arity=1,
             note="tan(x) = sin(x)/cos(x)，条件 cos(x)≠0")

lib.function(name="Exp", print_name="exp", arity=1, real_on_real=True,
             rule_lines=(
                 "rule exp_add = exp(?a)*exp(?b) -> exp(?a + ?b)",
             ),
             note="Exp∘Log 主支恒等属条件改写，未收")

lib.function(name="Log", print_name="log", arity=1,
             note="定义域 x>0；Log(uv) 拆分为分支破裂改写，未收")

lib.function(name="Sqrt", print_name="sqrt", arity=1,
             note="主支平方根；√(x²)=±x 分支破裂，未收")

lib.function(name="Abs", print_name="abs", arity=1, real_on_real=True)

lib.function(name="Atan", print_name="atan", arity=1, real_on_real=True,
             note="值域 (-π/2, π/2)：含 π 的精确界待常数引理组合后声明")
