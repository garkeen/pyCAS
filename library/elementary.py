# -*- coding: utf-8 -*-
"""初等函数定义。

准入纪律：rules 只收无条件恒等式；带定义域条件的改写（Log(uv) 拆分、
√(x²)=|x| 类分支破裂者）一律不收——它们将来以带守卫的规则或域层
标准形进入，绝不冒充无条件真理。

导数模板纪律：deriv 只收无条件成立的导数公式（相对函数自身定义域）。
分支破裂者（|x| 的符号导数）置 None 并记 deriv_note。
模板语义：f'(u) = 模板[DB(0) := u]，链式法则因子由微分层乘上。
"""

from fractions import Fraction as Fr

import library.api as lib
from cas import term as T
from cas.term import S, mk

_U = T.DB_(0)   # 导数模板占位：参数位置


# 函数定义域条件注册（图书馆声明，内核运行时查——无环）
lib.register_domain_cond("Log",
    lambda t: [mk(S("Gt"), (t.args[0], T.ZERO))])
lib.register_domain_cond("Sqrt",
    lambda t: [mk(S("Ge"), (t.args[0], T.ZERO))])


lib.function(name="Sin", print_name="sin", arity=1, real_on_real=True,
             bound=(Fr(-1), Fr(1)),
             deriv=T.cos(_U))
lib.function(name="Cos", print_name="cos", arity=1, real_on_real=True,
             bound=(Fr(-1), Fr(1)),
             deriv=T.times(T.MONE, T.sin(_U)))

# tan 的定义等式是条件改写（要求 cos ≠ 0），按纪律不进 rules，
# 记入 note 由函数结构层消费。导数 1/cos² 在 tan 的定义域内无条件成立。
lib.function(name="Tan", print_name="tan", arity=1,
             deriv=T.pw(T.cos(_U), T.N(-2)),
             note="tan(x) = sin(x)/cos(x)，条件 cos(x)≠0")

lib.function(name="Sinh", print_name="sinh", arity=1, real_on_real=True,
             deriv=T.cosh(_U))
lib.function(name="Cosh", print_name="cosh", arity=1, real_on_real=True,
             deriv=T.sinh(_U))
lib.function(name="Tanh", print_name="tanh", arity=1, real_on_real=True,
             deriv=T.pw(T.cosh(_U), T.N(-2)))

lib.function(name="Exp", print_name="exp", arity=1, real_on_real=True,
             rule_lines=(
                 "rule exp_add = exp(?a)*exp(?b) -> exp(?a + ?b) auto",
             ),
             deriv=T.exp(_U),
             note="Exp∘Log 主支恒等属条件改写，未收")

lib.function(name="Log", print_name="log", arity=1,
             deriv=T.pw(_U, T.N(-1)),
             note="定义域 x>0；Log(uv) 拆分为分支破裂改写，未收")

lib.function(name="Sqrt", print_name="sqrt", arity=1,
             deriv=T.times(T.N(Fr(1, 2)), T.pw(_U, T.N(Fr(-1, 2)))),
             note="主支平方根；√(x²)=±x 分支破裂，未收")

# |x| 非负、零集恰为 {0}：值域界与零点结构作为图书馆声明数据，
# 判定层（_nneg/_interval/符号规则）据此消费，不据函数名硬编码。
lib.function(name="Abs", print_name="abs", arity=1, real_on_real=True,
             bound=(Fr(0), None), zero_iff_arg_zero=True,
             deriv=mk(S("Piecewise"),
                      (T.ONE, mk(S("Gt"), (_U, T.ZERO)),
                       T.MONE, mk(S("Lt"), (_U, T.ZERO)))),
             note="D|x| = piecewise(1 if x>0, -1 if x<0)；x=0 无分支（不可导）")

lib.function(name="Atan", print_name="atan", arity=1, real_on_real=True,
             deriv=T.pw(T.plus(T.ONE, T.pw(_U, T.TWO)), T.N(-1)),
             note="值域 (-π/2, π/2)：含 π 的精确界待常数引理组合后声明")
