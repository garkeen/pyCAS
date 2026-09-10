# -*- coding: utf-8 -*-
"""装配期注册表（v4 §7.1 的 `RuntimeBuilder`）。

`RuntimeBuilder` 是**装配期的唯一写入口**：数学模块在自己的 `install(builder)`
里把声明登记进来，装配完成后由 `Runtime` 冻结为只读快照。

**只设确有内容的类别。** v4 §7.1 举例列了 heads / rules / checkers / deciders /
definedness / algorithms / commands 七类，但空注册表就是空壳（AGENTS.md 记录的
结构病）——目前实际有内容的只有：常数、函数声明、定义域条件、恒等判定阶段、
域构建器。规则由 `math/rules.py` 从函数声明装配，checker 由 kernel 的
CheckerRegistry 管，故不在此重复设表；确有内容时再加。

**禁止 import 期修改全局状态**（v4 §7.1）：本模块只在被显式调用时写入 builder；
数学模块 import 时不注册任何东西。装配由 `runtime/bootstrap.py` 的 `bootstrap()`
显式触发。
"""

from dataclasses import dataclass
from fractions import Fraction

from cas.syntax.term import C as _mk_const
from cas.syntax.term import Const


@dataclass(frozen=True, slots=True)
class ConstantDecl:
    """数学常数：原子对象 + 可判定性质的引理声明。"""
    atom: Const
    name: str
    print_name: str
    real: bool | None = None
    positive: bool | None = None
    bounds: tuple[int, int] | None = None


@dataclass(frozen=True, slots=True)
class FunctionDecl:
    """数学函数：头名 + 印名 + 性质 + 恒等式规则源 + 导数模板。

    `rule_lines` 是规则行字符串（DSL）；解析由消费方（math/rules.py 装配规则集时）
    负责，本层保持纯数据。`deriv` 是含 `DB(0)` 占位的导数模板，语义为
    `f'(u) = 模板[DB(0) := u]`，链式法则因子由微分层乘上。分支破裂者置 None
    并写入 `deriv_note`——导数模板的准入纪律是「只收无条件可证者」。
    """
    name: str
    print_name: str
    arity: int | None
    real_on_real: bool | None = None
    bound: tuple[Fraction | None, Fraction | None] | None = None
    zero_iff_arg_zero: bool = False
    rule_lines: tuple[str, ...] = ()
    deriv: object = None
    deriv_note: str = ""
    note: str = ""


class RuntimeBuilder:
    """装配期注册表集合。重复声明即报错（准入纪律：同一声明只有一处）。"""

    def __init__(self):
        self.constants: dict[str, ConstantDecl] = {}
        self.functions: dict[str, FunctionDecl] = {}
        self.domain_conds: dict[str, object] = {}
        self.eq_stages: list = []          # (name, run)
        self.domains: list = []            # 常驻基域构建器（按注册序进阶梯）

    # --- 常数 ---

    def declare_constant(self, *, name, print_name, real=None, positive=None,
                         bounds=None) -> ConstantDecl:
        return self.register_constant(ConstantDecl(
            atom=_mk_const(name), name=name, print_name=print_name,
            real=real, positive=positive, bounds=bounds))

    def register_constant(self, decl: ConstantDecl) -> ConstantDecl:
        if decl.name in self.constants:
            raise ValueError(f"constant redeclared: {decl.name}")
        self.constants[decl.name] = decl
        return decl

    def require_constant(self, name) -> ConstantDecl:
        """取已声明的常数（装配顺序依赖由此显式化，查无即报错）。"""
        d = self.constants.get(name)
        if d is None:
            raise KeyError(f"常数未声明: {name}（检查 install 顺序）")
        return d

    # --- 函数 ---

    def declare_function(self, **kw) -> FunctionDecl:
        kw["rule_lines"] = tuple(kw.get("rule_lines", ()))
        return self.register_function(FunctionDecl(**kw))

    def register_function(self, decl: FunctionDecl) -> FunctionDecl:
        if decl.name in self.functions:
            raise ValueError(f"function redeclared: {decl.name}")
        self.functions[decl.name] = decl
        return decl

    # --- 定义域条件 / 判定阶段 / 域 ---

    def declare_domain_cond(self, name, fn) -> None:
        if name in self.domain_conds:
            raise ValueError(f"domain condition redeclared: {name}")
        self.domain_conds[name] = fn

    def register_eq_stage(self, name, run, prepend=False) -> None:
        entry = (name, run)
        if prepend:
            self.eq_stages.insert(0, entry)
        else:
            self.eq_stages.append(entry)

    def register_domain(self, domain) -> None:
        self.domains.append(domain)
