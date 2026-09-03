"""图书馆制度：一切函数与常量的定义的唯一居所（cas_v3_arch.md 二.4）。

内核（cas/）不携带任何数学语义：打印名、正性、粗界、恒等式全部由
本包声明。准入纪律——只收无条件成立的恒等式；分支破裂者一律不收
（对照 FriCAS elemntry.spad 的构造期收缩纪律）。

条目是冻结 dataclass（ADT 语义强化）：注册后不可变，注册表只增。
"""

from dataclasses import dataclass, field
from fractions import Fraction as Fr

from cas.term import C as _mk_const, Const


# ---------------------------------------------------------------------------
# 条目类型
# ---------------------------------------------------------------------------

@dataclass(frozen=True, slots=True)
class ConstantDecl:
    """数学常数：原子对象 + 可判定性质的引理声明。"""
    atom: Const                      # 驻留常数原子（term.C 创建）
    name: str                        # 内部名，如 "pi"
    print_name: str                  # 展示名，如 "π"
    real: bool | None = None         # 实数性
    positive: bool | None = None     # 正性引理
    bounds: tuple[int, int] | None = None   # 整数粗界引理 lo < c < hi


@dataclass(frozen=True, slots=True)
class FunctionDecl:
    """数学函数：头名 + 印名 + 性质 + 恒等式规则源。

    rules 是规则行字符串（loader DSL）。图书馆保持纯数据：解析由
    内核消费方（cas/rules 装配规则集时）负责，本模块不导入内核。

    deriv 是导数模板：含 DB(0) 占位的驻留项，语义为
    f'(u) = 模板[DB(0) := u]；链式法则的 D(u) 因子由微分层乘上。
    分支破裂者（如 |x| 的符号导数）不收，置 None 并写入 deriv_note。
    """
    name: str                        # 头名，如 "Sin"
    print_name: str
    arity: int | None                # None = 变元
    real_on_real: bool | None = None # 实输入实值（定义域限制者置 None）
    # 值域粗界 (lo, hi)，端点可为 None（该侧无界）；lo ≤ f(u) ≤ hi 可达。
    # 例：Sin/Cos=(-1,1)；Abs=(0, None)（仅下界，上无界）。
    bound: tuple[Fr | None, Fr | None] | None = None
    # 零点结构引理：f(u)=0 ⟺ u=0（范数/绝对值类）。判定层据此做符号推理。
    zero_iff_arg_zero: bool = False
    rule_lines: tuple[str, ...] = ()
    deriv: object = None             # 导数模板（Term，DB(0) 占位）
    deriv_note: str = ""
    note: str = ""


_CONSTS: dict[str, ConstantDecl] = {}       # 内部名 -> 条目
_CONSTS_BY_ATOM: dict[int, ConstantDecl] = {}   # id(atom) -> 条目
_FUNCS: dict[str, FunctionDecl] = {}
_DOMAIN_CONDS: dict[str, object] = {}   # name -> callable(Expr) -> [Term]


# ---------------------------------------------------------------------------
# 注册 API
# ---------------------------------------------------------------------------

def constant(*, name: str, print_name: str, real=None, positive=None,
             bounds=None) -> ConstantDecl:
    d = ConstantDecl(atom=_mk_const(name), name=name,
                     print_name=print_name, real=real,
                     positive=positive, bounds=bounds)
    if name in _CONSTS:
        raise ValueError(f"constant redeclared: {name}")
    _CONSTS[name] = d
    _CONSTS_BY_ATOM[id(d.atom)] = d
    return d


def function(*, name: str, print_name: str, arity: int | None,
             real_on_real=None, bound=None, zero_iff_arg_zero=False,
             rule_lines=(), deriv=None, deriv_note="", note=""):
    d = FunctionDecl(name=name, print_name=print_name, arity=arity,
                     real_on_real=real_on_real, bound=bound,
                     zero_iff_arg_zero=zero_iff_arg_zero,
                     rule_lines=tuple(rule_lines),
                     deriv=deriv, deriv_note=deriv_note, note=note)
    if name in _FUNCS:
        raise ValueError(f"function redeclared: {name}")
    _FUNCS[name] = d
    return d


# ---------------------------------------------------------------------------
# 内核消费入口（零语义回退：查无此名时返回 None，调用方自行降级）
# ---------------------------------------------------------------------------

def const_by_atom(atom: Const) -> ConstantDecl | None:
    return _CONSTS_BY_ATOM.get(id(atom))


def const_by_name(name: str) -> ConstantDecl | None:
    """按内部名查常数声明。

    解析器的常数字面量表由此查询，不在内核里另存一份名字→原子的
    硬编码表（AGENTS.md 二：图书馆是唯一语义居所）。
    """
    return _CONSTS.get(name)


def is_const_name(name: str) -> bool:
    return name in _CONSTS


def lookup_function(name: str) -> FunctionDecl | None:
    return _FUNCS.get(name)


def print_name(head_name: str) -> str | None:
    """展示名查询：常数与函数两个表都查。

    常数按内部名（"pi"/"gamma"），函数按头名（"Sin"/"Cos"）——两个
    命名空间不重叠，先常数后函数。常数此前无出口，印名被迫在内核
    （cas/pprint）另存一份硬编码表，此处补齐。
    """
    c = _CONSTS.get(head_name)
    if c is not None:
        return c.print_name
    d = _FUNCS.get(head_name)
    return d.print_name if d else None


def const_positive(atom) -> bool | None:
    d = const_by_atom(atom)
    return d.positive if d else None


def const_real(atom) -> bool | None:
    d = const_by_atom(atom)
    return d.real if d else None


def const_bounds(atom):
    d = const_by_atom(atom)
    return d.bounds if d else None


def register_domain_cond(name: str, fn):
    """注册函数定义域条件生成器：fn(Expr) -> [约束Term]。"""
    _DOMAIN_CONDS[name] = fn


def lookup_domain_cond(name: str):
    return _DOMAIN_CONDS.get(name)


def all_functions() -> tuple:
    """全部函数声明（按注册序）。规则引擎装配与清单展示用。"""
    return tuple(_FUNCS.values())


def function_deriv(name: str):
    """导数模板查询：返回 (模板 | None, 说明)。查无此名返回 (None, "")。"""
    d = _FUNCS.get(name)
    if d is None:
        return None, ""
    return d.deriv, d.deriv_note


# ---------------------------------------------------------------------------
# 装载
# ---------------------------------------------------------------------------

_LOADED = False


def load_all():
    """装载全部图书馆模块（幂等）。新增定义文件在此登记。"""
    global _LOADED
    if _LOADED:
        return
    from library import constants, elementary   # noqa: F401
    _LOADED = True
