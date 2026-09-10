# -*- coding: utf-8 -*-
"""`Runtime`：装配完成的只读查询面。

它是旧 `library` 查询 API 的正式归属（v4 §三 的 `runtime/dispatch.py` 底座）：
常数/函数的印名、正性、粗界、导数模板、定义域条件、函数清单——一切数学语义
的**只读**出口。写入口只有 `RuntimeBuilder`（装配期），运行期没有写入路径。

消费者（parser / pprint / decide / project / rules / domcond / diff …）查无此名
时一律得到 `None`，由调用方自行降级——**零语义回退**，本层不猜。
"""

from cas.syntax.term import Const


class Runtime:
    """只读快照。构造后不再变化（构造只发生在 bootstrap）。"""

    def __init__(self, builder):
        self._consts = dict(builder.constants)
        self._funcs = dict(builder.functions)
        self._domain_conds = dict(builder.domain_conds)
        self._eq_stages = tuple(builder.eq_stages)
        self._domains = tuple(builder.domains)
        self._by_atom = {id(d.atom): d for d in self._consts.values()}

    # --- 常数 ---

    def const_by_atom(self, atom: Const):
        return self._by_atom.get(id(atom))

    def const_by_name(self, name: str):
        return self._consts.get(name)

    def is_const_name(self, name: str) -> bool:
        return name in self._consts

    def const_positive(self, atom):
        d = self.const_by_atom(atom)
        return d.positive if d else None

    def const_real(self, atom):
        d = self.const_by_atom(atom)
        return d.real if d else None

    def const_bounds(self, atom):
        d = self.const_by_atom(atom)
        return d.bounds if d else None

    # --- 函数 ---

    def lookup_function(self, name: str):
        return self._funcs.get(name)

    def function_deriv(self, name: str):
        d = self._funcs.get(name)
        return (None, "") if d is None else (d.deriv, d.deriv_note)

    def all_functions(self) -> tuple:
        return tuple(self._funcs.values())

    def print_name(self, head_name: str):
        """展示名：常数按内部名、函数按头名（两个命名空间不重叠）。"""
        c = self._consts.get(head_name)
        if c is not None:
            return c.print_name
        d = self._funcs.get(head_name)
        return d.print_name if d else None

    # --- 定义域条件 / 判定阶段 / 域 ---

    def lookup_domain_cond(self, name: str):
        return self._domain_conds.get(name)

    @property
    def eq_stages(self) -> tuple:
        return self._eq_stages

    @property
    def domains(self) -> tuple:
        return self._domains

    def stats(self):
        return {"constants": len(self._consts), "functions": len(self._funcs),
                "domain_conds": len(self._domain_conds),
                "eq_stages": len(self._eq_stages),
                "domains": len(self._domains)}


# ---------------------------------------------------------------------------
# 会话装配：checker 与判定服务都由本层注入（workflow 不依赖 cas.math）
# ---------------------------------------------------------------------------

def register_math_checkers(store) -> None:
    """把各数学模块的 checker 注册进账本（v4 §7.2 的 `math/*/checkers.py`）。"""
    from cas.math.base import checkers as base_c
    from cas.math.calculus.differentiation import checkers as diff_c
    from cas.math.calculus.integration import checkers as int_c
    from cas.math.solving.equations import checkers as eq_c
    for m in (base_c, diff_c, int_c, eq_c):
        m.register(store)


def new_workflow(**kw):
    """建一个工作流会话：账本 + 内核自带 checker + 数学 checker + 判定服务。

    workflow 不 import `cas.math`（v4 §四），所以 checker 与判定服务**必须由本层
    注入**——这也让「workflow 不知道自己有哪些 checker」成为结构事实，而不是约定。
    """
    from cas.kernel.services import register_core_checkers
    from cas.kernel.store import KernelStore
    from cas.runtime.algorithms import Algorithms
    from cas.runtime.services import ScopeServices
    from cas.workflow.workflow import Workflow

    store = kw.pop("store", None)
    if store is None:
        store = KernelStore()
    register_core_checkers(store)
    register_math_checkers(store)
    return Workflow(store=store, services=ScopeServices(store.scopes),
                    algorithms=Algorithms(), **kw)
