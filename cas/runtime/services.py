# -*- coding: utf-8 -*-
"""判定服务：把 `cas.math.decide` 接到内核端口上（v4 §6.7）。

`KernelServices` 是**内核定义的端口**；它的实现必须住在能同时看见 kernel 与
math 的层——runtime 正是这样一层（v4 §四：runtime → 所有数学模块）。内核与
workflow 都不认识 `cas.math.decide`，这正是阶段6 达到的状态。

作用域假设作为判定上下文：条件清偿因此在**正确的分支上下文**里进行——
分支作用域里的假设会进入判定，而不是全局假设。
"""


class ScopeServices:
    """按作用域做判定的 `KernelServices` 实现。"""

    def __init__(self, scopes):
        self._scopes = scopes

    def decide(self, proposition, scope_id):
        from cas.kernel.scope import Assumptions
        from cas.math.decide import decide
        return decide(proposition, Assumptions.of(self._scopes, scope_id))
