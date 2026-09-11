# -*- coding: utf-8 -*-
"""Decision services: adapts `cas.math.decide` onto the kernel port.

`KernelServices` is a port **defined by the kernel**; its implementation must live
in a layer that can see both kernel and math -- runtime is that layer, since it is
the only layer allowed to import every math module. Neither the kernel nor the
workflow knows about `cas.math.decide`.

Scope assumptions act as the decision context, so condition discharge happens in
the **correct branch context**: assumptions made inside a branch scope reach the
decision, rather than being global assumptions.
"""


class ScopeServices:
    """`KernelServices` implementation that decides relative to a scope."""

    def __init__(self, scopes):
        self._scopes = scopes

    def decide(self, proposition, scope_id):
        from cas.kernel.scope import Assumptions
        from cas.math.decide import decide
        return decide(proposition, Assumptions.of(self._scopes, scope_id))
