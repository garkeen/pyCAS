# -*- coding: utf-8 -*-
"""Explicit assembly.

`bootstrap()` is the **only** entry that installs math semantics into the runtime:
it calls each math module's `install(builder)` in dependency order, then binds the
assembly result to the consumers that need precomputed state (the projection base
field ladder, the identity-decision stages).

This replaces the former import-time mutation of global state: declarations used to
register themselves on import, base fields entered the ladder on import, and the
decision stage appended itself on import. Importing any `cas.math.*` now produces no
registration side effect; without assembly the semantics are simply unavailable
(an unknown name resolves to None), and assembly must be started explicitly by the
application.

Assembly order is dependency order: elementary declares the constants first (the
domain layer needs the identity of `i`), domains then build the base fields, and
base installs the decision stages last.
"""

from cas.runtime.registry import RuntimeBuilder
from cas.runtime.runtime import Runtime


def bootstrap() -> Runtime:
    """Assemble every math module and return the read-only runtime. Idempotence is
    the caller's job (dispatch caches the result)."""
    builder = RuntimeBuilder()

    # order is dependency: constant declarations -> base fields (i identity) -> decision stages
    from cas.math.elementary import module as elementary
    elementary.install(builder)

    from cas.math.domains import module as domains
    domains.install(builder)

    from cas.math.base import module as base
    base.install(builder)

    from cas.math.calculus import module as calculus
    calculus.install(builder)

    from cas.math.solving import module as solving
    solving.install(builder)

    rt = Runtime(builder)

    # hand the assembly result to consumers that need precomputed state explicitly
    from cas.math import project
    project.bind_domains(rt.domains)

    from cas.math import decide
    decide.bind_eq_stages(rt.eq_stages)

    # inject the declaration query surface into math modules (math never imports runtime)
    from cas.math import diff, domcond, rules
    for m in (decide, diff, domcond, rules):
        m.bind_runtime(rt)

    return rt
