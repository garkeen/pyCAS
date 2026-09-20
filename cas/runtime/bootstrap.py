# -*- coding: utf-8 -*-
"""Explicit assembly.

`bootstrap()` is the **only** entry that installs math semantics into the runtime:
it calls each math module's `install(builder)` in dependency order, builds the
projection ladder, and hands the result to the `MathContext` that every algorithm
receives as an explicit parameter.

This replaces the former import-time mutation of global state, and equally the
former assembly-time mutation of module-level handles (a declaration handle, a
stage list, a default coefficient ring): importing any `cas.math.*` still produces
no registration side effect, and assembly now produces no hidden writes either --
what assembly computes is returned, not stashed. Without assembly the semantics
are simply unavailable, and an algorithm cannot even be called without a context.

Assembly order is dependency order: elementary declares the constants first (the
domain layer needs the identity of `i`), domains then build the base fields, base
registers the decision stages last.

The returned runtime is not installed anywhere as a side effect; the application
entry point installs it explicitly (`cas.runtime.dispatch.install`).
"""

from cas.math.context import MathContext
from cas.runtime.registry import RuntimeBuilder
from cas.runtime.runtime import Runtime


def bootstrap() -> Runtime:
    """Assemble every math module and return the read-only runtime.

    Idempotence is the caller's job: assembling twice builds two independent
    runtimes, which is what the tests want when they re-assemble.
    """
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

    # The projection ladder is computed here, after every declaration is in: it
    # needs the resident domains (to pick the coefficient ring by capability) and
    # it produces the rungs the algorithms project along.
    from cas.math import project
    ladder = project.build_ladder(tuple(builder.domains))

    math = MathContext(
        consts=builder.constants,
        funcs=builder.functions,
        roles=builder.roles,
        rule_lines=tuple(builder.rule_lines),
        eq_stages=tuple(builder.eq_stages),
        projection_stages=ladder.stages,
        coeff_ring=ladder.coeff_ring,
    )
    return Runtime(builder, math)
