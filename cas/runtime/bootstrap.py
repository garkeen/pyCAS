"""Pure explicit assembly of the mathematical runtime."""

from __future__ import annotations

from cas.math.context import DeclarationCatalog, MathContext
from cas.math.domains.base import DomainCatalog
from cas.math.project import build_ladder
from cas.runtime.registry import RuntimeBuilder
from cas.runtime.runtime import Runtime


def bootstrap() -> Runtime:
    """Install every math module and return one immutable runtime snapshot."""

    builder = RuntimeBuilder()

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

    assembly = builder.freeze()
    domain_catalog = DomainCatalog(resident=assembly.domains)
    projection = build_ladder(domain_catalog)
    declarations = DeclarationCatalog.from_records(
        constants=assembly.constants,
        functions=assembly.functions,
        roles=assembly.roles,
        lift_policies=assembly.lifts,
    )
    math = MathContext(
        declarations=declarations,
        domains=domain_catalog,
        rule_catalog=assembly.rules,
        decision_stages=assembly.decision_stages,
        projection_ladder=projection,
    )
    return Runtime(assembly, math)
