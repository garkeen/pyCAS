"""Definedness and differentiability conditions for elementary applications.

The function's declared domain is a definedness condition; its derivative law
may impose a stricter differentiability condition. Both are instantiated with
the actual argument and combined with the argument's own conditions. The helpers
here only compose conditions; derivative recursion stays in the differentiator
and the independent verifier.
"""

from __future__ import annotations

from cas.language.signatures import LanguageSignature
from cas.math.elementary.declarations import (
    DOMAIN_ARGUMENT,
    ElementaryLibrary,
    FunctionSymbol,
)
from cas.semantics.conditions import and_all
from cas.syntax import term as T


def application_condition(
    library: ElementaryLibrary,
    function: FunctionSymbol,
    argument: T.Term,
    inner_condition: T.Term | None,
    inner_defined: T.Term | None,
    signature: LanguageSignature,
) -> T.Term:
    """Where the chain rule for `function(argument)` is justified."""
    parts: list[T.Term] = []
    if inner_condition is not None:
        parts.append(inner_condition)
    if inner_defined is not None:
        parts.append(inner_defined)
    if function.domain is not None:
        parts.append(
            library.instantiate(
                function.domain, DOMAIN_ARGUMENT, argument, signature
            )
        )
    law = function.law
    if law is not None and law.condition is not None:
        parts.append(
            library.instantiate(
                law.condition, law.argument, argument, signature
            )
        )
    return and_all(signature, *parts)


def application_defined(
    library: ElementaryLibrary,
    function: FunctionSymbol,
    argument: T.Term,
    inner_defined: T.Term | None,
    signature: LanguageSignature,
) -> T.Term:
    """Where `function(argument)` is defined, without requiring differentiability."""
    parts: list[T.Term] = []
    if inner_defined is not None:
        parts.append(inner_defined)
    if function.domain is not None:
        parts.append(
            library.instantiate(
                function.domain, DOMAIN_ARGUMENT, argument, signature
            )
        )
    return and_all(signature, *parts)


__all__ = ["application_condition", "application_defined"]
