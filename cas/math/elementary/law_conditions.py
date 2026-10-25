"""Definedness and differentiability conditions for elementary applications.

The function's declared domain is a definedness condition; its derivative law
may impose a stricter differentiability condition. Both are instantiated with
the actual argument and combined with the argument's own conditions. The helpers
here only compose conditions; derivative recursion stays in the differentiator
and the rule-instance verifier in `derivation.py`.

A conditional law is trusted for the body's nonzero requirements (for example a
negative power); declared function domains used by the body are collected by
`law_body_domain`. The admitted basis remains responsible for the nonzero
promise.
"""

from __future__ import annotations

from cas.language.declarations import (
    DOMAIN_ARGUMENT,
    Call,
    LawExpr,
    Name,
    Num,
    law_children,
)
from cas.language.signatures import LanguageSignature
from cas.math.elementary.declarations import (
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
    parts: list[T.Term] = [
        application_defined(
            library,
            function,
            argument,
            inner_defined,
            signature,
        )
    ]
    if inner_condition is not None:
        parts.append(inner_condition)
    law = function.law
    if law is not None and law.condition is not None:
        parts.append(
            library.instantiate(
                law.condition, law.argument, argument, signature
            )
        )
    return and_all(signature, *parts)


def law_body_domain(
    library: ElementaryLibrary,
    expression: LawExpr,
    argument_name: str,
    argument: T.Term,
    signature: LanguageSignature,
) -> T.Term:
    """Declared function domains required by a law body.

    The law condition is trusted for the body's own nonzero requirements (for
    example `sqrt(u)^-1` on `u > 0`); this helper only collects the domains of
    functions the body calls, so a body such as `G(u)` cannot silently use a
    point outside G's declared domain.
    """
    return and_all(
        signature,
        *_body_domain_parts(
            library, expression, argument_name, argument, signature
        ),
    )


def _body_domain_parts(
    library: ElementaryLibrary,
    expression: LawExpr,
    argument_name: str,
    argument: T.Term,
    signature: LanguageSignature,
) -> list[T.Term]:
    if isinstance(expression, (Num, Name)):
        return []
    parts: list[T.Term] = []
    if isinstance(expression, Call):
        function = library.functions.get(expression.name)
        if (
            function is not None
            and function.domain is not None
            and len(expression.arguments) == 1
        ):
            argument_term = library.instantiate(
                expression.arguments[0],
                argument_name,
                argument,
                signature,
            )
            parts.append(
                library.instantiate(
                    function.domain,
                    DOMAIN_ARGUMENT,
                    argument_term,
                    signature,
                )
            )
    for child in law_children(expression):
        parts.extend(
            _body_domain_parts(
                library, child, argument_name, argument, signature
            )
        )
    return parts


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
