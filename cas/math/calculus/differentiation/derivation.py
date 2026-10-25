"""Local rule instances for the declared elementary fragment.

`node_for` is the single implementation of each local derivative rule. The
candidate generator chooses which rule and children apply; the checker rebuilds
every node from its children and rejects any certificate node that does not
match. Neither side re-runs the other's recursive search, and the rule itself
has one definition.
"""

from __future__ import annotations

from dataclasses import dataclass

from cas.foundation.ids import SymbolId
from cas.language.decisions import Reason
from cas.language.declarations import DeclarationOrigin
from cas.language.signatures import LanguageSignature, StructuralHead
from cas.math.calculus.differentiation import terms as B
from cas.math.calculus.differentiation.certificate import Derivation, Rule
from cas.math.elementary.declarations import ElementaryLibrary
from cas.math.elementary.law_conditions import (
    application_condition,
    application_defined,
    law_body_domain,
)
from cas.semantics.conditions import and_all
from cas.syntax import term as T


class DerivationError(Exception):
    """A rule instance cannot be formed or has an empty domain."""

    def __init__(self, reason: Reason, detail: str) -> None:
        super().__init__(detail)
        self.reason = reason
        self.detail = detail


@dataclass(frozen=True, slots=True)
class RuleContext:
    """The declared library, language and target variable of one fragment."""

    library: ElementaryLibrary
    signature: LanguageSignature
    variable: SymbolId


def node_for(
    rule: Rule,
    source: T.Term,
    children: tuple[Derivation, ...],
    context: RuleContext,
) -> Derivation:
    """Build the unique instance of `rule` for `source` and its children."""
    if rule is Rule.LITERAL:
        if not isinstance(source, (T.IntLit, T.RatLit)) or children:
            raise DerivationError(
                Reason.FRAGMENT,
                "a literal rule needs a literal and no children",
            )
        return _node(rule, source, T.number(0), None, None, children)

    if rule is Rule.VARIABLE:
        if (
            not isinstance(source, T.SymbolRef)
            or source.symbol_id != context.variable
            or children
        ):
            raise DerivationError(
                Reason.FRAGMENT,
                "a variable rule needs the target variable",
            )
        return _node(rule, source, T.number(1), None, None, children)

    if rule is Rule.CONSTANT:
        if (
            not isinstance(source, T.SymbolRef)
            or source.symbol_id == context.variable
            or not context.library.is_constant(source.symbol_id)
            or children
        ):
            raise DerivationError(
                Reason.FRAGMENT,
                "a constant rule needs a declared constant other than "
                "the target",
            )
        return _node(rule, source, T.number(0), None, None, children)

    if rule in (Rule.SUM, Rule.PRODUCT):
        head = StructuralHead.PLUS if rule is Rule.SUM else StructuralHead.TIMES
        arguments = _application_arguments(source, head, context.signature)
        if arguments is None:
            raise DerivationError(
                Reason.FRAGMENT,
                f"a {rule.value} rule needs the matching source application",
            )
        if rule is Rule.PRODUCT and not arguments:
            raise DerivationError(
                Reason.FRAGMENT, "an empty product has no derivative rule"
            )
        _require_children(children, arguments)
        if rule is Rule.SUM:
            result = B.plus(
                context.signature, *(child.result for child in children)
            )
        else:
            terms: list[T.Term] = []
            for position, child in enumerate(children):
                if child.result == T.number(0):
                    continue
                factors = (
                    arguments[:position]
                    + (child.result,)
                    + arguments[position + 1 :]
                )
                terms.append(B.times(context.signature, *factors))
            result = B.plus(context.signature, *terms)
        return _node(
            rule,
            source,
            result,
            and_all(
                context.signature,
                *(child.condition for child in children),
            ),
            and_all(
                context.signature,
                *(child.defined for child in children),
            ),
            children,
        )

    if rule is Rule.POWER:
        arguments = _application_arguments(
            source, StructuralHead.POWER, context.signature
        )
        if arguments is None or len(arguments) != 2:
            raise DerivationError(
                Reason.FRAGMENT,
                "a power rule needs a base and an exponent",
            )
        base, exponent = arguments
        if not isinstance(exponent, T.IntLit) or exponent.value < 0:
            raise DerivationError(
                Reason.FRAGMENT,
                "only nonnegative integer powers are differentiated",
            )
        _require_children(children, (base,), count=1)
        inner = children[0]
        if exponent.value == 0:
            nonzero = B.ne_zero(context.signature, base)
            defined = and_all(context.signature, inner.defined, nonzero)
            return _node(
                rule, source, T.number(0), defined, defined, children
            )
        condition = and_all(
            context.signature, inner.condition, inner.defined
        )
        if inner.result == T.number(0):
            return _node(
                rule,
                source,
                T.number(0),
                condition,
                inner.defined,
                children,
            )
        if exponent.value == 1:
            return _node(
                rule,
                source,
                inner.result,
                condition,
                inner.defined,
                children,
            )
        return _node(
            rule,
            source,
            B.times(
                context.signature,
                T.number(exponent.value),
                B.power(context.signature, base, exponent.value - 1),
                inner.result,
            ),
            condition,
            inner.defined,
            children,
        )

    if rule is Rule.FUNCTION:
        if (
            not isinstance(source, T.Apply)
            or not isinstance(source.operator, T.SymbolRef)
        ):
            raise DerivationError(
                Reason.FRAGMENT,
                "a function rule needs a declared function application",
            )
        function = context.library.function_for(source.operator.symbol_id)
        if function is None:
            raise DerivationError(
                Reason.FRAGMENT,
                "the operator is not a declared elementary function",
            )
        if len(function.arguments) != 1 or len(source.arguments) != 1:
            raise DerivationError(
                Reason.FRAGMENT,
                "the elementary fragment declares unary functions only",
            )
        law = function.law
        if law is None:
            raise DerivationError(
                Reason.FRAGMENT,
                f"no derivative law is declared for {function.name}",
            )
        if law.origin is not DeclarationOrigin.BASIS:
            raise DerivationError(
                Reason.FRAGMENT,
                f"the derivative law for {function.name} is a user axiom, "
                "not an admitted basis",
            )
        if law.condition is None:
            problem = context.library.body_partiality(law.body)
            if problem is not None:
                raise DerivationError(
                    Reason.GUARDED,
                    f"the derivative law for {function.name} is not total: "
                    f"{problem}",
                )
        argument = source.arguments[0]
        _require_children(children, (argument,), count=1)
        inner = children[0]
        defined = application_defined(
            context.library,
            function,
            argument,
            inner.defined,
            context.signature,
        )
        if inner.result == T.number(0):
            return _node(
                rule,
                source,
                T.number(0),
                and_all(
                    context.signature, inner.condition, defined
                ),
                defined,
                children,
            )
        body_domain = law_body_domain(
            context.library,
            law.body,
            law.argument,
            argument,
            context.signature,
        )
        body = context.library.instantiate(
            law.body, law.argument, argument, context.signature
        )
        condition = and_all(
            context.signature,
            application_condition(
                context.library,
                function,
                argument,
                inner.condition,
                inner.defined,
                context.signature,
            ),
            body_domain,
        )
        defined = and_all(
            context.signature,
            defined,
            body_domain,
        )
        return _node(
            rule,
            source,
            B.times(context.signature, body, inner.result),
            condition,
            defined,
            children,
        )

    raise DerivationError(
        Reason.FRAGMENT, f"unknown derivative rule: {rule!r}"
    )


def verify_derivation(
    node: Derivation,
    context: RuleContext,
) -> str | None:
    """Rebuild every node and return the first inconsistency, if any."""
    for index, child in enumerate(node.children):
        problem = verify_derivation(child, context)
        if problem is not None:
            return f"child {index}: {problem}"
    try:
        expected = node_for(
            node.rule, node.source, node.children, context
        )
    except DerivationError as error:
        return error.detail
    if expected != node:
        return (
            f"the {node.rule.value} instance is inconsistent with its "
            "source, children or claimed result"
        )
    return None


def _application_arguments(
    source: T.Term,
    head: StructuralHead,
    signature: LanguageSignature,
) -> tuple[T.Term, ...] | None:
    if not isinstance(source, T.Apply) or not isinstance(
        source.operator, T.SymbolRef
    ):
        return None
    if signature.head_of(source.operator.symbol_id) is not head:
        return None
    return source.arguments


def _require_children(
    children: tuple[Derivation, ...],
    sources: tuple[T.Term, ...],
    *,
    count: int | None = None,
) -> None:
    if count is not None and len(children) != count:
        raise DerivationError(
            Reason.FRAGMENT,
            f"the rule needs exactly {count} child instance(s)",
        )
    if len(children) != len(sources):
        raise DerivationError(
            Reason.FRAGMENT,
            "the rule instance has the wrong number of children",
        )
    for child, source in zip(children, sources):
        if child.source != source:
            raise DerivationError(
                Reason.FRAGMENT,
                "a child instance derives a different source",
            )


def _node(
    rule: Rule,
    source: T.Term,
    result: T.Term,
    condition: T.Term | None,
    defined: T.Term | None,
    children: tuple[Derivation, ...],
) -> Derivation:
    actual_condition = T.TRUE if condition is None else condition
    actual_defined = T.TRUE if defined is None else defined
    if actual_condition == T.FALSE:
        raise DerivationError(
            Reason.GUARDED, "the source has no differentiability region"
        )
    if actual_defined == T.FALSE:
        raise DerivationError(
            Reason.GUARDED, "the source is not defined anywhere"
        )
    return Derivation(
        rule,
        source,
        result,
        None if actual_condition == T.TRUE else actual_condition,
        None if actual_defined == T.TRUE else actual_defined,
        tuple(children),
    )


__all__ = [
    "DerivationError",
    "RuleContext",
    "node_for",
    "verify_derivation",
]
