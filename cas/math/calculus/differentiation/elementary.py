"""Candidate generation for the declared elementary fragment.

The fragment contains exact literals, the target variable, declared elementary
constants, declared unary functions, sums, products and nonnegative integer
powers. The search chooses which local rule applies and builds a `Derivation`
tree; the rule instances themselves live in `derivation.py`, so the checker
verifies the same contract instead of re-running a second search.

A function's derivative law is used only when the library marks it as a trusted
basis. Conditional laws and function domains contribute to an explicit region
on which the derivative relation is stated. A source with an empty
differentiability region is still refused.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass

from cas.foundation.ids import SymbolId
from cas.language.decisions import Reason
from cas.language.signatures import LanguageSignature, StructuralHead
from cas.math.calculus.differentiation import derivation as D
from cas.math.calculus.differentiation.certificate import (
    Derivation,
    Rule,
)
from cas.math.elementary.declarations import ElementaryLibrary
from cas.semantics.services import (
    DerivationOutcome,
    DerivationUnsupported,
    Derived,
)
from cas.syntax import term as T


@dataclass(frozen=True, slots=True)
class ElementaryDifferentiator:
    """Differentiate one term in the declared elementary fragment."""

    library: ElementaryLibrary
    signature: LanguageSignature
    variable: SymbolId
    name_of: Callable[[SymbolId], str]

    def derive(self, term: T.Term) -> DerivationOutcome:
        return self._derive(term)

    def supports(self, term: T.Term) -> DerivationUnsupported | None:
        """Whether `term` is in the declared elementary fragment.

        This is the structural input schema of the differentiator.  It mirrors
        the rule dispatch in `_derive` without generating a candidate, so the
        problem builder can refuse an out-of-fragment source before a task is
        fixed.
        """
        if isinstance(term, (T.IntLit, T.RatLit)):
            return None
        if isinstance(term, T.SymbolRef):
            if term.symbol_id == self.variable:
                return None
            if self.library.is_constant(term.symbol_id):
                return None
            return DerivationUnsupported(
                Reason.FRAGMENT,
                "no dependency contract for "
                f"{self._name(term.symbol_id)}",
            )
        if not isinstance(term, T.Apply):
            return DerivationUnsupported(
                Reason.FRAGMENT,
                "the source is outside the elementary fragment",
            )
        if not isinstance(term.operator, T.SymbolRef):
            return DerivationUnsupported(
                Reason.FRAGMENT,
                "an applied expression must have a symbol operator",
            )
        head = self.signature.head_of(term.operator.symbol_id)
        if head in (StructuralHead.PLUS, StructuralHead.TIMES):
            for argument in term.arguments:
                issue = self.supports(argument)
                if issue is not None:
                    return issue
            return None
        if head is StructuralHead.POWER:
            if len(term.arguments) != 2:
                return DerivationUnsupported(
                    Reason.FRAGMENT, "Power takes a base and an exponent"
                )
            base, exponent = term.arguments
            if not isinstance(exponent, T.IntLit) or exponent.value < 0:
                return DerivationUnsupported(
                    Reason.FRAGMENT,
                    "only nonnegative integer powers are differentiated",
                )
            return self.supports(base)
        if head is not None:
            return DerivationUnsupported(
                Reason.FRAGMENT,
                f"{head.value} is not a scalar operation in this fragment",
            )
        function = self.library.function_for(term.operator.symbol_id)
        if function is None or function.law is None:
            return DerivationUnsupported(
                Reason.FRAGMENT,
                "no derivative law for "
                f"{self._name(term.operator.symbol_id)}",
            )
        for argument in term.arguments:
            issue = self.supports(argument)
            if issue is not None:
                return issue
        return None

    def _name(self, symbol_id: SymbolId) -> str:
        try:
            return self.name_of(symbol_id)
        except KeyError:
            return f"#{int(symbol_id)}"

    def _context(self) -> D.RuleContext:
        return D.RuleContext(self.library, self.signature, self.variable)

    def _derive(self, term: T.Term) -> DerivationOutcome:
        if isinstance(term, (T.IntLit, T.RatLit)):
            return self._node(Rule.LITERAL, term, ())
        if isinstance(term, T.SymbolRef):
            if term.symbol_id == self.variable:
                return self._node(Rule.VARIABLE, term, ())
            if self.library.is_constant(term.symbol_id):
                return self._node(Rule.CONSTANT, term, ())
            return DerivationUnsupported(
                Reason.FRAGMENT,
                "no dependency contract for "
                f"{self._name(term.symbol_id)}",
            )
        if not isinstance(term, T.Apply):
            return DerivationUnsupported(
                Reason.FRAGMENT,
                "the source is outside the elementary fragment",
            )
        if not isinstance(term.operator, T.SymbolRef):
            return DerivationUnsupported(
                Reason.FRAGMENT,
                "an applied expression must have a symbol operator",
            )
        head = self.signature.head_of(term.operator.symbol_id)
        if head is StructuralHead.PLUS:
            return self._composite(Rule.SUM, term)
        if head is StructuralHead.TIMES:
            return self._composite(Rule.PRODUCT, term)
        if head is StructuralHead.POWER:
            return self._composite(Rule.POWER, term)
        if head is not None:
            return DerivationUnsupported(
                Reason.FRAGMENT,
                f"{head.value} is not a scalar operation in this fragment",
            )
        return self._composite(Rule.FUNCTION, term)

    def _composite(
        self,
        rule: Rule,
        source: T.Term,
    ) -> DerivationOutcome:
        assert isinstance(source, T.Apply)
        children_sources: tuple[T.Term, ...]
        if rule is Rule.POWER:
            if len(source.arguments) != 2:
                return DerivationUnsupported(
                    Reason.FRAGMENT, "Power takes a base and an exponent"
                )
            children_sources = (source.arguments[0],)
        else:
            children_sources = source.arguments
        children: list[Derivation] = []
        for child_source in children_sources:
            outcome = self._derive(child_source)
            if not isinstance(outcome, Derived):
                return outcome
            if not isinstance(outcome.evidence, Derivation):
                return DerivationUnsupported(
                    Reason.FRAGMENT,
                    "the candidate has no rule-instance certificate",
                )
            children.append(outcome.evidence)
        return self._node(rule, source, tuple(children))

    def _node(
        self,
        rule: Rule,
        source: T.Term,
        children: tuple[Derivation, ...],
    ) -> DerivationOutcome:
        try:
            node = D.node_for(rule, source, children, self._context())
        except D.DerivationError as error:
            return DerivationUnsupported(error.reason, error.detail)
        return Derived(
            node.result,
            node.condition,
            node.defined,
            node,
        )


__all__ = ["ElementaryDifferentiator"]
