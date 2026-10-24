"""Candidate generation for the declared elementary fragment.

The fragment contains exact literals, the target variable, declared elementary
constants, declared unary functions, sums, products and nonnegative integer
powers. A function's derivative law is used only when the library marks it as a
trusted basis and it has no open condition. Anything else is refused instead of
being differentiated by an implicit assumption.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass

from cas.foundation.ids import SymbolId
from cas.language.decisions import Reason
from cas.language.signatures import LanguageSignature, StructuralHead
from cas.math.calculus.differentiation import terms as B
from cas.math.elementary.declarations import (
    ElementaryLibrary,
    FunctionSymbol,
    LawOrigin,
)
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

    def _name(self, symbol_id: SymbolId) -> str:
        try:
            return self.name_of(symbol_id)
        except KeyError:
            return f"#{int(symbol_id)}"

    def _derive(self, term: T.Term) -> DerivationOutcome:
        if isinstance(term, (T.IntLit, T.RatLit)):
            return Derived(T.number(0))
        if isinstance(term, T.SymbolRef):
            if term.symbol_id == self.variable:
                return Derived(T.number(1))
            if self.library.is_constant(term.symbol_id):
                return Derived(T.number(0))
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
            return self._sum(term.arguments)
        if head is StructuralHead.TIMES:
            return self._product(term.arguments)
        if head is StructuralHead.POWER:
            return self._power(term.arguments)
        if head is not None:
            return DerivationUnsupported(
                Reason.FRAGMENT,
                f"{head.value} is not a scalar operation in this fragment",
            )
        function = self.library.function_for(term.operator.symbol_id)
        if function is None:
            return DerivationUnsupported(
                Reason.FRAGMENT,
                "the operator is not a declared elementary function",
            )
        return self._function(term, function)

    def _sum(self, arguments: tuple[T.Term, ...]) -> DerivationOutcome:
        derivatives: list[T.Term] = []
        for argument in arguments:
            outcome = self._derive(argument)
            if not isinstance(outcome, Derived):
                return outcome
            derivatives.append(outcome.term)
        return Derived(B.plus(self.signature, *derivatives))

    def _product(self, arguments: tuple[T.Term, ...]) -> DerivationOutcome:
        if not arguments:
            return DerivationUnsupported(
                Reason.FRAGMENT, "an empty product has no derivative rule"
            )
        terms: list[T.Term] = []
        for position, argument in enumerate(arguments):
            outcome = self._derive(argument)
            if not isinstance(outcome, Derived):
                return outcome
            factors = (
                arguments[:position]
                + (outcome.term,)
                + arguments[position + 1 :]
            )
            terms.append(B.times(self.signature, *factors))
        return Derived(B.plus(self.signature, *terms))

    def _power(self, arguments: tuple[T.Term, ...]) -> DerivationOutcome:
        if len(arguments) != 2:
            return DerivationUnsupported(
                Reason.FRAGMENT, "Power takes a base and an exponent"
            )
        base, exponent = arguments
        if not isinstance(exponent, T.IntLit) or exponent.value < 0:
            return DerivationUnsupported(
                Reason.FRAGMENT,
                "only nonnegative integer powers are differentiated",
            )
        outcome = self._derive(base)
        if not isinstance(outcome, Derived):
            return outcome
        if exponent.value == 0:
            return Derived(T.number(0))
        return Derived(
            B.times(
                self.signature,
                T.number(exponent.value),
                B.power(self.signature, base, exponent.value - 1),
                outcome.term,
            )
        )

    def _function(
        self,
        application: T.Apply,
        function: FunctionSymbol,
    ) -> DerivationOutcome:
        if len(function.arguments) != 1:
            return DerivationUnsupported(
                Reason.FRAGMENT,
                "the elementary fragment declares unary functions only",
            )
        if len(application.arguments) != 1:
            return DerivationUnsupported(
                Reason.FRAGMENT,
                f"{function.name} takes one argument",
            )
        law = function.law
        if law is None:
            return DerivationUnsupported(
                Reason.FRAGMENT,
                f"no derivative law is declared for {function.name}",
            )
        if law.origin is not LawOrigin.BASIS:
            return DerivationUnsupported(
                Reason.FRAGMENT,
                f"the derivative law for {function.name} is a user axiom, "
                "not an admitted basis",
            )
        if law.condition is not None or function.domain is not None:
            return DerivationUnsupported(
                Reason.GUARDED,
                f"the derivative law or domain for {function.name} is "
                "conditional; its condition has not been discharged",
            )
        problem = self.library.body_partiality(law.body)
        if problem is not None:
            return DerivationUnsupported(
                Reason.GUARDED,
                f"the derivative law for {function.name} is not total: "
                f"{problem}",
            )
        argument = application.arguments[0]
        outcome = self._derive(argument)
        if not isinstance(outcome, Derived):
            return outcome
        body = self.library.instantiate(
            law.body, law.argument, argument, self.signature
        )
        return Derived(
            B.times(self.signature, body, outcome.term)
        )


__all__ = ["ElementaryDifferentiator"]
