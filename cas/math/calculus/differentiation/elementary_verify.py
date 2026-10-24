"""Independent verification of a declared elementary derivative.

This module is a second implementation of the same rule: it walks the source
term itself and constructs the expected derivative from the declared laws. It
does not import the candidate generator, so a defect in that search cannot
certify itself. A structural mismatch with the claimed candidate is reported as
"unverified", not refuted: structural difference alone does not decide
mathematical inequality.
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
class ElementaryVerifier:
    """Expected derivative for one term in the elementary fragment."""

    library: ElementaryLibrary
    signature: LanguageSignature
    variable: SymbolId
    name_of: Callable[[SymbolId], str]

    def verify(self, source: T.Term) -> DerivationOutcome:
        return self._walk(source)

    def _name(self, symbol_id: SymbolId) -> str:
        try:
            return self.name_of(symbol_id)
        except KeyError:
            return f"#{int(symbol_id)}"

    def _walk(self, current: T.Term) -> DerivationOutcome:
        if isinstance(current, T.IntLit) or isinstance(current, T.RatLit):
            return Derived(T.number(0))
        if isinstance(current, T.SymbolRef):
            return self._symbol(current)
        if not isinstance(current, T.Apply):
            return DerivationUnsupported(
                Reason.FRAGMENT,
                "the source is outside the elementary fragment",
            )
        if not isinstance(current.operator, T.SymbolRef):
            return DerivationUnsupported(
                Reason.FRAGMENT,
                "an applied expression must have a symbol operator",
            )
        head = self.signature.head_of(current.operator.symbol_id)
        if head is StructuralHead.PLUS:
            return self._sum(current.arguments)
        if head is StructuralHead.TIMES:
            return self._product(current.arguments)
        if head is StructuralHead.POWER:
            return self._power(current.arguments)
        if head is not None:
            return DerivationUnsupported(
                Reason.FRAGMENT,
                f"{head.value} is not a scalar operation in this fragment",
            )
        function = self.library.function_for(current.operator.symbol_id)
        if function is None:
            return DerivationUnsupported(
                Reason.FRAGMENT,
                "the operator is not a declared elementary function",
            )
        return self._chain(current, function)

    def _symbol(self, current: T.SymbolRef) -> DerivationOutcome:
        if current.symbol_id == self.variable:
            return Derived(T.number(1))
        if self.library.is_constant(current.symbol_id):
            return Derived(T.number(0))
        return DerivationUnsupported(
            Reason.FRAGMENT,
            f"no dependency contract for {self._name(current.symbol_id)}",
        )

    def _sum(self, arguments: tuple[T.Term, ...]) -> DerivationOutcome:
        values: list[T.Term] = []
        for argument in arguments:
            expected = self._walk(argument)
            if not isinstance(expected, Derived):
                return expected
            values.append(expected.term)
        return Derived(B.plus(self.signature, *values))

    def _product(self, arguments: tuple[T.Term, ...]) -> DerivationOutcome:
        if not arguments:
            return DerivationUnsupported(
                Reason.FRAGMENT, "an empty product has no derivative rule"
            )
        values: list[T.Term] = []
        for index in range(len(arguments)):
            expected = self._walk(arguments[index])
            if not isinstance(expected, Derived):
                return expected
            replaced = (
                arguments[:index]
                + (expected.term,)
                + arguments[index + 1 :]
            )
            values.append(B.times(self.signature, *replaced))
        return Derived(B.plus(self.signature, *values))

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
        if exponent.value < 0:
            return DerivationUnsupported(
                Reason.FRAGMENT,
                "only nonnegative integer powers are differentiated",
            )
        inner = self._walk(base)
        if not isinstance(inner, Derived):
            return inner
        if exponent.value == 0:
            return Derived(T.number(0))
        return Derived(
            B.times(
                self.signature,
                T.number(exponent.value),
                B.power(self.signature, base, exponent.value - 1),
                inner.term,
            )
        )

    def _chain(
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
        inner = self._walk(application.arguments[0])
        if not isinstance(inner, Derived):
            return inner
        outer = self.library.instantiate(
            law.body,
            law.argument,
            application.arguments[0],
            self.signature,
        )
        return Derived(B.times(self.signature, outer, inner.term))


def verify_elementary_derivative(
    source: T.Term,
    library: ElementaryLibrary,
    signature: LanguageSignature,
    variable: SymbolId,
    name_of: Callable[[SymbolId], str],
) -> DerivationOutcome:
    """The expected derivative, or a precise refusal."""
    return ElementaryVerifier(
        library, signature, variable, name_of
    ).verify(source)


__all__ = ["ElementaryVerifier", "verify_elementary_derivative"]
