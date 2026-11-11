"""Independent checker for `HasGroebnerBasis` over a fixed monomial order.

The checker never imports the Buchberger search module or the future operation
that will propose a basis.  It re-elaborates every generator, basis element and
cofactor through the multivariate bridge and recomputes the basis facts from the
candidate, the claim and the certificate.  It does not call
``ideal_membership``/``ideal_equal``: those read the sealed search-side record,
which is exactly the trust the checker must not inherit.

Verification order
------------------

1. The kernel-fixed algebra request, the single conclusion and the
   `HasGroebnerBasis` shape are admitted.
2. The candidate is the claimed basis set, the certificate is a cofactor matrix
   and the quoted order names this vocabulary's order.
3. The problem's generator set is compared with the claim (set reading), a
   restricted-region problem is refused, and the requested coverage/language are
   checked.
4. Every set member and cofactor term is independently admitted as a polynomial
   over the checker's ring.
5. The coefficient structure is a field.  Positive characteristic is allowed:
   Buchberger's criterion does not need ordered or characteristic-zero
   coefficients.
6. The candidate basis is reduced: nonzero, monic and interreduced.
7. Buchberger's criterion: every S-polynomial of the candidate basis has zero
   normal form.  This proves that the candidate is a Groebner basis of its own
   ideal.
8. Every original generator has zero normal form modulo the candidate basis.
   This is checked after the Buchberger criterion on purpose: a nonzero
   remainder only refutes ideal membership when the divisors are known to be a
   Groebner basis, because then the remainder is the unique ideal normal form.
   For an arbitrary divisor list it would only mean that this division order
   does not reduce the generator.
9. The cofactor rows reconstruct every basis element from the original
   generators.  Together with step 8 this proves that the two ideals are equal,
   so the candidate is the reduced Groebner basis of the original ideal under
   the fixed order.

A reduced/monic/interreduced failure, a nonzero S-polynomial or a generator with
a nonzero normal form is a mathematical refutation and carries the offending
claim term.  A malformed order quote, a candidate/certificate mismatch, a
cofactor-shape or cofactor-identity failure is `InvalidEvidence`: the certificate
does not support the claim, but that is not evidence that the claim is false.  A
typing/bridge refusal or a non-field coefficient structure is
`Unverified(FRAGMENT)`; pair-budget exhaustion is `Unverified(BUDGET)` and never
returns a partial verification.  This module publishes no judgment; it only
reports the closed `CheckOutcome`.
"""

from __future__ import annotations

from typing import Generic, TypeVar

from cas.algebra.multivariate import (
    leading_coefficient,
    leading_monomial,
    normal_form,
    s_polynomial,
)
from cas.algebra.polynomial import Exponents, Polynomial, PolynomialRing
from cas.algebra.protocols import Field
from cas.foundation.ids import FrameId
from cas.kernel.evidence import (
    CheckOutcome,
    CheckRequest,
    InvalidEvidence,
    Refuted,
    Unverified,
    Verified,
    context_algebra_mismatch,
    problem_mismatch,
)
from cas.language.decisions import Reason
from cas.language.problems import (
    Coverage,
    Exactness,
    ResultLanguage,
)
from cas.language.roles import CandidateRole
from cas.language.sets import set_members
from cas.language.signatures import LanguageSignature
from cas.math.algebra.groebner_specification import (
    GroebnerCertificate,
    GroebnerVocabulary,
    parse_groebner,
)
from cas.semantics.bridge import (
    AlgebraView,
    MultivariatePolynomialBridge,
    ViewRefused,
    typed_view,
)
from cas.semantics.frames import FrameStore
from cas.semantics.request import AlgebraRequest
from cas.syntax import term as T

E = TypeVar("E")

_REPRESENTATION_MISSING = frozenset(
    {"multivariate_polynomial_representation"}
)
_PAIR_BUDGET_MISSING = frozenset({"groebner_pair_budget"})
_FIELD_MISSING = frozenset({"coefficient_field"})
_ORDER_MISSING = frozenset({"monomial_order"})


class GroebnerChecker(Generic[E]):
    """An independent checker for one multivariate polynomial ring."""

    id = "algebra.groebner"
    version = "1"

    def __init__(
        self,
        ring: PolynomialRing[E],
        signature: LanguageSignature,
        vocabulary: GroebnerVocabulary,
        bridge: MultivariatePolynomialBridge[E],
        frames: FrameStore,
        request: AlgebraRequest,
        *,
        identifier: str = "algebra.groebner",
        pair_budget: int = 4096,
    ) -> None:
        if not identifier:
            raise ValueError("a checker needs an identifier")
        if ring is not bridge.ring:
            raise ValueError(
                "the checker ring is not the multivariate bridge's ring"
            )
        if request.roles.target is not None:
            raise ValueError(
                "a Groebner checker needs a generator-mode request"
            )
        if request.roles.variables != ring.generators:
            raise ValueError(
                "the request generator roles are not the ring's generators "
                "in ring order"
            )
        if request.parameter_ring is not None:
            raise ValueError(
                "a Groebner checker cannot take a parameter ring"
            )
        if vocabulary.order is not ring.monomial_order:
            raise ValueError(
                "the vocabulary order is not the ring's monomial order"
            )
        if isinstance(pair_budget, bool) or not isinstance(pair_budget, int):
            raise TypeError(
                "the Groebner pair budget must be an int (bool is not accepted)"
            )
        if pair_budget < 0:
            raise ValueError("the Groebner pair budget must be nonnegative")
        self.id = identifier
        self._ring = ring
        self._signature = signature
        self._vocabulary = vocabulary
        self._bridge = bridge
        self._frames = frames
        self._request = request
        self._pair_budget = pair_budget

    def _view(
        self, term: T.Term, frame: FrameId
    ) -> AlgebraView[Polynomial[E]] | Unverified:
        """Independently elaborate and admit one claimed polynomial term."""
        outcome = typed_view(
            self._bridge,
            term,
            self._frames,
            frame,
            self._signature,
            self._request,
        )
        if isinstance(outcome, ViewRefused):
            missing = outcome.missing
            if outcome.reason is Reason.FRAGMENT:
                missing = missing | _REPRESENTATION_MISSING
            return Unverified(
                reason=outcome.reason,
                detail=outcome.detail,
                missing=missing,
                conditions=outcome.conditions,
            )
        if not isinstance(outcome, AlgebraView):
            return Unverified(
                reason=Reason.FRAGMENT,
                detail=outcome.detail,
                missing=outcome.missing | _REPRESENTATION_MISSING,
            )
        return outcome

    def _values(
        self,
        terms: tuple[T.Term, ...],
        frame: FrameId,
        label: str,
    ) -> tuple[Polynomial[E], ...] | InvalidEvidence | Unverified:
        """Admit one ordered term tuple as polynomials."""
        values: list[Polynomial[E]] = []
        for term in terms:
            view = self._view(term, frame)
            if isinstance(view, Unverified):
                return view
            if view.source.term != term:
                return InvalidEvidence(
                    f"the elaborated {label} does not match the claim"
                )
            values.append(view.value)
        return tuple(values)

    def check(self, request: CheckRequest) -> CheckOutcome:
        algebra_mismatch = context_algebra_mismatch(
            request.context, self._request
        )
        if algebra_mismatch is not None:
            return InvalidEvidence(algebra_mismatch)
        if len(request.conclusions) != 1:
            return InvalidEvidence(
                "a Groebner-basis certificate names exactly one claim"
            )
        conclusion = request.conclusions[0]
        frame = conclusion.meaning.frame
        claim = parse_groebner(self._vocabulary, conclusion.term)
        if claim is None:
            return InvalidEvidence(
                "the conclusion is not a HasGroebnerBasis specification"
            )
        candidate = request.candidate
        if candidate is None:
            return InvalidEvidence("a Groebner-basis candidate is required")
        if request.candidate_role is not CandidateRole.SET:
            return InvalidEvidence(
                "a Groebner-basis candidate needs the set candidate role"
            )
        if candidate != claim.basis:
            return InvalidEvidence(
                "the candidate does not match the specification"
            )
        certificate = request.certificate
        if not isinstance(certificate, GroebnerCertificate):
            return InvalidEvidence(
                "a Groebner-basis certificate is required"
            )
        if not isinstance(claim.order, T.Quote) or not isinstance(
            claim.order.term, T.SymbolRef
        ):
            return InvalidEvidence(
                "the specification order is not a quoted order symbol"
            )
        if claim.order.term.symbol_id != self._vocabulary.order_symbol:
            return Unverified(
                Reason.FRAGMENT,
                "the specification names another monomial order",
                missing=_ORDER_MISSING,
            )
        generator_terms = set_members(
            claim.generators, self._signature
        )
        if generator_terms is None:
            return InvalidEvidence(
                "the first argument is not a finite-set term"
            )
        basis_terms = set_members(claim.basis, self._signature)
        if basis_terms is None:
            return InvalidEvidence(
                "the second argument is not a finite-set term"
            )
        mismatch = problem_mismatch(
            request,
            operations=("groebner_basis",),
            input_set=generator_terms,
            roles=self._request.roles,
            interpretation_requirement=(
                self._request.interpretation_requirement
            ),
            exactness=Exactness.EXACT,
            coefficient_domain=self._request.coefficient_domain,
            value_domain=self._request.value_domain,
        )
        if mismatch is not None:
            return InvalidEvidence(mismatch)
        problem = request.problem
        if problem is not None:
            if problem.region is not None:
                return InvalidEvidence(
                    "a Groebner basis problem has no restricted-region form"
                )
            if problem.coverage is not Coverage.COMPLETE_SET:
                return InvalidEvidence(
                    "a Groebner basis requires complete-set coverage"
                )
            if problem.result_language is not ResultLanguage.SET:
                return InvalidEvidence(
                    "a Groebner basis requires a set result language"
                )
        generator_values = self._values(
            generator_terms, frame, "generator"
        )
        if isinstance(generator_values, (InvalidEvidence, Unverified)):
            return generator_values
        basis_values = self._values(basis_terms, frame, "basis element")
        if isinstance(basis_values, (InvalidEvidence, Unverified)):
            return basis_values
        coefficients = self._ring.coefficients
        if not isinstance(coefficients, Field):
            return Unverified(
                Reason.FRAGMENT,
                "a Groebner basis needs a field of coefficients",
                missing=_FIELD_MISSING,
            )
        for term, value in zip(basis_terms, basis_values):
            if value.is_zero():
                return Refuted(
                    conclusion,
                    (term,),
                    "a reduced Groebner basis cannot contain the zero "
                    "polynomial",
                )
        for index, value in enumerate(basis_values):
            if not coefficients.is_one(
                leading_coefficient(self._ring, value)
            ):
                return Refuted(
                    conclusion,
                    (basis_terms[index],),
                    "a reduced Groebner basis element must be monic",
                )
            for exponents, _ in value.terms:
                for other_index, other in enumerate(basis_values):
                    if other_index == index:
                        continue
                    divisor = leading_monomial(self._ring, other)
                    if _divides(divisor, exponents):
                        return Refuted(
                            conclusion,
                            (basis_terms[index],),
                            "a reduced Groebner basis element contains a "
                            "monomial divisible by another element's leading "
                            "monomial",
                        )
        basis_size = len(basis_values)
        pair_count = basis_size * (basis_size - 1) // 2
        if pair_count > self._pair_budget:
            return Unverified(
                Reason.BUDGET,
                f"the candidate basis needs {pair_count} critical pairs, "
                f"above the pair budget {self._pair_budget}",
                missing=_PAIR_BUDGET_MISSING,
            )
        for left_index in range(basis_size):
            for right_index in range(left_index + 1, basis_size):
                pair = s_polynomial(
                    self._ring,
                    basis_values[left_index],
                    basis_values[right_index],
                )
                if not normal_form(
                    self._ring, pair, basis_values
                ).is_zero():
                    return Refuted(
                        conclusion,
                        (
                            basis_terms[left_index],
                            basis_terms[right_index],
                        ),
                        "an S-polynomial of the candidate basis has a "
                        "nonzero normal form",
                    )
        for term, value in zip(generator_terms, generator_values):
            if not normal_form(self._ring, value, basis_values).is_zero():
                return Refuted(
                    conclusion,
                    (term,),
                    "an original generator is not in the ideal of the "
                    "candidate basis",
                )
        cofactors = certificate.cofactors
        if len(cofactors) != len(basis_values):
            return InvalidEvidence(
                "the cofactor matrix has one row per basis element"
            )
        if any(
            len(row) != len(generator_values) for row in cofactors
        ):
            return InvalidEvidence(
                "every cofactor row needs one entry per generator"
            )
        cofactor_values = self._values(
            tuple(term for row in cofactors for term in row),
            frame,
            "cofactor",
        )
        if isinstance(cofactor_values, (InvalidEvidence, Unverified)):
            return cofactor_values
        width = len(generator_values)
        for index in range(len(basis_values)):
            row = cofactor_values[index * width : (index + 1) * width]
            combination = self._ring.sum(
                self._ring.mul(cofactor, generator)
                for cofactor, generator in zip(row, generator_values)
            )
            if not self._ring.equal(combination, basis_values[index]):
                return InvalidEvidence(
                    "the cofactor identity does not express the claimed "
                    "basis element"
                )
        return Verified((conclusion,))


def _divides(divisor: Exponents, dividend: Exponents) -> bool:
    """Whether the divisor monomial divides the dividend monomial."""
    return all(
        left <= right for left, right in zip(divisor, dividend)
    )


__all__ = ["GroebnerChecker"]
