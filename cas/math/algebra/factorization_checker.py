"""Independent checker for the `HasFactorization` specification over ``Q[x]``.

The checker never imports the factorization search
(``cas.algebra.factorization``) or the modular factorization search
(``cas.algebra.modular_factorization``).  It re-elaborates every claimed term
through the univariate polynomial bridge and rebuilds the product, the radical
and the irreducibility argument from the candidate, the claim and the
certificate.  The only algebra it reuses is the low-level mathematical
vocabulary: integer primitive forms and coefficient bounds, symmetric residues
and positive primitive parts, deterministic Rabin irreducibility and the
deterministic primality certificate.  Those are the facts behind the argument,
not a search module claiming success.

Verification order
------------------

1. The kernel-fixed algebra request must be the one this checker was built for.
2. Exactly one conclusion must parse as `HasFactorization`.
3. The candidate is the visible product built by
   `factorization_product_term` from the claimed unit and factor set, and the
   candidate role is `RESULT`.
4. The certificate is a `FactorizationCertificate` and matches the claim.
5. The structured result is exactly `(("unit", unit), ("factors", factors))`.
6. The fixed problem names operation `factor_polynomial`, the claim variable
   and source, the fixed roles/interpretation/exactness and rational
   coefficients with real values.  It must request a decomposition, one verified
   result, no restricted region and no function inputs.
7. The source is independently typed and admitted.  A zero source is not a
   factorization instance.
8. The unit is a nonzero rational literal equal to the source's leading
   coefficient.
9. The encoded factor set parses back to exactly the canonical form.  Every base
   is independently admitted, monic, nonzero and nonconstant.  The bases are
   pairwise coprime, their degrees sum to the source degree and the claimed
   product multiplies back to the source.
10. The certificate radical is the canonical product of the distinct bases and
    its independent view equals that product.  The radical must be squarefree.
11. A witness is required exactly when some claimed base has degree at least
    two.
12. The Hensel/Mignotte witness is proved independently: the prime is proven
    prime, ``p**k > 2*B`` for the Landau/Mignotte coefficient bound of the
    primitive radical, ``p`` does not divide the leading coefficient, the
    radical is squarefree modulo ``p``, the lifted factors are monic
    nonconstant integer polynomials with coefficients in ``[0, p**k)``, their
    degrees sum to the radical degree, each is irreducible modulo ``p``, they
    are pairwise distinct, and ``R == a*prod(G_i) (mod p**k)``.
13. Each claimed nonlinear factor is proved irreducible by the complete
    Zassenhaus subset/leading-divisor enumeration below.
14. Only then is the single conclusion reported as verified.

Why the witness proves a complete modular factorization
-------------------------------------------------------

Let ``R`` be the primitive integer form of the claimed radical, ``a = lc(R)``
and ``B`` the Landau/Mignotte coefficient bound.  The checker proves that
``p`` is prime, ``p`` does not divide ``a``, ``R/a mod p`` is squarefree and its
complete Berlekamp factorization has pairwise-distinct irreducible factors
``g_i``.  The lifted terms ``G_i`` are monic, reduce to ``g_i`` modulo ``p``
(each is irreducible there), have total degree ``deg(R)`` and satisfy

    R == a * G_1 * ... * G_r (mod p**k).

Uniqueness of Hensel lifting of a complete coprime factorization then makes the
``G_i`` exactly the lifted factors of ``R/a``.  The precision condition
``p**k > 2B`` makes every true factor's symmetric residue unique.

Completeness of the recombination enumeration
---------------------------------------------

Let ``H`` be the primitive integer form of a claimed nonlinear base ``h`` and
``L = lc(H)``.  If ``H`` has a proper factor, one of ``H``'s two nontrivial
factors has degree at most ``deg(H)//2``.  Its leading coefficient divides
``L`` and, by the argument above, its reduction modulo ``p`` is the product of
some subset ``S`` of the ``G_i``; the true factor is the symmetric residue of
``b * prod_{i in S} G_i`` for one positive divisor ``b`` of ``L``, and its
positive primitive part is exactly that integer factor.  The checker enumerates
every positive divisor of ``L`` and every subset whose total lifted degree is
at most ``deg(H)//2``.  An exact division of ``H`` by a candidate refutes
irreducibility; the absence of a successful division after the complete
enumeration proves irreducibility.  Each candidate division test spends one
unit of the pair budget.  Exhaustion reports `Unverified(BUDGET)` with
``{"factorization_irreducibility_budget"}`` and never a partial proof.

Classification
--------------

A bridge or typing refusal is `Unverified(FRAGMENT)` with its structured
`missing`/`conditions`.  A malformed certificate, candidate, structured result,
witness shape or congruence is `InvalidEvidence`.  A mathematical failure
(wrong unit, wrong product, wrong degree sum, non-coprime factors, non-squarefree
radical or a found proper factor) is `Refuted` with the offending term.
Budget exhaustion is `Unverified(BUDGET)`.  A fragment or budget failure is
never turned into a refutation.  This module publishes no judgment; it only
returns the closed `CheckOutcome`.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations

from cas.algebra.finite_field import PrimeField, is_prime64
from cas.algebra.integer_polynomial import (
    coefficient_bound,
    congruent_mod,
    integer_divisors,
    integer_primitive_form,
    positive_primitive_part,
    symmetric_residue,
)
from cas.algebra.modular_polynomial import (
    ModularPolynomialError,
    is_irreducible_mod_prime,
    is_squarefree_mod_prime,
    reduce_mod_prime,
)
from cas.algebra.polynomial import (
    Polynomial,
    PolynomialRing,
    UnivariatePolynomialRing,
)
from cas.algebra.rationals import RationalField
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
    ValueDomain,
)
from cas.language.propositions import Proposition
from cas.language.roles import CandidateRole
from cas.language.signatures import LanguageSignature, StructuralHead
from cas.math.algebra.factorization_specification import (
    FactorizationCertificate,
    FactorizationVocabulary,
    HenselIrreducibilityWitness,
    certificate_matches_claim,
    factorization_factor_set,
    factorization_product_term,
    factorization_radical_term,
    parse_factor_entries,
    parse_factorization,
    rational_literal,
)
from cas.semantics.bridge import (
    AlgebraView,
    PolynomialBridge,
    ViewRefused,
    typed_view,
)
from cas.semantics.frames import FrameStore
from cas.semantics.request import AlgebraRequest
from cas.syntax import term as T

_IRREDUCIBILITY_BUDGET_MISSING = frozenset(
    {"factorization_irreducibility_budget"}
)


@dataclass(frozen=True, slots=True)
class _HenselContext:
    """The independently verified lifted factorization of the radical."""

    ring_z: PolynomialRing[int]
    modulus: int
    lifted: tuple[Polynomial[int], ...]


@dataclass(slots=True)
class _IrreducibilityCounter:
    """The remaining candidate/exact-division tests."""

    remaining: int

    def spend(self) -> bool:
        if self.remaining <= 0:
            return False
        self.remaining -= 1
        return True


class FactorizationChecker:
    """An independent `HasFactorization` checker for one ``Q[x]`` ring."""

    id = "algebra.factorization"
    version = "1"

    def __init__(
        self,
        ring_q: UnivariatePolynomialRing[Fraction],
        signature: LanguageSignature,
        vocabulary: FactorizationVocabulary,
        bridge: PolynomialBridge[Fraction],
        frames: FrameStore,
        request: AlgebraRequest,
        *,
        identifier: str = "algebra.factorization",
        irreducibility_pair_budget: int = 200_000,
    ) -> None:
        if not identifier:
            raise ValueError("a checker needs an identifier")
        if not isinstance(ring_q, UnivariatePolynomialRing):
            raise TypeError(
                "a factorization checker needs a univariate polynomial ring"
            )
        if not isinstance(ring_q.coefficients, RationalField):
            raise TypeError(
                "a factorization checker needs rational coefficients"
            )
        if ring_q is not bridge.ring:
            raise ValueError(
                "the checker ring is not the polynomial bridge's ring"
            )
        if not isinstance(signature, LanguageSignature):
            raise TypeError("a factorization checker needs a signature")
        if not isinstance(vocabulary, FactorizationVocabulary):
            raise TypeError(
                "a factorization checker needs a factorization vocabulary"
            )
        if signature.head_of(vocabulary.symbol) is not None:
            raise ValueError(
                "the factorization predicate cannot be a structural head"
            )
        declared = signature.operator_of(vocabulary.symbol)
        if declared is not None and declared != vocabulary.signature:
            raise ValueError(
                "the signature's factorization operator does not match the "
                "vocabulary"
            )
        for head in (
            StructuralHead.SET,
            StructuralHead.POWER,
            StructuralHead.TIMES,
        ):
            if signature.symbol_of(head) is None:
                raise ValueError(
                    "the factorization language has no "
                    f"{head.value} head"
                )
        target = request.roles.target
        if target is None:
            raise ValueError(
                "a factorization checker needs a target request"
            )
        if target != ring_q.generators[0]:
            raise ValueError(
                "the request target is not the polynomial ring generator"
            )
        if request.roles.parameters or request.parameter_ring is not None:
            raise ValueError(
                "a factorization checker cannot take formal parameters"
            )
        if request.coefficient_domain is not ValueDomain.RATIONAL:
            raise ValueError(
                "a factorization checker needs rational coefficients"
            )
        if request.value_domain is not ValueDomain.REAL:
            raise ValueError(
                "a factorization checker needs real values"
            )
        if isinstance(irreducibility_pair_budget, bool) or not isinstance(
            irreducibility_pair_budget, int
        ):
            raise TypeError(
                "the irreducibility pair budget must be an int "
                "(bool is not accepted)"
            )
        if irreducibility_pair_budget < 0:
            raise ValueError(
                "the irreducibility pair budget must be nonnegative"
            )
        self.id = identifier
        self._ring = ring_q
        self._signature = signature
        self._vocabulary = vocabulary
        self._bridge = bridge
        self._frames = frames
        self._request = request
        self._irreducibility_pair_budget = irreducibility_pair_budget

    def _view(
        self, term: T.Term, frame: FrameId
    ) -> AlgebraView[Polynomial[Fraction]] | Unverified:
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
            return Unverified(
                reason=outcome.reason,
                detail=outcome.detail,
                missing=outcome.missing,
                conditions=outcome.conditions,
            )
        if not isinstance(outcome, AlgebraView):
            return Unverified(
                reason=Reason.FRAGMENT,
                detail=outcome.detail,
                missing=outcome.missing,
            )
        return outcome

    def _base_values(
        self,
        entries: tuple[tuple[T.Term, int], ...],
        frame: FrameId,
    ) -> tuple[Polynomial[Fraction], ...] | InvalidEvidence | Unverified:
        """Admit every factor base and verify the base invariants."""
        values: list[Polynomial[Fraction]] = []
        for factor, _ in entries:
            view = self._view(factor, frame)
            if isinstance(view, Unverified):
                return view
            if view.source.term != factor:
                return InvalidEvidence(
                    "the elaborated factor does not match the claim"
                )
            value = view.value
            if value.is_zero():
                return InvalidEvidence(
                    "a claimed factor is the zero polynomial"
                )
            degree = self._ring.degree(value, 0)
            if degree < 1:
                return InvalidEvidence(
                    "a claimed factor must be nonconstant"
                )
            if not self._ring.coefficients.is_one(
                self._ring.coefficient(value, (degree,))
            ):
                return InvalidEvidence("a claimed factor must be monic")
            values.append(value)
        return tuple(values)

    def _check_witness(
        self,
        frame: FrameId,
        radical: Polynomial[Fraction],
        witness: HenselIrreducibilityWitness,
    ) -> _HenselContext | InvalidEvidence | Unverified:
        """Re-prove the lifted modular factorization without the search."""
        form = integer_primitive_form(self._ring, radical)
        primitive = form.primitive
        ring_z = primitive.owner
        degree = ring_z.degree(primitive, 0)
        if degree < 1:
            return InvalidEvidence(
                "a Hensel witness needs a nonconstant radical"
            )
        leading = ring_z.coefficient(primitive, (degree,))
        if leading <= 0:
            return InvalidEvidence(
                "the primitive radical must have a positive leading "
                "coefficient"
            )
        prime = witness.prime
        try:
            proven_prime = is_prime64(prime)
        except ValueError:
            return InvalidEvidence(
                "the Hensel prime is outside the proven 64-bit range"
            )
        if not proven_prime:
            return InvalidEvidence(
                "the Hensel witness prime is not a proven prime"
            )
        modulus = prime**witness.precision
        bound = coefficient_bound(primitive)
        if modulus <= 2 * bound:
            return InvalidEvidence(
                "the Hensel precision does not exceed twice the coefficient "
                "bound"
            )
        if leading % prime == 0:
            return InvalidEvidence(
                "the Hensel prime divides the radical's leading coefficient"
            )
        ring_p = UnivariatePolynomialRing(
            ring_z.generators[0], PrimeField(prime)
        )
        try:
            reduced = reduce_mod_prime(ring_p, primitive)
            reduced_degree = ring_p.degree(reduced, 0)
            if reduced_degree != degree:
                return InvalidEvidence(
                    "the Hensel prime changed the radical degree"
                )
            inverse = ring_p.coefficients.inv(
                ring_p.coefficient(reduced, (reduced_degree,))
            )
            normalized = ring_p.mul(
                ring_p.constant(inverse), reduced
            )
            if not is_squarefree_mod_prime(ring_p, normalized):
                return InvalidEvidence(
                    "the radical is not squarefree modulo the Hensel prime"
                )
        except ModularPolynomialError as error:
            return InvalidEvidence(
                "the modular radical is outside the checker's fragment: "
                + error.detail
            )
        lifted: list[Polynomial[int]] = []
        degree_sum = 0
        for term in witness.lifted:
            view = self._view(term, frame)
            if isinstance(view, Unverified):
                return view
            if view.source.term != term:
                return InvalidEvidence(
                    "an elaborated lifted factor does not match the witness"
                )
            value = view.value
            if value.is_zero():
                return InvalidEvidence(
                    "a lifted Hensel factor is the zero polynomial"
                )
            factor_degree = self._ring.degree(value, 0)
            if factor_degree < 1:
                return InvalidEvidence(
                    "a lifted Hensel factor must be nonconstant"
                )
            if not self._ring.coefficients.is_one(
                self._ring.coefficient(value, (factor_degree,))
            ):
                return InvalidEvidence(
                    "a lifted Hensel factor must be monic"
                )
            converted = self._integer_polynomial(ring_z, value)
            if converted is None:
                return InvalidEvidence(
                    "a lifted Hensel factor needs integer coefficients"
                )
            if any(
                not 0 <= coefficient < modulus
                for _, coefficient in converted.terms
            ):
                return InvalidEvidence(
                    "a lifted Hensel coefficient lies outside "
                    "[0, p**precision)"
                )
            lifted.append(converted)
            degree_sum += factor_degree
        if not lifted:
            return InvalidEvidence(
                "a Hensel witness needs at least one lifted factor"
            )
        if degree_sum != degree:
            return InvalidEvidence(
                "the lifted factor degrees do not sum to the radical degree"
            )
        product = ring_z.one()
        for lifted_value in lifted:
            product = ring_z.mul(product, lifted_value)
        if ring_z.degree(product, 0) != degree:
            return InvalidEvidence(
                "the lifted product does not have the radical degree"
            )
        try:
            reduced_values: list[Polynomial[int]] = []
            for lifted_value in lifted:
                reduced_value = reduce_mod_prime(ring_p, lifted_value)
                if not is_irreducible_mod_prime(ring_p, reduced_value):
                    return InvalidEvidence(
                        "a lifted Hensel factor is not irreducible modulo the "
                        "prime"
                    )
                reduced_values.append(reduced_value)
            for index, reduced_value in enumerate(reduced_values):
                for other in reduced_values[index + 1 :]:
                    if ring_p.equal(reduced_value, other):
                        return InvalidEvidence(
                            "the lifted Hensel factors are not pairwise "
                            "distinct modulo the prime"
                        )
        except ModularPolynomialError as error:
            return InvalidEvidence(
                "the lifted modular factors are outside the checker's "
                "fragment: " + error.detail
            )
        if not congruent_mod(
            primitive,
            ring_z.mul(ring_z.constant(leading), product),
            modulus,
        ):
            return InvalidEvidence(
                "the lifted factors do not reconstruct the radical modulo "
                "p**precision"
            )
        return _HenselContext(
            ring_z=ring_z,
            modulus=modulus,
            lifted=tuple(lifted),
        )

    def _integer_polynomial(
        self,
        ring_z: PolynomialRing[int],
        value: Polynomial[Fraction],
    ) -> Polynomial[int] | None:
        """Convert a rational polynomial to `ring_z` or None.

        Returning None reports a non-integral coefficient.  The caller checks
        the separate ``[0, p**k)`` range against the witness modulus.
        """
        terms: list[Polynomial[int]] = []
        for exponents, coefficient in value.terms:
            if coefficient.denominator != 1:
                return None
            terms.append(ring_z.monomial(exponents, coefficient.numerator))
        return ring_z.sum(terms)

    def _check_irreducible(
        self,
        conclusion: Proposition,
        context: _HenselContext,
        counter: _IrreducibilityCounter,
        factor_term: T.Term,
        factor_value: Polynomial[Fraction],
    ) -> Refuted | Unverified | None:
        """Run the complete subset/leading-divisor recombination check."""
        form = integer_primitive_form(self._ring, factor_value)
        ring_z = context.ring_z
        primitive = ring_z.sum(
            ring_z.monomial(exponents, coefficient)
            for exponents, coefficient in form.primitive.terms
        )
        degree = ring_z.degree(primitive, 0)
        leading = ring_z.coefficient(primitive, (degree,))
        divisors = integer_divisors(leading)
        degrees = tuple(
            ring_z.degree(value, 0) for value in context.lifted
        )
        for size in range(len(degrees) + 1):
            for subset in combinations(range(len(degrees)), size):
                if sum(degrees[index] for index in subset) > degree // 2:
                    continue
                product = ring_z.one()
                for index in subset:
                    product = ring_z.mul(product, context.lifted[index])
                for divisor in divisors:
                    scaled = ring_z.mul(
                        ring_z.constant(divisor), product
                    )
                    residue = symmetric_residue(
                        ring_z, scaled, context.modulus
                    )
                    candidate = positive_primitive_part(ring_z, residue)
                    candidate_degree = ring_z.degree(candidate, 0)
                    if not 1 <= candidate_degree < degree:
                        continue
                    if not counter.spend():
                        return Unverified(
                            Reason.BUDGET,
                            "the irreducibility enumeration exhausted its "
                            "candidate budget",
                            missing=_IRREDUCIBILITY_BUDGET_MISSING,
                        )
                    try:
                        ring_z.exact_div(primitive, candidate)
                    except ValueError:
                        continue
                    return Refuted(
                        conclusion,
                        (factor_term,),
                        "the claimed nonlinear factor has a proper factor",
                    )
        return None

    def check(self, request: CheckRequest) -> CheckOutcome:
        algebra_mismatch = context_algebra_mismatch(
            request.context, self._request
        )
        if algebra_mismatch is not None:
            return InvalidEvidence(algebra_mismatch)
        if len(request.conclusions) != 1:
            return InvalidEvidence(
                "a factorization certificate names exactly one claim"
            )
        conclusion = request.conclusions[0]
        frame = conclusion.meaning.frame
        claim = parse_factorization(self._vocabulary, conclusion.term)
        if claim is None:
            return InvalidEvidence(
                "the conclusion is not a HasFactorization specification"
            )
        if claim.variable.symbol_id != self._request.roles.target:
            return InvalidEvidence(
                "the specification variable is not the request target"
            )
        expected = factorization_product_term(
            self._signature, claim.unit, claim.factors
        )
        if expected is None:
            return InvalidEvidence(
                "the claimed unit or factor set is not a well-formed "
                "factorization"
            )
        candidate = request.candidate
        if candidate is None:
            return InvalidEvidence(
                "a factorization candidate is required"
            )
        if request.candidate_role is not CandidateRole.RESULT:
            return InvalidEvidence(
                "a factorization candidate needs the result candidate role"
            )
        if candidate != expected:
            return InvalidEvidence(
                "the candidate does not match the claimed factorization"
            )
        certificate = request.certificate
        if not isinstance(certificate, FactorizationCertificate):
            return InvalidEvidence(
                "a factorization certificate is required"
            )
        if not certificate_matches_claim(certificate, claim):
            return InvalidEvidence(
                "the certificate does not match the specification"
            )
        if request.structured != (
            ("unit", claim.unit),
            ("factors", claim.factors),
        ):
            return InvalidEvidence(
                "the structured result is not exactly the claimed unit and "
                "factor set"
            )
        mismatch = problem_mismatch(
            request,
            operations=("factor_polynomial",),
            target=claim.variable.symbol_id,
            inputs=(claim.source,),
            roles=self._request.roles,
            interpretation_requirement=(
                self._request.interpretation_requirement
            ),
            exactness=Exactness.EXACT,
            coefficient_domain=ValueDomain.RATIONAL,
            value_domain=ValueDomain.REAL,
        )
        if mismatch is not None:
            return InvalidEvidence(mismatch)
        problem = request.problem
        if problem is not None:
            if problem.result_language is not ResultLanguage.DECOMPOSITION:
                return InvalidEvidence(
                    "a factorization requires a decomposition result language"
                )
            if problem.coverage is not Coverage.ONE_VERIFIED:
                return InvalidEvidence(
                    "a factorization requires one-verified coverage"
                )
            if problem.region is not None:
                return InvalidEvidence(
                    "a factorization problem has no restricted-region form"
                )
            if problem.function_inputs:
                return InvalidEvidence(
                    "a factorization problem cannot carry function inputs"
                )
        source_view = self._view(claim.source, frame)
        if isinstance(source_view, Unverified):
            return source_view
        if source_view.source.term != claim.source:
            return InvalidEvidence(
                "the elaborated source does not match the claim"
            )
        source = source_view.value
        if source.is_zero():
            return InvalidEvidence(
                "the zero polynomial has no factorization claim"
            )
        unit = rational_literal(claim.unit)
        if unit is None or unit == 0:
            return InvalidEvidence(
                "the claimed unit is not a nonzero rational literal"
            )
        degree = self._ring.degree(source, 0)
        leading = self._ring.coefficient(source, (degree,))
        if unit != leading:
            return Refuted(
                conclusion,
                (claim.unit,),
                "the claimed unit is not the source leading coefficient",
            )
        entries = parse_factor_entries(self._signature, claim.factors)
        if entries is None:
            return InvalidEvidence(
                "the factor set is not the canonical encoded factor set"
            )
        if (
            factorization_factor_set(self._signature, entries)
            != claim.factors
        ):
            return InvalidEvidence(
                "the factor set is not canonical"
            )
        base_values = self._base_values(entries, frame)
        if isinstance(base_values, (InvalidEvidence, Unverified)):
            return base_values
        for index, value in enumerate(base_values):
            for other_index in range(index + 1, len(base_values)):
                other = base_values[other_index]
                if not self._ring.is_one(
                    self._ring.gcd(value, other)
                ):
                    return Refuted(
                        conclusion,
                        (entries[index][0], entries[other_index][0]),
                        "two claimed factors are not coprime",
                    )
        degree_sum = sum(
            multiplicity * self._ring.degree(value, 0)
            for value, (_, multiplicity) in zip(base_values, entries)
        )
        if degree_sum != degree:
            return Refuted(
                conclusion,
                (claim.factors,),
                "the claimed factor degrees do not sum to the source degree",
            )
        product = self._ring.one()
        for value, (_, multiplicity) in zip(base_values, entries):
            product = self._ring.mul(
                product, self._ring.pow(value, multiplicity)
            )
        if not self._ring.equal(
            self._ring.mul(self._ring.constant(unit), product), source
        ):
            return Refuted(
                conclusion,
                (claim.source, claim.factors),
                "the claimed factorization does not multiply back to the "
                "source",
            )
        radical_term = factorization_radical_term(
            self._signature, entries
        )
        if certificate.radical != radical_term:
            return InvalidEvidence(
                "the certificate radical is not the canonical product of the "
                "distinct factors"
            )
        radical_view = self._view(certificate.radical, frame)
        if isinstance(radical_view, Unverified):
            return radical_view
        if radical_view.source.term != certificate.radical:
            return InvalidEvidence(
                "the elaborated radical does not match the certificate"
            )
        radical = self._ring.one()
        for value in base_values:
            radical = self._ring.mul(radical, value)
        if not self._ring.equal(radical_view.value, radical):
            return InvalidEvidence(
                "the certificate radical does not equal the product of the "
                "distinct factors"
            )
        if radical.is_zero():
            return InvalidEvidence(
                "the claimed radical is the zero polynomial"
            )
        if not self._ring.is_constant(radical):
            derivative = self._ring.derivative(radical, 0)
            if not self._ring.is_one(
                self._ring.gcd(radical, derivative)
            ):
                return Refuted(
                    conclusion,
                    (certificate.radical,),
                    "the claimed radical is not squarefree",
                )
        nonlinear = tuple(
            (term, value)
            for (term, _), value in zip(entries, base_values)
            if self._ring.degree(value, 0) >= 2
        )
        witness = certificate.irreducibility
        if not nonlinear:
            if witness is not None:
                return InvalidEvidence(
                    "a factorization with only linear factors needs no "
                    "irreducibility witness"
                )
            return Verified((conclusion,))
        if witness is None:
            return InvalidEvidence(
                "a nonlinear claimed factor needs an irreducibility witness"
            )
        context = self._check_witness(frame, radical, witness)
        if isinstance(context, (InvalidEvidence, Unverified)):
            return context
        counter = _IrreducibilityCounter(
            self._irreducibility_pair_budget
        )
        for factor_term, factor_value in nonlinear:
            outcome = self._check_irreducible(
                conclusion,
                context,
                counter,
                factor_term,
                factor_value,
            )
            if outcome is not None:
                return outcome
        return Verified((conclusion,))


__all__ = ["FactorizationChecker"]
