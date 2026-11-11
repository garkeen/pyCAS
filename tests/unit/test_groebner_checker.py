"""The independent `HasGroebnerBasis` checker over a fixed monomial order."""

from dataclasses import dataclass
from fractions import Fraction
from typing import TYPE_CHECKING

import pytest
from support import (
    head_app,
    multivariate_setup,
    proposition_in,
    typed_in,
    verification_context,
)

from cas.algebra.groebner import GroebnerBasis, buchberger
from cas.algebra.integers import IntegerRing
from cas.algebra.parents import ParentRegistry, ParentSpec
from cas.algebra.polynomial import MonomialOrder, Polynomial, PolynomialRing
from cas.algebra.rationals import RationalField
from cas.foundation.ids import FrameId, SymbolId
from cas.kernel.evidence import (
    CheckRequest,
    InvalidEvidence,
    Refuted,
    Unverified,
    Verified,
)
from cas.language import sorts as S
from cas.language.decisions import Reason
from cas.language.problems import (
    Coverage,
    DomainRequirement,
    InterpretationRequirement,
    ParameterMode,
    ProblemSpec,
    ResultLanguage,
    ValueDomain,
    VariableRoles,
)
from cas.language.propositions import Proposition
from cas.language.roles import CandidateRole
from cas.language.sets import set_members, set_term
from cas.language.signatures import LanguageSignature, StructuralHead
from cas.math.algebra.groebner_checker import GroebnerChecker
from cas.math.algebra.groebner_specification import (
    GroebnerCertificate,
    GroebnerVocabulary,
    has_groebner_basis,
)
from cas.semantics.bridge import (
    AlgebraView,
    MultivariatePolynomialBridge,
    Rendered,
    typed_view,
)
from cas.semantics.request import AlgebraRequest, Interpretation
from cas.syntax import term as T

if TYPE_CHECKING:
    from cas.runtime.bootstrap import Runtime


@dataclass(frozen=True, slots=True)
class CheckerSetup:
    runtime: "Runtime"
    frame: FrameId
    ring: PolynomialRing
    request: AlgebraRequest
    signature: LanguageSignature
    vocabulary: GroebnerVocabulary
    bridge: MultivariatePolynomialBridge
    symbols: tuple[SymbolId, ...]


@dataclass(frozen=True, slots=True)
class ClaimBundle:
    proposition: Proposition
    generators: T.Term
    basis: T.Term
    generator_terms: tuple[T.Term, ...]
    basis_terms: tuple[T.Term, ...]


def groebner_setup(runtime: "Runtime") -> CheckerSetup:
    """Assemble Q[x, y] with the Groebner predicate added to the signature.

    The predicate is not registered by the runtime yet: this slice adds only the
    specification and the checker, so the test builds the operator entry itself.
    """
    base = multivariate_setup(runtime)
    predicate = runtime.table.intern("HasGroebnerBasis")
    order_symbol = runtime.table.intern("lex_order")
    vocabulary = GroebnerVocabulary(
        predicate,
        "HasGroebnerBasis",
        order_symbol,
        MonomialOrder.LEX,
    )
    operators = dict(runtime.signature.operators)
    operators[predicate] = vocabulary.signature
    signature = LanguageSignature.build(
        runtime.signature.heads,
        runtime.signature.binders,
        operators,
    )
    bridge = MultivariatePolynomialBridge(
        base.ring,
        base.parent,
        runtime.world.id,
        signature,
        runtime.table.name_of,
        T.number,
    )
    return CheckerSetup(
        runtime,
        base.frame,
        base.ring,
        base.request,
        signature,
        vocabulary,
        bridge,
        base.symbols,
    )


def integer_setup(runtime: "Runtime") -> CheckerSetup:
    """Assemble Z[x, y] to exercise the coefficient-field boundary."""
    base = groebner_setup(runtime)
    integers = IntegerRing()
    ring = PolynomialRing(base.symbols, integers, MonomialOrder.LEX)
    registry = ParentRegistry()
    coefficient = registry.intern(ParentSpec("Z"), integers)
    parent = registry.intern(
        ParentSpec(
            "polynomial",
            base=ParentSpec("Z"),
            generators=base.symbols,
            options=(("monomial_order", "lex"),),
        ),
        ring,
    )
    bridge = MultivariatePolynomialBridge(
        ring,
        parent,
        runtime.world.id,
        base.signature,
        runtime.table.name_of,
        T.number,
    )
    request = AlgebraRequest(
        coefficient=coefficient,
        coefficient_domain=ValueDomain.INTEGER,
        parameter_ring=None,
        roles=VariableRoles(
            None,
            (),
            ParameterMode.SPECIFIED_VALUES,
            runtime.world.id,
            None,
            (),
            base.symbols,
            (S.REAL, S.REAL),
        ),
        interpretation=Interpretation.FORMAL,
    )
    vocabulary = GroebnerVocabulary(
        base.vocabulary.symbol,
        "HasGroebnerBasis",
        base.vocabulary.order_symbol,
        MonomialOrder.LEX,
    )
    return CheckerSetup(
        runtime,
        base.frame,
        ring,
        request,
        base.signature,
        vocabulary,
        bridge,
        base.symbols,
    )


def render(setup: CheckerSetup, value: Polynomial) -> T.Term:
    view = typed_view(
        setup.bridge,
        T.number(1),
        setup.runtime.frames,
        setup.frame,
        setup.signature,
        setup.request,
    )
    assert isinstance(view, AlgebraView), view
    rendered = setup.bridge.render(view, value)
    assert isinstance(rendered, Rendered), rendered
    return rendered.term


def make_claim(
    setup: CheckerSetup,
    generator_values: tuple[Polynomial, ...],
    basis_values: tuple[Polynomial, ...],
    *,
    order_term: T.Term | None = None,
) -> ClaimBundle:
    generator_terms = tuple(
        render(setup, value) for value in generator_values
    )
    basis_terms = tuple(render(setup, value) for value in basis_values)
    generators = set_term(setup.signature, generator_terms)
    basis = set_term(setup.signature, basis_terms)
    order = (
        setup.vocabulary.order_term()
        if order_term is None
        else order_term
    )
    proposition = proposition_in(
        setup.runtime.frames,
        setup.frame,
        setup.signature,
        has_groebner_basis(
            setup.vocabulary, generators, basis, order
        ),
    )
    canonical_generators = set_members(generators, setup.signature)
    canonical_basis = set_members(basis, setup.signature)
    assert canonical_generators is not None
    assert canonical_basis is not None
    return ClaimBundle(
        proposition,
        generators,
        basis,
        canonical_generators,
        canonical_basis,
    )


def make_problem(
    setup: CheckerSetup,
    generator_terms: tuple[T.Term, ...],
    *,
    coverage: Coverage = Coverage.COMPLETE_SET,
    language: ResultLanguage = ResultLanguage.SET,
    region: Proposition | None = None,
) -> ProblemSpec:
    inputs = tuple(
        typed_in(
            setup.runtime.frames,
            setup.frame,
            setup.signature,
            term,
        )
        for term in generator_terms
    )
    return ProblemSpec(
        "groebner_basis",
        inputs,
        setup.request.roles,
        region,
        language,
        coverage,
        interpretation_requirement=InterpretationRequirement.FORMAL,
        domain_requirement=DomainRequirement(
            coefficient=setup.request.coefficient_domain,
            values=setup.request.value_domain,
        ),
    )


def make_checker(
    setup: CheckerSetup, *, pair_budget: int = 4096
) -> GroebnerChecker:
    return GroebnerChecker(
        setup.ring,
        setup.signature,
        setup.vocabulary,
        setup.bridge,
        setup.runtime.frames,
        setup.request,
        pair_budget=pair_budget,
    )


def check(
    setup: CheckerSetup,
    bundle: ClaimBundle,
    certificate: GroebnerCertificate,
    *,
    candidate: T.Term | None = None,
    role: CandidateRole = CandidateRole.SET,
    problem: ProblemSpec | None = None,
    checker: GroebnerChecker | None = None,
) -> object:
    actual = make_checker(setup) if checker is None else checker
    return actual.check(
        CheckRequest(
            setup.frame,
            (bundle.proposition,),
            (),
            certificate,
            problem=problem,
            candidate=bundle.basis if candidate is None else candidate,
            candidate_role=role,
            context=verification_context(
                setup.runtime, setup.frame, algebra=setup.request
            ),
        )
    )


def record_certificate(
    setup: CheckerSetup,
    record: GroebnerBasis,
    bundle: ClaimBundle,
) -> GroebnerCertificate:
    rendered_generators = tuple(
        render(setup, value) for value in record.original_generators
    )
    rendered_basis = tuple(
        render(setup, value) for value in record.basis
    )
    assert len(set(rendered_generators)) == len(rendered_generators)
    assert len(set(rendered_basis)) == len(rendered_basis)
    generator_position = {
        term: index for index, term in enumerate(rendered_generators)
    }
    basis_position = {
        term: index for index, term in enumerate(rendered_basis)
    }
    assert set(rendered_generators) == set(bundle.generator_terms)
    assert set(rendered_basis) == set(bundle.basis_terms)
    rows = []
    for term in bundle.basis_terms:
        cofactors = record.cofactors[basis_position[term]]
        rows.append(
            tuple(
                render(setup, cofactors[generator_position[generator]])
                for generator in bundle.generator_terms
            )
        )
    return GroebnerCertificate(tuple(rows))


def identity_certificate(
    setup: CheckerSetup,
    generator_values: tuple[Polynomial, ...],
    basis_values: tuple[Polynomial, ...],
    bundle: ClaimBundle,
) -> GroebnerCertificate:
    one = setup.ring.one()
    zero = setup.ring.zero()
    row_for: dict[T.Term, tuple[T.Term, ...]] = {}
    for value in basis_values:
        target = render(setup, value)
        row = tuple(
            render(setup, one) if term == target else render(setup, zero)
            for term in bundle.generator_terms
        )
        row_for[target] = row
    return GroebnerCertificate(
        tuple(row_for[term] for term in bundle.basis_terms)
    )


def x(setup: CheckerSetup) -> Polynomial:
    return setup.ring.generator(0)


def y(setup: CheckerSetup) -> Polynomial:
    return setup.ring.generator(1)


def circle(setup: CheckerSetup) -> Polynomial:
    ring = setup.ring
    return ring.sum(
        (
            ring.monomial((2, 0), Fraction(1)),
            ring.monomial((0, 2), Fraction(1)),
            ring.constant(Fraction(-1)),
        )
    )


def line(setup: CheckerSetup) -> Polynomial:
    ring = setup.ring
    return ring.sub(ring.generator(0), ring.generator(1))


def test_the_checker_verifies_the_circle_line_reduced_basis(runtime):
    setup = groebner_setup(runtime)
    record = buchberger(setup.ring, (circle(setup), line(setup)), budget=1000)
    bundle = make_claim(setup, record.original_generators, record.basis)
    certificate = record_certificate(setup, record, bundle)
    problem = make_problem(setup, bundle.generator_terms)
    outcome = check(
        setup, bundle, certificate, problem=problem
    )
    assert isinstance(outcome, Verified), outcome
    assert outcome.checked == (bundle.proposition,)


def test_the_checker_verifies_the_parabola_reduced_basis(runtime):
    setup = groebner_setup(runtime)
    ring = setup.ring
    first = ring.sub(
        ring.mul(ring.generator(0), ring.generator(0)),
        ring.generator(1),
    )
    second = ring.sub(
        ring.generator(0),
        ring.mul(ring.generator(1), ring.generator(1)),
    )
    record = buchberger(ring, (first, second), budget=1000)
    bundle = make_claim(setup, record.original_generators, record.basis)
    certificate = record_certificate(setup, record, bundle)
    outcome = check(setup, bundle, certificate)
    assert isinstance(outcome, Verified), outcome


def test_a_zero_ideal_has_the_empty_reduced_basis(runtime):
    setup = groebner_setup(runtime)
    bundle = make_claim(setup, (), ())
    outcome = check(setup, bundle, GroebnerCertificate(()))
    assert isinstance(outcome, Verified), outcome


def test_a_zero_generator_still_describes_the_zero_ideal(runtime):
    setup = groebner_setup(runtime)
    zero = setup.ring.zero()
    bundle = make_claim(setup, (zero,), ())
    problem = make_problem(setup, bundle.generator_terms)
    outcome = check(
        setup, bundle, GroebnerCertificate(()), problem=problem
    )
    assert isinstance(outcome, Verified), outcome


def test_the_unit_ideal_has_the_constant_one_basis(runtime):
    setup = groebner_setup(runtime)
    ring = setup.ring
    three = ring.constant(Fraction(3))
    one = ring.one()
    third = ring.constant(Fraction(1, 3))
    bundle = make_claim(setup, (three,), (one,))
    certificate = GroebnerCertificate(((render(setup, third),),))
    outcome = check(setup, bundle, certificate)
    assert isinstance(outcome, Verified), outcome


def test_a_zero_basis_element_is_refuted(runtime):
    setup = groebner_setup(runtime)
    zero = setup.ring.zero()
    bundle = make_claim(setup, (), (zero,))
    outcome = check(setup, bundle, GroebnerCertificate(((),)))
    assert isinstance(outcome, Refuted), outcome
    assert outcome.witnesses == (bundle.basis_terms[0],)


def test_a_non_monic_basis_element_is_refuted(runtime):
    setup = groebner_setup(runtime)
    scaled = setup.ring.monomial((1, 0), Fraction(2))
    bundle = make_claim(setup, (scaled,), (scaled,))
    certificate = identity_certificate(
        setup, (scaled,), (scaled,), bundle
    )
    outcome = check(setup, bundle, certificate)
    assert isinstance(outcome, Refuted), outcome
    assert outcome.witnesses == (bundle.basis_terms[0],)


def test_a_non_interreduced_basis_is_refuted(runtime):
    setup = groebner_setup(runtime)
    base = x(setup)
    multiple = setup.ring.mul(base, y(setup))
    bundle = make_claim(
        setup, (base, multiple), (base, multiple)
    )
    certificate = identity_certificate(
        setup, (base, multiple), (base, multiple), bundle
    )
    outcome = check(setup, bundle, certificate)
    assert isinstance(outcome, Refuted), outcome
    assert len(outcome.witnesses) == 1


def test_a_non_groebner_reduced_basis_is_refuted_by_an_s_pair(runtime):
    setup = groebner_setup(runtime)
    ring = setup.ring
    first = ring.sub(
        ring.mul(ring.generator(0), ring.generator(1)), ring.one()
    )
    second = ring.sub(
        ring.mul(ring.generator(0), ring.generator(0)),
        ring.generator(1),
    )
    bundle = make_claim(setup, (first, second), (first, second))
    certificate = identity_certificate(
        setup, (first, second), (first, second), bundle
    )
    outcome = check(setup, bundle, certificate)
    assert isinstance(outcome, Refuted), outcome
    assert len(outcome.witnesses) == 2


def test_a_generator_outside_the_basis_ideal_is_refuted(runtime):
    setup = groebner_setup(runtime)
    base = x(setup)
    generators = (base, y(setup))
    bundle = make_claim(setup, generators, (base,))
    certificate = identity_certificate(
        setup, generators, (base,), bundle
    )
    outcome = check(setup, bundle, certificate)
    assert isinstance(outcome, Refuted), outcome
    assert outcome.witnesses == (render(setup, y(setup)),)


def test_a_wrong_cofactor_shape_is_invalid_evidence(runtime):
    setup = groebner_setup(runtime)
    base = x(setup)
    bundle = make_claim(setup, (base,), (base,))
    outcome = check(setup, bundle, GroebnerCertificate(()))
    assert isinstance(outcome, InvalidEvidence), outcome


def test_a_wrong_cofactor_identity_is_invalid_evidence(runtime):
    setup = groebner_setup(runtime)
    base = x(setup)
    bundle = make_claim(setup, (base,), (base,))
    wrong = setup.ring.constant(Fraction(2))
    certificate = GroebnerCertificate(((render(setup, wrong),),))
    outcome = check(setup, bundle, certificate)
    assert isinstance(outcome, InvalidEvidence), outcome


def test_a_candidate_that_differs_from_the_claim_basis_is_invalid(runtime):
    setup = groebner_setup(runtime)
    base = x(setup)
    bundle = make_claim(setup, (base,), (base,))
    certificate = identity_certificate(setup, (base,), (base,), bundle)
    empty = set_term(setup.signature, ())
    outcome = check(setup, bundle, certificate, candidate=empty)
    assert isinstance(outcome, InvalidEvidence), outcome


def test_a_wrong_candidate_role_is_invalid(runtime):
    setup = groebner_setup(runtime)
    base = x(setup)
    bundle = make_claim(setup, (base,), (base,))
    certificate = identity_certificate(setup, (base,), (base,), bundle)
    outcome = check(
        setup, bundle, certificate, role=CandidateRole.RESULT
    )
    assert isinstance(outcome, InvalidEvidence), outcome


def test_a_malformed_order_quote_is_invalid_evidence(runtime):
    setup = groebner_setup(runtime)
    base = x(setup)
    bundle = make_claim(
        setup,
        (base,),
        (base,),
        order_term=T.quote(T.number(1)),
    )
    certificate = identity_certificate(setup, (base,), (base,), bundle)
    outcome = check(setup, bundle, certificate)
    assert isinstance(outcome, InvalidEvidence), outcome


def test_another_order_symbol_is_unverified_not_refuted(runtime):
    setup = groebner_setup(runtime)
    base = x(setup)
    other = runtime.table.intern("other_order")
    bundle = make_claim(
        setup,
        (base,),
        (base,),
        order_term=T.quote(T.symbol(other, "grlex")),
    )
    certificate = identity_certificate(setup, (base,), (base,), bundle)
    outcome = check(setup, bundle, certificate)
    assert isinstance(outcome, Unverified), outcome
    assert outcome.reason is Reason.FRAGMENT
    assert outcome.missing == frozenset({"monomial_order"})


def test_a_module_over_a_non_field_is_unverified(runtime):
    setup = integer_setup(runtime)
    scaled = setup.ring.monomial((1, 0), 2)
    bundle = make_claim(setup, (scaled,), (scaled,))
    certificate = identity_certificate(
        setup, (scaled,), (scaled,), bundle
    )
    outcome = check(setup, bundle, certificate)
    assert isinstance(outcome, Unverified), outcome
    assert outcome.reason is Reason.FRAGMENT
    assert "coefficient_field" in outcome.missing


def test_pair_budget_exhaustion_is_unverified(runtime):
    setup = groebner_setup(runtime)
    record = buchberger(
        setup.ring, (circle(setup), line(setup)), budget=1000
    )
    bundle = make_claim(setup, record.original_generators, record.basis)
    certificate = record_certificate(setup, record, bundle)
    outcome = check(
        setup,
        bundle,
        certificate,
        checker=make_checker(setup, pair_budget=0),
    )
    assert isinstance(outcome, Unverified), outcome
    assert outcome.reason is Reason.BUDGET
    assert outcome.missing == frozenset({"groebner_pair_budget"})


def test_a_problem_generator_set_mismatch_is_invalid_evidence(runtime):
    setup = groebner_setup(runtime)
    record = buchberger(
        setup.ring, (circle(setup), line(setup)), budget=1000
    )
    bundle = make_claim(setup, record.original_generators, record.basis)
    certificate = record_certificate(setup, record, bundle)
    problem = make_problem(setup, (bundle.generator_terms[0],))
    outcome = check(
        setup, bundle, certificate, problem=problem
    )
    assert isinstance(outcome, InvalidEvidence), outcome
    assert "generator set" in outcome.detail


def test_a_region_restricted_problem_is_invalid_evidence(runtime):
    setup = groebner_setup(runtime)
    base = x(setup)
    bundle = make_claim(setup, (base,), (base,))
    certificate = identity_certificate(setup, (base,), (base,), bundle)
    region = proposition_in(
        setup.runtime.frames,
        setup.frame,
        setup.signature,
        head_app(
            setup.signature,
            StructuralHead.GT,
            render(setup, base),
            T.number(0),
        ),
    )
    problem = make_problem(
        setup, bundle.generator_terms, region=region
    )
    outcome = check(
        setup, bundle, certificate, problem=problem
    )
    assert isinstance(outcome, InvalidEvidence), outcome
    assert "restricted-region" in outcome.detail


@pytest.mark.parametrize(
    "coverage,language",
    (
        (Coverage.SOUND_SET, ResultLanguage.SET),
        (Coverage.COMPLETE_SET, ResultLanguage.EXPRESSION),
    ),
)
def test_a_problem_with_the_wrong_coverage_or_language_is_invalid(
    runtime, coverage, language
):
    setup = groebner_setup(runtime)
    record = buchberger(
        setup.ring, (circle(setup), line(setup)), budget=1000
    )
    bundle = make_claim(setup, record.original_generators, record.basis)
    certificate = record_certificate(setup, record, bundle)
    problem = make_problem(
        setup,
        bundle.generator_terms,
        coverage=coverage,
        language=language,
    )
    outcome = check(
        setup, bundle, certificate, problem=problem
    )
    assert isinstance(outcome, InvalidEvidence), outcome


def test_the_checker_validates_its_ring_request_and_budget(runtime):
    setup = groebner_setup(runtime)
    other_ring = PolynomialRing(
        setup.symbols, RationalField(), MonomialOrder.LEX
    )
    with pytest.raises(ValueError):
        GroebnerChecker(
            other_ring,
            setup.signature,
            setup.vocabulary,
            setup.bridge,
            setup.runtime.frames,
            setup.request,
        )
    with pytest.raises(ValueError):
        GroebnerChecker(
            setup.ring,
            setup.signature,
            setup.vocabulary,
            setup.bridge,
            setup.runtime.frames,
            setup.runtime.request,
        )
    with pytest.raises(ValueError):
        make_checker(setup, pair_budget=-1)
    with pytest.raises(TypeError):
        make_checker(setup, pair_budget=True)  # type: ignore[arg-type]
