"""Shared constructors for the factorization specification and checker tests.

The low-level factorization search is used here only to build honest claims and
certificates; the checker under test recomputes every fact independently.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import TYPE_CHECKING

from support import proposition_in, typed_in, verification_context

from cas.algebra.factorization import (
    FactorizationBudget,
    factor_polynomial_over_q,
    hensel_witness_for_radical,
)
from cas.algebra.integer_polynomial import rational_polynomial_form
from cas.algebra.polynomial import Polynomial
from cas.foundation.ids import FrameId
from cas.kernel.evidence import CheckOutcome, CheckRequest
from cas.language.problems import (
    Coverage,
    DomainRequirement,
    InterpretationRequirement,
    ProblemSpec,
    ResultLanguage,
    ValueDomain,
    VariableRoles,
)
from cas.language.propositions import Proposition
from cas.language.roles import CandidateRole
from cas.language.signatures import LanguageSignature
from cas.language.typing import TypedExpr
from cas.math.algebra.factorization_checker import FactorizationChecker
from cas.math.algebra.factorization_specification import (
    FactorizationCertificate,
    FactorizationVocabulary,
    HenselIrreducibilityWitness,
    factorization_factor_set,
    factorization_product_term,
    factorization_radical_term,
    has_factorization,
    parse_factor_entries,
)
from cas.semantics.bridge import AlgebraView, Rendered, typed_view
from cas.syntax import term as T

if TYPE_CHECKING:
    from cas.runtime.bootstrap import Runtime


@dataclass(frozen=True, slots=True)
class FactorizationSetup:
    runtime: "Runtime"
    frame: FrameId
    signature: LanguageSignature
    vocabulary: FactorizationVocabulary


@dataclass(frozen=True, slots=True)
class FactorizationBundle:
    proposition: Proposition
    source: T.Term
    unit: T.Term
    factors: T.Term
    product: T.Term
    radical: T.Term
    certificate: FactorizationCertificate
    problem: ProblemSpec
    entries: tuple[tuple[T.Term, int], ...]


_DEFAULT = object()


def factorization_setup(runtime: "Runtime") -> FactorizationSetup:
    """Extend the runtime signature with the factorization predicate."""
    predicate = runtime.table.intern("HasFactorization")
    vocabulary = FactorizationVocabulary(predicate, "HasFactorization")
    operators = dict(runtime.signature.operators)
    operators[predicate] = vocabulary.signature
    signature = LanguageSignature.build(
        runtime.signature.heads,
        runtime.signature.binders,
        operators,
    )
    return FactorizationSetup(
        runtime,
        runtime.frame.id,
        signature,
        vocabulary,
    )


def variable(setup: FactorizationSetup) -> T.SymbolRef:
    runtime = setup.runtime
    return T.symbol(runtime.variable, runtime.table.name_of(runtime.variable))


def render(setup: FactorizationSetup, value: Polynomial[Fraction]) -> T.Term:
    """Render one polynomial through the runtime's Q[x] bridge."""
    runtime = setup.runtime
    view = typed_view(
        runtime.bridge,
        T.number(1),
        runtime.frames,
        setup.frame,
        setup.signature,
        runtime.request,
    )
    assert isinstance(view, AlgebraView), view
    rendered = runtime.bridge.render(view, value)
    assert isinstance(rendered, Rendered), rendered
    return rendered.term


def make_problem(
    setup: FactorizationSetup,
    source: T.Term,
    *,
    operation: str = "factor_polynomial",
    coverage: Coverage = Coverage.ONE_VERIFIED,
    language: ResultLanguage = ResultLanguage.DECOMPOSITION,
    region: Proposition | None = None,
    roles: VariableRoles | None = None,
) -> ProblemSpec:
    runtime = setup.runtime
    inputs: tuple[TypedExpr, ...] = (
        typed_in(runtime.frames, setup.frame, setup.signature, source),
    )
    return ProblemSpec(
        operation,
        inputs,
        runtime.request.roles if roles is None else roles,
        region,
        language,
        coverage,
        interpretation_requirement=InterpretationRequirement.FORMAL,
        domain_requirement=DomainRequirement(
            coefficient=ValueDomain.RATIONAL,
            values=ValueDomain.REAL,
        ),
    )


def make_bundle(
    setup: FactorizationSetup,
    *,
    source: T.Term,
    unit: T.Term,
    entries: tuple[tuple[T.Term, int], ...],
    radical: T.Term | None = None,
    witness: HenselIrreducibilityWitness | None = None,
    problem: ProblemSpec | None = None,
    product: T.Term | None = None,
) -> FactorizationBundle:
    """Build one claim, certificate and problem from explicit parts."""
    runtime = setup.runtime
    factors = factorization_factor_set(setup.signature, entries)
    canonical = parse_factor_entries(setup.signature, factors)
    assert canonical is not None
    computed_product = factorization_product_term(
        setup.signature, unit, factors
    )
    product_term = (
        computed_product if product is None else product
    )
    assert product_term is not None
    radical_term = (
        factorization_radical_term(setup.signature, canonical)
        if radical is None
        else radical
    )
    claim = has_factorization(
        setup.vocabulary,
        source,
        variable(setup),
        unit,
        factors,
    )
    proposition = proposition_in(
        runtime.frames, setup.frame, setup.signature, claim
    )
    certificate = FactorizationCertificate(
        source,
        runtime.variable,
        unit,
        factors,
        radical_term,
        witness,
    )
    fixed_problem = (
        make_problem(setup, source) if problem is None else problem
    )
    return FactorizationBundle(
        proposition,
        source,
        unit,
        factors,
        product_term,
        radical_term,
        certificate,
        fixed_problem,
        canonical,
    )


def make_raw_bundle(
    setup: FactorizationSetup,
    *,
    source: T.Term,
    unit: T.Term,
    factors: T.Term,
    candidate: T.Term,
    radical: T.Term,
    witness: HenselIrreducibilityWitness | None = None,
    problem: ProblemSpec | None = None,
) -> FactorizationBundle:
    """Build a deliberately raw claim without canonicalizing the factor set.

    This helper exists for malformed-input tests: it lets the test keep a
    noncanonical or otherwise invalid factor set instead of hiding it behind the
    canonical builder.
    """
    runtime = setup.runtime
    claim = has_factorization(
        setup.vocabulary,
        source,
        variable(setup),
        unit,
        factors,
    )
    proposition = proposition_in(
        runtime.frames, setup.frame, setup.signature, claim
    )
    certificate = FactorizationCertificate(
        source,
        runtime.variable,
        unit,
        factors,
        radical,
        witness,
    )
    fixed_problem = (
        make_problem(setup, source) if problem is None else problem
    )
    return FactorizationBundle(
        proposition,
        source,
        unit,
        factors,
        candidate,
        radical,
        certificate,
        fixed_problem,
        (),
    )


def valid_bundle(
    setup: FactorizationSetup,
    value: Polynomial[Fraction],
    *,
    budget: FactorizationBudget = FactorizationBudget(),
) -> FactorizationBundle:
    """Build the honest search result for `value` as a claim and certificate."""
    runtime = setup.runtime
    ring = runtime.ring
    result = factor_polynomial_over_q(ring, value, budget)
    unit = T.number(result.unit)
    entries = tuple(
        (render(setup, factor), multiplicity)
        for factor, multiplicity in result.factors
    )
    witness: HenselIrreducibilityWitness | None = None
    nonlinear = any(
        ring.degree(factor, 0) >= 2
        for factor, _ in result.factors
    )
    if nonlinear:
        radical_value = ring.one()
        for factor, _ in result.factors:
            radical_value = ring.mul(radical_value, factor)
        lift = hensel_witness_for_radical(ring, radical_value, budget)
        lifted_terms = tuple(
            render(setup, rational_polynomial_form(ring, factor))
            for factor in lift.lifted
        )
        witness = HenselIrreducibilityWitness(
            lift.prime, lift.precision, lifted_terms
        )
    return make_bundle(
        setup,
        source=render(setup, value),
        unit=unit,
        entries=entries,
        witness=witness,
    )


def make_checker(
    setup: FactorizationSetup,
    *,
    pair_budget: int = 200_000,
) -> FactorizationChecker:
    runtime = setup.runtime
    return FactorizationChecker(
        runtime.ring,
        setup.signature,
        setup.vocabulary,
        runtime.bridge,
        runtime.frames,
        runtime.request,
        irreducibility_pair_budget=pair_budget,
    )


def check_bundle(
    setup: FactorizationSetup,
    bundle: FactorizationBundle,
    *,
    candidate: T.Term | None = None,
    role: CandidateRole = CandidateRole.RESULT,
    problem: ProblemSpec | None | object = _DEFAULT,
    certificate: object = _DEFAULT,
    structured: object = _DEFAULT,
    context: object = _DEFAULT,
    checker: FactorizationChecker | None = None,
) -> CheckOutcome:
    runtime = setup.runtime
    actual_candidate = bundle.product if candidate is None else candidate
    actual_problem = (
        bundle.problem if problem is _DEFAULT else problem
    )
    actual_certificate = (
        bundle.certificate if certificate is _DEFAULT else certificate
    )
    actual_structured = (
        (("unit", bundle.unit), ("factors", bundle.factors))
        if structured is _DEFAULT
        else structured
    )
    actual_context = (
        verification_context(
            runtime, setup.frame, algebra=runtime.request
        )
        if context is _DEFAULT
        else context
    )
    actual_checker = make_checker(setup) if checker is None else checker
    return actual_checker.check(
        CheckRequest(
            setup.frame,
            (bundle.proposition,),
            (),
            actual_certificate,
            problem=actual_problem,  # type: ignore[arg-type]
            candidate=actual_candidate,
            candidate_role=role,
            context=actual_context,  # type: ignore[arg-type]
            structured=actual_structured,  # type: ignore[arg-type]
        )
    )
