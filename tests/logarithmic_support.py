"""Shared constructors for the rational-logarithmic checker tests.

The low-level rational-residue search is used here only to build honest claims
and certificates; the checker under test recomputes every fact independently.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import TYPE_CHECKING

from support import proposition_in, typed_in, verification_context

from cas.algebra.logarithmic_integration import rational_log_integral
from cas.algebra.parents import ParentRegistry, ParentSpec
from cas.algebra.polynomial import Polynomial
from cas.algebra.rational import RationalFunction, RationalFunctionField
from cas.foundation.ids import FrameId
from cas.kernel.evidence import (
    AlgebraService,
    CheckOutcome,
    CheckRequest,
    DecisionService,
    DefinednessService,
    VerificationContext,
)
from cas.language import sorts as S
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
from cas.language.signatures import (
    LanguageSignature,
    OperatorSignature,
    StructuralHead,
)
from cas.math.calculus.integration.logarithmic_checker import (
    LogarithmicIntegrationChecker,
)
from cas.math.calculus.integration.logarithmic_operation import (
    LogarithmicIntegrationOperation,
)
from cas.math.calculus.integration.logarithmic_specification import (
    RationalLogAntiderivativeCertificate,
    RationalLogVocabulary,
    has_rational_log_antiderivative,
    rational_log_antiderivative_term,
    rational_log_term_set,
)
from cas.math.calculus.integration.rational_view import (
    RationalFunctionView,
)
from cas.semantics.bridge import (
    AlgebraView,
    RationalFunctionBridge,
    Rendered,
    typed_view,
)
from cas.semantics.conditions import and_all
from cas.semantics.request import AlgebraRequest
from cas.syntax import term as T

if TYPE_CHECKING:
    from cas.runtime.bootstrap import Runtime


@dataclass(frozen=True, slots=True)
class LogSetup:
    runtime: "Runtime"
    frame: FrameId
    signature: LanguageSignature
    vocabulary: RationalLogVocabulary
    bridge: RationalFunctionBridge[Fraction]
    request: AlgebraRequest


@dataclass(frozen=True, slots=True)
class LogBundle:
    proposition: Proposition
    source: T.Term
    polynomial_part: T.Term
    log_terms: T.Term
    result: T.Term
    region: T.Term
    certificate: RationalLogAntiderivativeCertificate
    problem: ProblemSpec


_DEFAULT = object()


def log_setup(runtime: "Runtime") -> LogSetup:
    """Extend the runtime language with the rational-log predicate and log."""
    predicate = runtime.table.intern("HasRationalLogAntiderivative")
    log_symbol = runtime.table.intern("log")
    vocabulary = RationalLogVocabulary(
        predicate,
        "HasRationalLogAntiderivative",
        log_symbol,
        "log",
    )
    operators = dict(runtime.signature.operators)
    operators[predicate] = vocabulary.signature
    operators[log_symbol] = OperatorSignature((S.REAL,), S.REAL)
    signature = LanguageSignature.build(
        runtime.signature.heads,
        runtime.signature.binders,
        operators,
    )
    field = RationalFunctionField(runtime.ring)
    registry = ParentRegistry()
    parent = registry.intern(
        ParentSpec(
            "rational_function",
            base=runtime.parent.spec,
            generators=runtime.ring.generators,
            options=(),
        ),
        field,
    )
    bridge = RationalFunctionBridge(
        field,
        parent,
        runtime.world.id,
        runtime.signature,
        runtime.frames,
        runtime.table.name_of,
        T.number,
    )
    return LogSetup(
        runtime,
        runtime.frame.id,
        signature,
        vocabulary,
        bridge,
        runtime.request,
    )


def variable(setup: LogSetup) -> T.SymbolRef:
    runtime = setup.runtime
    return T.symbol(runtime.variable, runtime.table.name_of(runtime.variable))


def generator(setup: LogSetup) -> Polynomial[Fraction]:
    return setup.bridge.field.polynomials.generator(0)


def polynomial(
    setup: LogSetup,
    terms: tuple[tuple[int, Fraction], ...],
) -> Polynomial[Fraction]:
    ring = setup.bridge.field.polynomials
    return ring.sum(
        ring.monomial((exponent,), coefficient)
        for exponent, coefficient in terms
    )


def linear_factor(setup: LogSetup, root: int) -> Polynomial[Fraction]:
    ring = setup.bridge.field.polynomials
    return ring.sub(
        generator(setup), ring.constant(Fraction(root))
    )


def monic_product(
    setup: LogSetup, roots: tuple[int, ...]
) -> Polynomial[Fraction]:
    ring = setup.bridge.field.polynomials
    value = ring.one()
    for root in roots:
        value = ring.mul(value, linear_factor(setup, root))
    return value


def view_of(
    setup: LogSetup, term: T.Term
) -> AlgebraView[RationalFunction[Fraction]]:
    runtime = setup.runtime
    outcome = typed_view(
        setup.bridge,
        term,
        runtime.frames,
        setup.frame,
        runtime.signature,
        runtime.request,
    )
    assert isinstance(outcome, AlgebraView), outcome
    return outcome


def render(
    setup: LogSetup, value: RationalFunction[Fraction]
) -> T.Term:
    view = view_of(setup, T.number(1))
    outcome = setup.bridge.render(view, value)
    assert isinstance(outcome, Rendered), outcome
    return outcome.term


def render_polynomial(
    setup: LogSetup, value: Polynomial[Fraction]
) -> T.Term:
    return render(setup, setup.bridge.field.of_polynomial(value))


def checker(setup: LogSetup) -> LogarithmicIntegrationChecker:
    runtime = setup.runtime
    return LogarithmicIntegrationChecker(
        setup.bridge,
        setup.signature,
        setup.vocabulary,
        runtime.frames,
        runtime.request,
    )


def rational_view(setup: LogSetup) -> RationalFunctionView[Fraction]:
    """The request-local view the L2 checker is admitted for."""
    return RationalFunctionView(
        setup.request,
        setup.bridge.field,
        setup.bridge.parent,
        setup.bridge,
        checker(setup).id,
    )


def logarithmic_operation(
    setup: LogSetup,
) -> LogarithmicIntegrationOperation:
    """The operation over the setup's single rational-function view."""
    return LogarithmicIntegrationOperation(
        setup.signature,
        setup.runtime.frames,
        setup.vocabulary,
        (rational_view(setup),),
        setup.runtime.table.name_of,
        setup.runtime.variable,
    )


def full_context(setup: LogSetup) -> VerificationContext:
    """A context with both the decision and definedness services."""
    runtime = setup.runtime
    decision = DecisionService(setup.signature)
    return VerificationContext(
        runtime.world.id,
        setup.frame,
        runtime.frames,
        decision=decision,
        definedness=DefinednessService(
            decision, runtime.frames, setup.frame
        ),
        algebra=AlgebraService(runtime.request),
    )


def honest_region(
    setup: LogSetup,
    source: T.Term,
    polynomial_part: T.Term,
    arguments: tuple[T.Term, ...],
) -> Proposition:
    """The source/part definedness plus every ``Gt(g, 0)`` condition."""
    conditions: list[T.Term] = []
    for term in (source, polynomial_part):
        view = view_of(setup, term)
        for region in (view.source_domain, view.valid_on):
            if region is not None and region.term != T.TRUE:
                conditions.append(region.term)
    for argument in arguments:
        conditions.append(
            T.app(
                setup.signature.head_term(StructuralHead.GT),
                argument,
                T.number(0),
            )
        )
    return proposition_in(
        setup.runtime.frames,
        setup.frame,
        setup.signature,
        and_all(setup.signature, *conditions),
    )


def make_problem(
    setup: LogSetup,
    source: T.Term,
    *,
    operation: str = "integrate_rational_logarithmic",
    coverage: Coverage = Coverage.ONE_VERIFIED,
    language: ResultLanguage = ResultLanguage.DECOMPOSITION,
    region: Proposition | None = None,
    roles: VariableRoles | None = None,
    inputs: tuple[T.Term, ...] | None = None,
) -> ProblemSpec:
    runtime = setup.runtime
    terms = (source,) if inputs is None else inputs
    typed_inputs = tuple(
        typed_in(
            runtime.frames,
            setup.frame,
            setup.signature,
            term,
        )
        for term in terms
    )
    return ProblemSpec(
        operation,
        typed_inputs,
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
    setup: LogSetup,
    *,
    source_value: RationalFunction[Fraction],
    polynomial_part_value: RationalFunction[Fraction],
    entries: tuple[tuple[Fraction, Polynomial[Fraction]], ...] = (),
    log_terms: T.Term | None = None,
    log_arguments: tuple[T.Term, ...] = (),
    result: T.Term | None = None,
    region: Proposition | None = None,
    problem: ProblemSpec | None = None,
) -> LogBundle:
    """Assemble one claim, certificate and problem from explicit parts.

    When ``log_terms`` is omitted the canonical set is built from ``entries``.
    The raw form exists for malformed-encoding tests; it never bypasses the
    certificate or problem constructors.
    """
    source = render(setup, source_value)
    polynomial_part = render(setup, polynomial_part_value)
    if log_terms is None:
        rendered = tuple(
            (coefficient, render_polynomial(setup, argument))
            for coefficient, argument in entries
        )
        log_terms = rational_log_term_set(
            setup.signature,
            setup.vocabulary.log_function,
            rendered,
        )
        log_arguments = tuple(argument for _, argument in rendered)
    actual_result = (
        rational_log_antiderivative_term(
            setup.signature, polynomial_part, log_terms
        )
        if result is None
        else result
    )
    actual_region = (
        honest_region(
            setup, source, polynomial_part, tuple(log_arguments)
        )
        if region is None
        else region
    )
    claim = has_rational_log_antiderivative(
        setup.vocabulary,
        actual_region.term,
        source,
        variable(setup),
        polynomial_part,
        log_terms,
        actual_result,
    )
    proposition = proposition_in(
        setup.runtime.frames,
        setup.frame,
        setup.signature,
        claim,
    )
    certificate = RationalLogAntiderivativeCertificate(
        actual_region.term,
        source,
        setup.runtime.variable,
        polynomial_part,
        log_terms,
        actual_result,
    )
    fixed_problem = (
        make_problem(setup, source) if problem is None else problem
    )
    return LogBundle(
        proposition,
        source,
        polynomial_part,
        log_terms,
        actual_result,
        actual_region.term,
        certificate,
        fixed_problem,
    )


def search_bundle(
    setup: LogSetup, value: RationalFunction[Fraction]
) -> LogBundle:
    """Build the honest low-level search result as a claim and certificate."""
    result = rational_log_integral(setup.bridge.field, value)
    entries = tuple(
        (term.coefficient, term.argument) for term in result.log_terms
    )
    return make_bundle(
        setup,
        source_value=value,
        polynomial_part_value=result.polynomial_part,
        entries=entries,
    )


def check_bundle(
    setup: LogSetup,
    bundle: LogBundle,
    *,
    candidate: T.Term | None | object = _DEFAULT,
    role: CandidateRole | None = CandidateRole.RESULT,
    problem: ProblemSpec | None | object = _DEFAULT,
    certificate: object = _DEFAULT,
    structured: object = _DEFAULT,
    context: object = _DEFAULT,
    conclusions: tuple[Proposition, ...] | None = None,
    checker_override: LogarithmicIntegrationChecker | None = None,
) -> CheckOutcome:
    runtime = setup.runtime
    actual_candidate = (
        bundle.result if candidate is _DEFAULT else candidate
    )
    actual_problem = (
        bundle.problem if problem is _DEFAULT else problem
    )
    actual_certificate = (
        bundle.certificate if certificate is _DEFAULT else certificate
    )
    actual_structured = (
        (
            ("polynomial_part", bundle.polynomial_part),
            ("log_terms", bundle.log_terms),
        )
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
    actual_checker = (
        checker(setup) if checker_override is None else checker_override
    )
    actual_conclusions = (
        (bundle.proposition,) if conclusions is None else conclusions
    )
    return actual_checker.check(
        CheckRequest(
            setup.frame,
            actual_conclusions,
            (),
            actual_certificate,
            problem=actual_problem,  # type: ignore[arg-type]
            candidate=actual_candidate,  # type: ignore[arg-type]
            candidate_role=role,
            context=actual_context,  # type: ignore[arg-type]
            structured=actual_structured,  # type: ignore[arg-type]
        )
    )
