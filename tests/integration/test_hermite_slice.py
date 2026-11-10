"""Hermite reduction through the workflow and its independent checker."""

from dataclasses import replace
from fractions import Fraction

from support import (
    head_app,
    runtime_proposition,
    variable,
    verification_context,
    view_of,
)

from cas.frontend.session import Session
from cas.kernel.evidence import (
    AlgebraService,
    CheckRequest,
    DecisionService,
    DefinednessService,
    InvalidEvidence,
    Refuted,
    Unverified,
    VerificationContext,
    Verified,
)
from cas.language import sorts as S
from cas.language.decisions import Reason
from cas.language.execution import ConditionPolicy, ExecutionBudget
from cas.language.problems import ResultLanguage
from cas.language.roles import CandidateRole
from cas.language.signatures import StructuralHead
from cas.language.typing import FreeSymbol
from cas.math.calculus.integration.hermite_checker import HermiteChecker
from cas.math.calculus.integration.hermite_operation import (
    HermiteReductionOperation,
)
from cas.math.calculus.integration.hermite_specification import (
    HermiteCertificate,
    HermiteVocabulary,
    has_hermite_reduction,
    parse_hermite_reduction,
)
from cas.operations.protocols import (
    ExecutionRequest,
    OperationRequest,
    ProblemBuilt,
    Proposed,
)
from cas.runtime import bootstrap, bootstrap_elementary, new_workspace
from cas.semantics.bridge import (
    RationalFunctionBridge,
    ViewBuilt,
    _build_view,
)
from cas.semantics.request import Interpretation
from cas.syntax import term as T
from cas.workflow.records import OperationStatus, TaskState


def vocab(runtime):
    return HermiteVocabulary(
        runtime.table.intern("HasHermiteReduction"),
        "HasHermiteReduction",
    )


def checker(runtime) -> HermiteChecker[Fraction]:
    found = runtime.store.checkers.get("calculus.hermite")
    assert isinstance(found, HermiteChecker)
    return found


def rational_bridge(runtime) -> RationalFunctionBridge[Fraction]:
    return checker(runtime).bridge


def rational_view(runtime, term):
    return view_of(runtime, term, bridge=rational_bridge(runtime))


def power(runtime, base, exponent):
    return head_app(
        runtime.signature, StructuralHead.POWER, base, T.number(exponent)
    )


def denominator_region(runtime, denominator: T.Term):
    return head_app(
        runtime.signature, StructuralHead.NE, denominator, T.number(0)
    )


def test_one_over_x_squared_verifies_regionally():
    runtime = bootstrap()
    workspace = new_workspace(runtime)
    x = variable(runtime)
    source = workspace.intake(power(runtime, x, -2), "1/x^2")
    result = workspace.hermite_reduce(source, runtime.variable)
    expected = denominator_region(runtime, power(runtime, x, 2))
    # The result is proved on the source's own denominator-nonzero region, so
    # the workflow records it as conditional rather than globally verified.
    assert result.status is OperationStatus.CONDITIONAL
    assert result.result is not None
    assert result.region is not None
    assert result.region.term == expected
    assert result.blocker is None
    assert result.candidate is not None
    claim = parse_hermite_reduction(
        vocab(runtime), result.candidate.specifications[0].term
    )
    assert claim is not None
    assert claim.region == expected
    assert claim.source == source.term
    assert claim.remainder == T.number(0)
    assert result.verifications[0].condition == result.region
    assert result.verifications[0].status is OperationStatus.VERIFIED
    view = rational_view(runtime, source.term)
    assert view.valid_on is not None
    assert view.witness.preserves_definedness is True


def test_a_total_source_is_verified_and_structured():
    runtime = bootstrap()
    workspace = new_workspace(runtime)
    x = variable(runtime)
    source = workspace.intake(power(runtime, x, 2), "x^2")
    result = workspace.hermite_reduce(source, runtime.variable)
    assert result.status is OperationStatus.VERIFIED
    assert result.region is None
    assert result.result is not None
    assert result.result.term == source.term
    assert result.structured is not None
    assert result.structured.kind == "HermiteReduction"
    assert [name for name, _ in result.structured.components] == [
        "polynomial_part",
        "remainder",
    ]
    claim = parse_hermite_reduction(
        vocab(runtime), result.verifications[0].specification.term
    )
    assert claim is not None
    assert claim.region == T.TRUE
    assert claim.source == source.term
    assert claim.remainder == source.term
    field = rational_bridge(runtime).field
    polynomial_part = rational_view(runtime, claim.polynomial_part).value
    remainder = rational_view(runtime, claim.remainder).value
    original = rational_view(runtime, source.term).value
    assert field.equal(
        field.add(field.derivative(polynomial_part), remainder), original
    )
    assert workspace.structured_result(result.result) is result.structured
    assert workspace.undo()
    assert workspace.structured_result(result.result) is None
    assert workspace.redo()
    assert workspace.structured_result(result.result) is result.structured
    assert result.candidate is not None
    assert (
        result.candidate.problem.result_language
        is ResultLanguage.DECOMPOSITION
    )


def test_a_mixed_denominator_candidate_keeps_a_squarefree_remainder():
    runtime = bootstrap()
    workspace = new_workspace(runtime)
    x = variable(runtime)
    denominator = head_app(
        runtime.signature,
        StructuralHead.TIMES,
        power(runtime, x, -1),
        power(
            runtime,
            head_app(
                runtime.signature, StructuralHead.PLUS, x, T.number(1)
            ),
            -2,
        ),
    )
    source = workspace.intake(denominator, "1/(x*(x+1)^2)")
    result = workspace.hermite_reduce(source, runtime.variable)
    assert result.status is OperationStatus.CONDITIONAL
    assert result.result is not None
    assert result.region is not None
    assert result.candidate is not None
    claim = parse_hermite_reduction(
        vocab(runtime), result.candidate.specifications[0].term
    )
    assert claim is not None
    field = rational_bridge(runtime).field
    original = rational_view(runtime, source.term).value
    polynomial_part = rational_view(runtime, claim.polynomial_part).value
    remainder = rational_view(runtime, claim.remainder).value
    assert field.equal(
        field.add(field.derivative(polynomial_part), remainder), original
    )
    denominator = remainder.denominator
    assert field.polynomials.is_one(
        field.polynomials.gcd(
            denominator, field.polynomials.derivative(denominator, 0)
        )
    )


def test_the_session_exposes_the_hermite_command():
    session = Session(bootstrap())
    session.execute("x^2")
    output = session.execute("hermite")
    assert output.startswith("verified @E1:")


def test_the_session_reports_a_regional_hermite_on_its_region():
    session = Session(bootstrap())
    session.execute("1/x^2")
    output = session.execute("hermite")
    assert output.startswith("verified on ")
    assert "x^2 != 0" in output
    assert "condition:" in output


def test_a_non_rational_source_is_refused():
    runtime = bootstrap_elementary()
    workspace = new_workspace(runtime)
    source = workspace.intake(
        head_app(
            runtime.signature,
            StructuralHead.POWER,
            T.symbol(runtime.table.intern("x"), "x"),
            T.number(-1),
        ),
        "1/x",
    )
    # 1/x is rational and its denominator region is verified.
    accepted = workspace.hermite_reduce(source, runtime.variable)
    assert accepted.status is OperationStatus.CONDITIONAL
    sine = runtime.table.intern("sin")
    source = workspace.intake(T.app(T.symbol(sine, "sin"), variable(runtime)))
    before = runtime.store.stats()
    refused = workspace.hermite_reduce(source, runtime.variable)
    assert refused.status is OperationStatus.UNSUPPORTED
    assert runtime.store.stats() == before


def test_the_checker_refutes_a_false_decomposition():
    runtime = bootstrap()
    x = variable(runtime)
    source = power(runtime, x, 2)
    wrong_remainder = x
    polynomial_part = T.number(0)
    conclusion = runtime_proposition(
        runtime,
        has_hermite_reduction(
            vocab(runtime),
            T.TRUE,
            source,
            x,
            polynomial_part,
            wrong_remainder,
        ),
    )
    certificate = HermiteCertificate(
        T.TRUE, source, runtime.variable, polynomial_part, wrong_remainder
    )
    outcome = checker(runtime).check(
        CheckRequest(
            runtime.frame.id,
            (conclusion,),
            (),
            certificate,
            candidate=wrong_remainder,
            candidate_role=CandidateRole.REMAINDER,
            context=verification_context(runtime, algebra=runtime.request),
        )
    )
    assert isinstance(outcome, Refuted)


def test_the_checker_refuses_a_mismatched_structured_result():
    runtime = bootstrap()
    x = variable(runtime)
    source = power(runtime, x, 2)
    polynomial_part = T.number(0)
    remainder = source
    conclusion = runtime_proposition(
        runtime,
        has_hermite_reduction(
            vocab(runtime),
            T.TRUE,
            source,
            x,
            polynomial_part,
            remainder,
        ),
    )
    certificate = HermiteCertificate(
        T.TRUE, source, runtime.variable, polynomial_part, remainder
    )
    outcome = checker(runtime).check(
        CheckRequest(
            runtime.frame.id,
            (conclusion,),
            (),
            certificate,
            candidate=remainder,
            candidate_role=CandidateRole.REMAINDER,
            context=verification_context(runtime, algebra=runtime.request),
            structured=(("polynomial_part", polynomial_part), ("remainder", x)),
        )
    )
    assert isinstance(outcome, InvalidEvidence)


def test_the_checker_verifies_a_non_total_region():
    runtime = bootstrap()
    x = variable(runtime)
    source = power(runtime, x, -2)
    region = denominator_region(runtime, power(runtime, x, 2))
    polynomial_part = head_app(
        runtime.signature,
        StructuralHead.TIMES,
        T.number(-1),
        power(runtime, x, -1),
    )
    remainder = T.number(0)
    conclusion = runtime_proposition(
        runtime,
        has_hermite_reduction(
            vocab(runtime),
            region,
            source,
            x,
            polynomial_part,
            remainder,
        ),
    )
    certificate = HermiteCertificate(
        region, source, runtime.variable, polynomial_part, remainder
    )
    outcome = checker(runtime).check(
        CheckRequest(
            runtime.frame.id,
            (conclusion,),
            (),
            certificate,
            candidate=remainder,
            candidate_role=CandidateRole.REMAINDER,
            context=verification_context(runtime, algebra=runtime.request),
        )
    )
    assert isinstance(outcome, Verified)


def test_the_checker_verifies_one_over_x_regionally():
    runtime = bootstrap()
    x = variable(runtime)
    source = power(runtime, x, -1)
    region = denominator_region(runtime, x)
    polynomial_part = T.number(0)
    remainder = source
    conclusion = runtime_proposition(
        runtime,
        has_hermite_reduction(
            vocab(runtime),
            region,
            source,
            x,
            polynomial_part,
            remainder,
        ),
    )
    certificate = HermiteCertificate(
        region, source, runtime.variable, polynomial_part, remainder
    )
    outcome = checker(runtime).check(
        CheckRequest(
            runtime.frame.id,
            (conclusion,),
            (),
            certificate,
            candidate=remainder,
            candidate_role=CandidateRole.REMAINDER,
            context=verification_context(runtime, algebra=runtime.request),
        )
    )
    assert isinstance(outcome, Verified)


def test_the_checker_verifies_a_restricted_claim_on_a_total_source():
    runtime = bootstrap()
    x = variable(runtime)
    source = power(runtime, x, 2)
    region = greater_than(runtime, 0)
    polynomial_part = head_app(
        runtime.signature,
        StructuralHead.TIMES,
        T.number(Fraction(1, 3)),
        power(runtime, x, 3),
    )
    remainder = T.number(0)
    conclusion = runtime_proposition(
        runtime,
        has_hermite_reduction(
            vocab(runtime),
            region.term,
            source,
            x,
            polynomial_part,
            remainder,
        ),
    )
    certificate = HermiteCertificate(
        region.term, source, runtime.variable, polynomial_part, remainder
    )
    outcome = checker(runtime).check(
        CheckRequest(
            runtime.frame.id,
            (conclusion,),
            (),
            certificate,
            candidate=remainder,
            candidate_role=CandidateRole.REMAINDER,
            context=verification_context(runtime, algebra=runtime.request),
        )
    )
    assert isinstance(outcome, Verified)


def test_a_non_total_source_does_not_support_a_global_claim():
    runtime = bootstrap()
    x = variable(runtime)
    source = power(runtime, x, -2)
    polynomial_part = head_app(
        runtime.signature,
        StructuralHead.TIMES,
        T.number(-1),
        power(runtime, x, -1),
    )
    remainder = T.number(0)
    conclusion = runtime_proposition(
        runtime,
        has_hermite_reduction(
            vocab(runtime),
            T.TRUE,
            source,
            x,
            polynomial_part,
            remainder,
        ),
    )
    certificate = HermiteCertificate(
        T.TRUE, source, runtime.variable, polynomial_part, remainder
    )
    outcome = checker(runtime).check(
        CheckRequest(
            runtime.frame.id,
            (conclusion,),
            (),
            certificate,
            candidate=remainder,
            candidate_role=CandidateRole.REMAINDER,
            context=verification_context(runtime, algebra=runtime.request),
        )
    )
    assert isinstance(outcome, Unverified)
    assert outcome.reason is Reason.GUARDED
    assert "regional_hermite" in outcome.missing
    assert {condition.term for condition in outcome.conditions} == {
        denominator_region(runtime, power(runtime, x, 2))
    }


def test_a_claimed_part_outside_the_source_denominator_is_not_verified():
    runtime = bootstrap()
    x = variable(runtime)
    source = power(runtime, x, -1)
    region = denominator_region(runtime, x)
    one_plus_x = head_app(
        runtime.signature, StructuralHead.PLUS, x, T.number(1)
    )
    polynomial_part = power(runtime, one_plus_x, -1)
    remainder = head_app(
        runtime.signature,
        StructuralHead.PLUS,
        power(runtime, x, -1),
        power(runtime, one_plus_x, -2),
    )
    conclusion = runtime_proposition(
        runtime,
        has_hermite_reduction(
            vocab(runtime),
            region,
            source,
            x,
            polynomial_part,
            remainder,
        ),
    )
    certificate = HermiteCertificate(
        region, source, runtime.variable, polynomial_part, remainder
    )
    outcome = checker(runtime).check(
        CheckRequest(
            runtime.frame.id,
            (conclusion,),
            (),
            certificate,
            candidate=remainder,
            candidate_role=CandidateRole.REMAINDER,
            context=verification_context(runtime, algebra=runtime.request),
        )
    )
    assert isinstance(outcome, Unverified)
    assert outcome.reason is Reason.GUARDED
    assert "regional_hermite_denominator" in outcome.missing
    assert "polynomial part" in outcome.detail
    assert "does not divide the source denominator" in outcome.detail


def test_a_cancelled_hole_in_a_claimed_part_is_not_verified():
    runtime = bootstrap()
    x = variable(runtime)
    source = power(runtime, x, -2)
    region = denominator_region(runtime, power(runtime, x, 2))
    one_plus_x = head_app(
        runtime.signature, StructuralHead.PLUS, x, T.number(1)
    )
    # Formally -1/x, but the source expression is undefined at x = -1.
    polynomial_part = head_app(
        runtime.signature,
        StructuralHead.TIMES,
        head_app(
            runtime.signature,
            StructuralHead.TIMES,
            one_plus_x,
            power(runtime, one_plus_x, -1),
        ),
        head_app(
            runtime.signature,
            StructuralHead.TIMES,
            T.number(-1),
            power(runtime, x, -1),
        ),
    )
    remainder = T.number(0)
    conclusion = runtime_proposition(
        runtime,
        has_hermite_reduction(
            vocab(runtime),
            region,
            source,
            x,
            polynomial_part,
            remainder,
        ),
    )
    certificate = HermiteCertificate(
        region, source, runtime.variable, polynomial_part, remainder
    )
    outcome = checker(runtime).check(
        CheckRequest(
            runtime.frame.id,
            (conclusion,),
            (),
            certificate,
            candidate=remainder,
            candidate_role=CandidateRole.REMAINDER,
            context=verification_context(runtime, algebra=runtime.request),
        )
    )
    assert isinstance(outcome, Unverified)
    assert outcome.reason is Reason.GUARDED
    assert "regional_hermite_denominator" in outcome.missing
    assert "polynomial part" in outcome.detail


def test_a_global_mismatch_does_not_refute_a_restricted_claim():
    runtime = bootstrap()
    x = variable(runtime)
    source = power(runtime, x, 2)
    region = greater_than(runtime, 0)
    conclusion = runtime_proposition(
        runtime,
        has_hermite_reduction(
            vocab(runtime),
            region.term,
            source,
            x,
            T.number(0),
            x,
        ),
    )
    certificate = HermiteCertificate(
        region.term, source, runtime.variable, T.number(0), x
    )
    outcome = checker(runtime).check(
        CheckRequest(
            runtime.frame.id,
            (conclusion,),
            (),
            certificate,
            candidate=x,
            candidate_role=CandidateRole.REMAINDER,
            context=verification_context(runtime, algebra=runtime.request),
        )
    )
    assert isinstance(outcome, Unverified)
    assert outcome.reason is Reason.FRAGMENT
    assert "regional_hermite_identity" in outcome.missing


def test_undefined_zero_powers_are_refused_without_writing():
    runtime = bootstrap()
    workspace = new_workspace(runtime)
    x = variable(runtime)

    for label, term in (
        ("x^0", power(runtime, x, 0)),
        ("0^0", power(runtime, T.number(0), 0)),
        ("0^-1", power(runtime, T.number(0), -1)),
    ):
        source = workspace.intake(term, label)
        before_stats = runtime.store.stats()
        before_events = len(workspace.events())
        result = workspace.hermite_reduce(source, runtime.variable)
        assert result.status is OperationStatus.UNSUPPORTED
        assert result.result is None
        assert result.task is not None
        assert result.task.state is TaskState.BLOCKED
        assert runtime.store.stats() == before_stats
        assert len(workspace.events()) == before_events + 1


def test_the_checker_refuses_undefined_zero_powers():
    runtime = bootstrap()
    x = variable(runtime)

    for source in (
        power(runtime, x, 0),
        power(runtime, T.number(0), 0),
        power(runtime, T.number(0), -1),
    ):
        conclusion = runtime_proposition(
            runtime,
            has_hermite_reduction(
                vocab(runtime),
                T.TRUE,
                source,
                x,
                T.number(0),
                T.number(1),
            ),
        )
        certificate = HermiteCertificate(
            T.TRUE, source, runtime.variable, T.number(0), T.number(1)
        )
        outcome = checker(runtime).check(
            CheckRequest(
                runtime.frame.id,
                (conclusion,),
                (),
                certificate,
                candidate=T.number(1),
                candidate_role=CandidateRole.REMAINDER,
                context=verification_context(runtime, algebra=runtime.request),
            )
        )
        assert isinstance(outcome, Unverified)


def test_the_checker_refutes_a_non_squarefree_remainder():
    runtime = bootstrap()
    x = variable(runtime)
    denominator = head_app(
        runtime.signature, StructuralHead.PLUS, x, T.number(1)
    )
    source = T.number(0)
    polynomial_part = power(runtime, denominator, -1)
    remainder = power(runtime, denominator, -2)
    conclusion = runtime_proposition(
        runtime,
        has_hermite_reduction(
            vocab(runtime),
            T.TRUE,
            source,
            x,
            polynomial_part,
            remainder,
        ),
    )
    certificate = HermiteCertificate(
        T.TRUE, source, runtime.variable, polynomial_part, remainder
    )
    outcome = checker(runtime).check(
        CheckRequest(
            runtime.frame.id,
            (conclusion,),
            (),
            certificate,
            candidate=remainder,
            candidate_role=CandidateRole.REMAINDER,
            context=verification_context(runtime, algebra=runtime.request),
        )
    )
    assert isinstance(outcome, Refuted)
    assert "squarefree" in outcome.detail


def test_the_checker_accepts_a_true_decomposition():
    runtime = bootstrap()
    x = variable(runtime)
    source = power(runtime, x, 2)
    polynomial_part = head_app(
        runtime.signature,
        StructuralHead.TIMES,
        T.number(Fraction(1, 3)),
        power(runtime, x, 3),
    )
    remainder = T.number(0)
    conclusion = runtime_proposition(
        runtime,
        has_hermite_reduction(
            vocab(runtime),
            T.TRUE,
            source,
            x,
            polynomial_part,
            remainder,
        ),
    )
    certificate = HermiteCertificate(
        T.TRUE, source, runtime.variable, polynomial_part, remainder
    )
    outcome = checker(runtime).check(
        CheckRequest(
            runtime.frame.id,
            (conclusion,),
            (),
            certificate,
            candidate=remainder,
            candidate_role=CandidateRole.REMAINDER,
            context=verification_context(runtime, algebra=runtime.request),
        )
    )
    assert isinstance(outcome, Verified)


def test_the_checker_requires_the_candidate_role():
    runtime = bootstrap()
    x = variable(runtime)
    source = power(runtime, x, -2)
    polynomial_part = head_app(
        runtime.signature,
        StructuralHead.TIMES,
        T.number(-1),
        power(runtime, x, -1),
    )
    remainder = T.number(0)
    conclusion = runtime_proposition(
        runtime,
        has_hermite_reduction(
            vocab(runtime),
            T.TRUE,
            source,
            x,
            polynomial_part,
            remainder,
        ),
    )
    certificate = HermiteCertificate(
        T.TRUE, source, runtime.variable, polynomial_part, remainder
    )
    for role in (None, CandidateRole.RESULT):
        outcome = checker(runtime).check(
            CheckRequest(
                runtime.frame.id,
                (conclusion,),
                (),
                certificate,
                candidate=remainder,
                candidate_role=role,
                context=verification_context(runtime, algebra=runtime.request),
            )
        )
        assert isinstance(outcome, InvalidEvidence)
        assert "candidate role" in outcome.detail
    for candidate in (None, polynomial_part):
        outcome = checker(runtime).check(
            CheckRequest(
                runtime.frame.id,
                (conclusion,),
                (),
                certificate,
                candidate=candidate,
                candidate_role=CandidateRole.REMAINDER,
                context=verification_context(runtime, algebra=runtime.request),
            )
        )
        assert isinstance(outcome, InvalidEvidence)
        assert "candidate" in outcome.detail


class RegionalBridge:
    """A test bridge that issues a view with explicit source regions.

    The production rational bridge sets `source_domain == valid_on`; this
    wrapper lets a test state them independently without bypassing the view
    seal (it replaces fields on a view the bridge itself issued).
    """

    def __init__(self, bridge, source_domain, valid_on):
        self._bridge = bridge
        self.field = bridge.field
        self.parent = bridge.parent
        self.world = bridge.world
        self.signature = bridge.signature
        self.frames = bridge.frames
        self.name_of = bridge.name_of
        self.render_coefficient = bridge.render_coefficient
        self.source_domain = source_domain
        self.valid_on = valid_on

    def to_view(self, source, request):
        outcome = self._bridge.to_view(source, request)
        if isinstance(outcome, ViewBuilt):
            view = outcome.view
            return ViewBuilt(
                _build_view(
                    view.source,
                    view.parent,
                    view.value,
                    view.symbols,
                    view.interpretation,
                    view.witness,
                    self.source_domain,
                    self.valid_on,
                    signature=self.signature,
                    region_bindings=(
                        FreeSymbol(
                            self._bridge.field.polynomials.generators[0],
                            S.REAL,
                        ),
                    ),
                )
            )
        return outcome

    def render(self, view, value):
        return self._bridge.render(view, value)


def greater_than(runtime, bound):
    return runtime_proposition(
        runtime,
        head_app(
            runtime.signature,
            StructuralHead.GT,
            variable(runtime),
            T.number(bound),
        ),
    )


def regional_checker(runtime, source_domain, valid_on):
    return replace(
        checker(runtime),
        bridge=RegionalBridge(
            rational_bridge(runtime), source_domain, valid_on
        ),
    )


def hermite_claim(runtime, source, polynomial_part, remainder):
    return runtime_proposition(
        runtime,
        has_hermite_reduction(
            vocab(runtime),
            T.TRUE,
            source,
            variable(runtime),
            polynomial_part,
            remainder,
        ),
    )


def test_the_operation_carries_the_intrinsic_domain_and_valid_on():
    runtime = bootstrap()
    workspace = new_workspace(runtime)
    x = variable(runtime)
    source = workspace.intake(power(runtime, x, 2), "x^2")
    found = runtime.operations.get("hermite_reduce")
    assert isinstance(found, HermiteReductionOperation)
    view = found.views[0]
    domain = greater_than(runtime, 1)
    valid_on = greater_than(runtime, 0)
    regional_view = replace(
        view,
        bridge=RegionalBridge(view.bridge, domain, valid_on),
    )
    operation = replace(found, views=(regional_view,))
    request = OperationRequest(
        runtime.frame.id, (source.term,), target=runtime.variable
    )
    problem_outcome = operation.build_problem(request)
    assert isinstance(problem_outcome, ProblemBuilt)
    execution = ExecutionRequest(
        request,
        problem_outcome.problem,
        problem_outcome.algebra,
        request.frame,
        ConditionPolicy.REQUIRE_PROVED,
        ExecutionBudget(),
    )
    proposal_outcome = operation.propose(execution)
    assert isinstance(proposal_outcome, Proposed)
    proposal = proposal_outcome.proposal
    claim = parse_hermite_reduction(
        vocab(runtime), proposal.specifications[0].term
    )
    assert claim is not None
    assert claim.region == domain.term
    certificate = proposal.certificate
    assert isinstance(certificate, HermiteCertificate)
    assert certificate.region == domain.term
    assert proposal.result_region is not None
    assert proposal.result_region.term == domain.term


def test_the_checker_refuses_a_valid_on_outside_the_source_domain():
    runtime = bootstrap()
    x = variable(runtime)
    source = power(runtime, x, 2)
    conclusion = hermite_claim(runtime, source, T.number(0), source)
    certificate = HermiteCertificate(
        T.TRUE, source, runtime.variable, T.number(0), source
    )
    domain = greater_than(runtime, 0)
    valid_on = runtime_proposition(
        runtime,
        head_app(
            runtime.signature,
            StructuralHead.NE,
            x,
            T.number(0),
        ),
    )
    outcome = regional_checker(runtime, domain, valid_on).check(
        CheckRequest(
            runtime.frame.id,
            (conclusion,),
            (),
            certificate,
            candidate=source,
            candidate_role=CandidateRole.REMAINDER,
            context=verification_context(runtime, algebra=runtime.request),
        )
    )
    assert isinstance(outcome, InvalidEvidence)
    assert "source domain" in outcome.detail


def test_the_checker_reports_both_non_total_source_regions():
    runtime = bootstrap()
    x = variable(runtime)
    source = power(runtime, x, 2)
    conclusion = hermite_claim(runtime, source, T.number(0), source)
    certificate = HermiteCertificate(
        T.TRUE, source, runtime.variable, T.number(0), source
    )
    domain = greater_than(runtime, 0)
    valid_on = greater_than(runtime, 1)
    outcome = regional_checker(runtime, domain, valid_on).check(
        CheckRequest(
            runtime.frame.id,
            (conclusion,),
            (),
            certificate,
            candidate=source,
            candidate_role=CandidateRole.REMAINDER,
            context=verification_context(runtime, algebra=runtime.request),
        )
    )
    assert isinstance(outcome, Unverified)
    assert outcome.reason is Reason.GUARDED
    assert {condition.term for condition in outcome.conditions} == {
        domain.term,
        valid_on.term,
    }


class RefusingDecision(DecisionService):
    """A decision service that never proves a region inclusion."""

    def is_subregion(
        self, subregion: T.Term, region: T.Term
    ) -> bool | None:
        del subregion, region
        return None


def test_the_checker_uses_the_context_decision_service():
    runtime = bootstrap()
    x = variable(runtime)
    source = power(runtime, x, 2)
    region = greater_than(runtime, 0)
    polynomial_part = head_app(
        runtime.signature,
        StructuralHead.TIMES,
        T.number(Fraction(1, 3)),
        power(runtime, x, 3),
    )
    remainder = T.number(0)
    conclusion = runtime_proposition(
        runtime,
        has_hermite_reduction(
            vocab(runtime),
            region.term,
            source,
            x,
            polynomial_part,
            remainder,
        ),
    )
    certificate = HermiteCertificate(
        region.term, source, runtime.variable, polynomial_part, remainder
    )

    def request_with(decision):
        return CheckRequest(
            runtime.frame.id,
            (conclusion,),
            (),
            certificate,
            candidate=remainder,
            candidate_role=CandidateRole.REMAINDER,
            context=VerificationContext(
                runtime.world.id,
                runtime.frame.id,
                runtime.frames,
                decision=decision,
                algebra=AlgebraService(runtime.request),
            ),
        )

    verified = regional_checker(runtime, region, None).check(
        request_with(DecisionService(runtime.signature))
    )
    assert isinstance(verified, Verified)

    guarded = regional_checker(runtime, region, None).check(
        request_with(RefusingDecision(runtime.signature))
    )
    assert isinstance(guarded, Unverified)
    assert guarded.reason is Reason.GUARDED
    assert "region_coverage" in guarded.missing
    assert {condition.term for condition in guarded.conditions} == {
        region.term
    }


def test_the_checker_uses_the_context_definedness_service():
    runtime = bootstrap()
    x = variable(runtime)
    source = power(runtime, x, 2)
    region = greater_than(runtime, 0)
    polynomial_part = head_app(
        runtime.signature,
        StructuralHead.TIMES,
        T.number(Fraction(1, 3)),
        power(runtime, x, 3),
    )
    remainder = T.number(0)
    conclusion = runtime_proposition(
        runtime,
        has_hermite_reduction(
            vocab(runtime),
            region.term,
            source,
            x,
            polynomial_part,
            remainder,
        ),
    )
    certificate = HermiteCertificate(
        region.term, source, runtime.variable, polynomial_part, remainder
    )

    def request_with(definedness):
        return CheckRequest(
            runtime.frame.id,
            (conclusion,),
            (),
            certificate,
            candidate=remainder,
            candidate_role=CandidateRole.REMAINDER,
            context=VerificationContext(
                runtime.world.id,
                runtime.frame.id,
                runtime.frames,
                decision=DecisionService(runtime.signature),
                definedness=definedness,
                algebra=AlgebraService(runtime.request),
            ),
        )

    verified = regional_checker(runtime, region, None).check(
        request_with(
            DefinednessService(
                DecisionService(runtime.signature),
                runtime.frames,
                runtime.frame.id,
            )
        )
    )
    assert isinstance(verified, Verified)

    guarded = regional_checker(runtime, region, None).check(
        request_with(
            DefinednessService(
                RefusingDecision(runtime.signature),
                runtime.frames,
                runtime.frame.id,
            )
        )
    )
    assert isinstance(guarded, Unverified)
    assert guarded.reason is Reason.GUARDED
    assert "region_coverage" in guarded.missing
    assert {condition.term for condition in guarded.conditions} == {
        region.term
    }


def test_the_definedness_service_covers_the_source_domain_region():
    runtime = bootstrap()
    x = variable(runtime)
    source = power(runtime, x, 2)
    region = greater_than(runtime, 0)
    conclusion = runtime_proposition(
        runtime,
        has_hermite_reduction(
            vocab(runtime),
            region.term,
            source,
            x,
            T.number(0),
            source,
        ),
    )
    certificate = HermiteCertificate(
        region.term, source, runtime.variable, T.number(0), source
    )
    # The context decision refuses every inclusion; only the definedness
    # service can prove that the validity region lies inside the domain.
    context = VerificationContext(
        runtime.world.id,
        runtime.frame.id,
        runtime.frames,
        decision=RefusingDecision(runtime.signature),
        definedness=DefinednessService(
            DecisionService(runtime.signature),
            runtime.frames,
            runtime.frame.id,
        ),
        algebra=AlgebraService(runtime.request),
    )
    outcome = regional_checker(runtime, region, region).check(
        CheckRequest(
            runtime.frame.id,
            (conclusion,),
            (),
            certificate,
            candidate=source,
            candidate_role=CandidateRole.REMAINDER,
            context=context,
        )
    )
    assert isinstance(outcome, Verified)


def test_the_checker_requires_the_context_algebra_request():
    runtime = bootstrap()
    x = variable(runtime)
    source = power(runtime, x, 2)
    polynomial_part = head_app(
        runtime.signature,
        StructuralHead.TIMES,
        T.number(Fraction(1, 3)),
        power(runtime, x, 3),
    )
    remainder = T.number(0)
    conclusion = runtime_proposition(
        runtime,
        has_hermite_reduction(
            vocab(runtime),
            T.TRUE,
            source,
            x,
            polynomial_part,
            remainder,
        ),
    )
    certificate = HermiteCertificate(
        T.TRUE, source, runtime.variable, polynomial_part, remainder
    )

    def request_with(algebra):
        return CheckRequest(
            runtime.frame.id,
            (conclusion,),
            (),
            certificate,
            candidate=remainder,
            candidate_role=CandidateRole.REMAINDER,
            context=VerificationContext(
                runtime.world.id,
                runtime.frame.id,
                runtime.frames,
                algebra=algebra,
            ),
        )

    matching = AlgebraService(checker(runtime).request)
    verified = checker(runtime).check(request_with(matching))
    assert isinstance(verified, Verified)

    mismatched = AlgebraService(
        replace(
            checker(runtime).request,
            interpretation=Interpretation.EMBEDDED,
        )
    )
    refused = checker(runtime).check(request_with(mismatched))
    assert isinstance(refused, InvalidEvidence)
    assert "algebra" in refused.detail
