"""Checker protocol, outcomes and the frozen checker registry."""

from collections.abc import Callable
from dataclasses import replace
from typing import cast

import pytest
from support import (
    equation,
    head_app,
    runtime_proposition,
    typed_in,
    variable,
    verification_context,
)

from cas.foundation.ids import (
    FrameId,
    InferenceId,
    JudgmentId,
    ObligationId,
    WorldId,
)
from cas.kernel.evidence import (
    AlgebraService,
    BudgetService,
    CheckerRegistry,
    CheckerSpec,
    CheckRequest,
    DecisionService,
    DefinednessService,
    InvalidEvidence,
    ObligationReport,
    Refuted,
    SupportsService,
    Unverified,
    VerificationContext,
    Verified,
    context_algebra_mismatch,
    problem_mismatch,
)
from cas.kernel.model import InferenceRecord, Judgment, ObligationReason
from cas.kernel.trust import (
    AxiomRef,
    BasisKind,
    BasisRef,
    CertificateSchema,
)
from cas.language import sorts as S
from cas.language.decisions import Reason
from cas.language.execution import BudgetTicket, ExecutionBudget
from cas.language.problems import (
    Coverage,
    DomainRequirement,
    Exactness,
    InterpretationRequirement,
    ProblemSpec,
    ResultLanguage,
)
from cas.language.propositions import Proposition
from cas.language.roles import CandidateRole
from cas.language.signatures import LanguageSignature, StructuralHead
from cas.runtime.bootstrap import bootstrap
from cas.semantics import conditions
from cas.semantics.frames import FrameStore
from cas.semantics.request import AlgebraRequest
from cas.syntax import term as T


class GoodChecker:
    id = "test.good"
    version = "1"

    def check(self, request: CheckRequest) -> Verified:
        return Verified(tuple(request.conclusions))


class NoVersion(GoodChecker):
    version = ""


class RefusingDecision(DecisionService):
    """A decision service that never proves a region inclusion."""

    def is_subregion(
        self, subregion: T.Term, region: T.Term
    ) -> bool | None:
        del subregion, region
        return None


def spec(checker, *, deps=()):
    return CheckerSpec(
        checker,
        CertificateSchema("test", "1", type(None)),
        frozenset({"test.problem"}),
        frozenset({"test.specification"}),
        WorldId(0),
        deps,
    )


def basis(name="library"):
    return BasisRef(
        name, BasisKind.STANDARD_LIBRARY, "1", "digest", WorldId(0)
    )


def test_a_certificate_schema_enforces_a_structural_budget():
    schema = CertificateSchema(
        "test", "1", tuple, max_nodes=4, max_depth=3
    )
    assert schema.within_budget((1, 2))
    assert not schema.within_budget((1, 2, 3, 4, 5))
    deep = ((((1,),),),)
    assert schema.accepts(deep)
    assert not schema.within_budget(deep)


def test_a_certificate_budget_refuses_unmeasurable_or_cyclic_values():
    schema = CertificateSchema("test", "1", object)
    assert not schema.within_budget(object())
    cyclic: list[object] = []
    cyclic.append(cyclic)
    assert schema.accepts(cyclic)
    assert not schema.within_budget(cyclic)


def test_trust_records_validate_their_kinds():
    with pytest.raises(TypeError):
        BasisRef(
            "library",
            "standard_library",
            "1",
            "digest",
            WorldId(0),
        )
    with pytest.raises(TypeError):
        CheckerSpec(
            GoodChecker(),
            CertificateSchema("test", "1", type(None)),
            ["test.problem"],
            frozenset({"test.specification"}),
            WorldId(0),
        )


def test_check_outcomes_validate_their_payloads():
    with pytest.raises(TypeError):
        Verified((T.TRUE,))  # type: ignore[arg-type]
    with pytest.raises(TypeError):
        Refuted(T.TRUE, (T.number(1),), "not a proposition")  # type: ignore[arg-type]
    with pytest.raises(TypeError):
        Unverified("fragment", "detail")  # type: ignore[arg-type]
    with pytest.raises(TypeError):
        Unverified(Reason.FRAGMENT)  # type: ignore[call-arg]
    with pytest.raises(ValueError):
        Unverified(Reason.FRAGMENT, "")
    with pytest.raises(TypeError):
        Unverified(Reason.FRAGMENT, "detail", missing=frozenset({""}))
    with pytest.raises(TypeError):
        Unverified(
            Reason.FRAGMENT,
            "detail",
            conditions=(object(),),  # type: ignore[arg-type]
        )


def test_check_requests_and_obligation_reports_validate_their_data():
    assert CheckRequest(FrameId(0), (), (), None).conclusions == ()
    candidate = T.number(1)
    assert (
        CheckRequest(
            FrameId(0), (), (), None, candidate=candidate
        ).candidate
        is candidate
    )
    role_request = CheckRequest(
        FrameId(0),
        (),
        (),
        None,
        candidate=candidate,
        candidate_role=CandidateRole.RESULT,
    )
    assert role_request.candidate_role is CandidateRole.RESULT
    with pytest.raises(TypeError):
        CheckRequest(FrameId(0), (T.TRUE,), (), None)  # type: ignore[arg-type]
    with pytest.raises(TypeError):
        CheckRequest(
            FrameId(0),
            (),
            (),
            None,
            candidate=cast(T.Term, "not a term"),
        )
    with pytest.raises(TypeError):
        CheckRequest(
            FrameId(0),
            (),
            (),
            None,
            candidate_role="result",
        )
    with pytest.raises(TypeError):
        ObligationReport(T.TRUE, ObligationReason.DEFINEDNESS)  # type: ignore[arg-type]


def test_a_verification_context_fixes_world_frame_and_store(runtime):
    context = VerificationContext(
        runtime.world.id, runtime.frame.id, runtime.frames
    )
    assert context.world == runtime.world.id
    assert context.frame == runtime.frame.id
    assert context.frames is runtime.frames
    with pytest.raises(TypeError):
        VerificationContext(
            cast(WorldId, "world"), runtime.frame.id, runtime.frames
        )
    with pytest.raises(TypeError):
        VerificationContext(
            runtime.world.id, cast(FrameId, "frame"), runtime.frames
        )
    with pytest.raises(TypeError):
        VerificationContext(
            runtime.world.id,
            runtime.frame.id,
            cast(FrameStore, object()),
        )


def test_decision_service_agrees_with_the_condition_fragment(runtime):
    decision = DecisionService(runtime.signature)
    x = variable(runtime)
    positive = head_app(
        runtime.signature, StructuralHead.GT, x, T.number(0)
    )
    stronger = head_app(
        runtime.signature, StructuralHead.GT, x, T.number(1)
    )
    negative = head_app(
        runtime.signature, StructuralHead.LT, x, T.number(0)
    )
    contradiction = head_app(
        runtime.signature, StructuralHead.AND, positive, negative
    )
    for assumption, goal in (
        (stronger, positive),
        (positive, stronger),
        (positive, negative),
        (T.TRUE, T.FALSE),
    ):
        assert decision.implies(assumption, goal) is conditions.implies(
            assumption, goal, runtime.signature
        )
    assert decision.implies(stronger, positive) is True
    assert decision.implies(positive, stronger) is None
    assert decision.equivalent(positive, positive) is True
    assert decision.equivalent(positive, negative) is False
    assert decision.is_subregion(stronger, positive) is True
    assert decision.is_subregion(positive, stronger) is None
    assert decision.is_empty(contradiction) is True
    assert decision.is_empty(positive) is False


def test_a_verification_context_carries_and_validates_services(runtime):
    decision = DecisionService(runtime.signature)
    supports = SupportsService(
        runtime.store.get_judgment,
        runtime.store.judgments_visible,
        runtime.store.is_discharged,
    )
    budget = BudgetService(ExecutionBudget(max_nodes=4, max_depth=2))
    context = VerificationContext(
        runtime.world.id,
        runtime.frame.id,
        runtime.frames,
        decision=decision,
        supports=supports,
        budget=budget,
    )
    assert context.decision is decision
    assert context.supports is supports
    assert context.budget is budget
    assert context.readable(runtime_proposition(runtime, T.TRUE))
    other = bootstrap()
    assert not context.readable(runtime_proposition(other, T.TRUE))
    with pytest.raises(TypeError):
        VerificationContext(
            runtime.world.id,
            runtime.frame.id,
            runtime.frames,
            decision=cast(DecisionService, object()),
        )
    with pytest.raises(TypeError):
        VerificationContext(
            runtime.world.id,
            runtime.frame.id,
            runtime.frames,
            supports=cast(SupportsService, object()),
        )
    with pytest.raises(TypeError):
        VerificationContext(
            runtime.world.id,
            runtime.frame.id,
            runtime.frames,
            budget=cast(BudgetService, object()),
        )


def test_a_verification_context_carries_axioms_and_algebra(runtime):
    reference = replace(basis(), world=runtime.world.id)
    axiom = AxiomRef.from_basis(reference)
    algebra = AlgebraService(runtime.request)
    context = VerificationContext(
        runtime.world.id,
        runtime.frame.id,
        runtime.frames,
        axioms=(axiom,),
        algebra=algebra,
    )
    assert context.axioms == (axiom,)
    assert context.algebra is algebra

    with pytest.raises(TypeError):
        VerificationContext(
            runtime.world.id,
            runtime.frame.id,
            runtime.frames,
            axioms=(cast(AxiomRef, object()),),
        )
    foreign = AxiomRef.from_basis(
        replace(basis(), world=WorldId(runtime.world.id + 1))
    )
    with pytest.raises(ValueError):
        VerificationContext(
            runtime.world.id,
            runtime.frame.id,
            runtime.frames,
            axioms=(foreign,),
        )
    with pytest.raises(TypeError):
        VerificationContext(
            runtime.world.id,
            runtime.frame.id,
            runtime.frames,
            algebra=cast(AlgebraService, object()),
        )


def test_an_axiom_reference_records_one_admitted_basis(runtime):
    reference = replace(basis(), world=runtime.world.id)
    axiom = AxiomRef.from_basis(reference)
    assert axiom.name == reference.name
    assert axiom.version == reference.version
    assert axiom.digest == reference.digest
    assert axiom.world == reference.world
    with pytest.raises(ValueError):
        AxiomRef("", "1", "digest", WorldId(0))
    with pytest.raises(ValueError):
        AxiomRef("name", "", "digest", WorldId(0))
    with pytest.raises(ValueError):
        AxiomRef("name", "1", "", WorldId(0))
    with pytest.raises(TypeError):
        AxiomRef("name", "1", "digest", cast(WorldId, "world"))
    with pytest.raises(TypeError):
        AxiomRef.from_basis(cast(BasisRef, "basis"))


def test_an_algebra_service_needs_an_algebra_request(runtime):
    service = AlgebraService(runtime.request)
    assert service.request is runtime.request
    with pytest.raises(TypeError):
        AlgebraService(cast(AlgebraRequest, object()))


def test_context_algebra_mismatch_requires_the_same_fixed_request(runtime):
    bare = VerificationContext(
        runtime.world.id, runtime.frame.id, runtime.frames
    )
    assert context_algebra_mismatch(None, runtime.request) == (
        "the check request has no trusted verification context"
    )
    assert context_algebra_mismatch(bare, runtime.request) == (
        "the check request has no fixed algebra request"
    )
    fixed = VerificationContext(
        runtime.world.id,
        runtime.frame.id,
        runtime.frames,
        algebra=AlgebraService(runtime.request),
    )
    assert context_algebra_mismatch(fixed, runtime.request) is None
    same_fields = replace(runtime.request)
    assert same_fields is not runtime.request
    assert context_algebra_mismatch(fixed, same_fields) == (
        "the context algebra request does not match the checker request"
    )


def test_a_budget_service_carries_an_optional_ticket(runtime):
    budget = ExecutionBudget(max_nodes=4, max_depth=2)
    ticket = BudgetTicket(budget)
    service = BudgetService(budget, ticket)
    assert service.budget is budget
    assert service.ticket is ticket
    assert BudgetService(budget).ticket is None
    with pytest.raises(TypeError):
        BudgetService(budget, cast(BudgetTicket, "ticket"))


def test_context_services_validate_their_inputs(runtime):
    with pytest.raises(TypeError):
        DecisionService(cast(LanguageSignature, object()))
    with pytest.raises(TypeError):
        BudgetService(cast(ExecutionBudget, "small"))
    with pytest.raises(TypeError):
        SupportsService(
            cast(Callable[[JudgmentId], Judgment], "judgment"),
            runtime.store.judgments_visible,
            runtime.store.is_discharged,
        )
    with pytest.raises(TypeError):
        SupportsService(
            runtime.store.get_judgment,
            cast(Callable[[FrameId], tuple[Judgment, ...]], "visible"),
            runtime.store.is_discharged,
        )
    with pytest.raises(TypeError):
        SupportsService(
            runtime.store.get_judgment,
            runtime.store.judgments_visible,
            cast(Callable[[ObligationId, FrameId], bool], "discharged"),
        )


def test_a_check_request_context_must_be_a_verification_context():
    with pytest.raises(TypeError):
        CheckRequest(
            FrameId(0),
            (),
            (),
            None,
            context=cast(VerificationContext, "context"),
        )


def test_the_registry_returns_registered_checkers():
    checker = GoodChecker()
    registration = spec(checker)
    registry = CheckerRegistry({checker.id: registration})
    assert registry.get(checker.id) is checker
    assert registry.spec(checker.id) is registration
    assert registry.get("missing") is None
    assert registry.spec("missing") is None
    assert len(registry) == 1


def test_the_registry_refuses_a_key_that_disagrees_with_the_checker_id():
    with pytest.raises(ValueError):
        CheckerRegistry({"another.id": spec(GoodChecker())})


def test_the_registry_refuses_an_empty_version():
    with pytest.raises(ValueError):
        CheckerRegistry({"test.good": spec(NoVersion())})


def test_a_checker_spec_needs_kinds_and_a_schema():
    with pytest.raises(ValueError):
        CheckerSpec(
            GoodChecker(),
            CertificateSchema("test", "1", type(None)),
            frozenset(),
            frozenset({"test.specification"}),
            WorldId(0),
        )
    with pytest.raises(ValueError):
        CheckerSpec(
            GoodChecker(),
            CertificateSchema("test", "1", type(None)),
            frozenset({"test.problem"}),
            frozenset(),
            WorldId(0),
        )
    with pytest.raises(ValueError):
        CertificateSchema("", "1", type(None))
    with pytest.raises(ValueError):
        CertificateSchema("test", "", type(None))


def test_a_basis_reference_records_kind_version_scope_and_digest():
    reference = basis()
    assert reference.name == "library"
    assert reference.kind is BasisKind.STANDARD_LIBRARY
    assert reference.version == "1"
    assert reference.digest == "digest"
    assert reference.world == WorldId(0)
    with pytest.raises(ValueError):
        BasisRef("", BasisKind.STANDARD_LIBRARY, "1", "d", WorldId(0))
    with pytest.raises(ValueError):
        BasisRef("b", BasisKind.STANDARD_LIBRARY, "", "d", WorldId(0))
    with pytest.raises(ValueError):
        BasisRef("b", BasisKind.STANDARD_LIBRARY, "1", "", WorldId(0))


def test_a_checker_spec_does_not_repeat_trusted_dependencies():
    with pytest.raises(ValueError):
        spec(GoodChecker(), deps=(basis(), basis()))


def test_a_verified_outcome_reports_exactly_what_it_checked(runtime):
    conclusion = equation(runtime, variable(runtime), T.number(1))
    report = ObligationReport(conclusion, ObligationReason.DEFINEDNESS)
    outcome = Verified((conclusion,), (report,), (("domain", "Q"),), (0,))
    assert outcome.checked == (conclusion,)
    assert outcome.obligations == (report,)
    assert outcome.reads == (("domain", "Q"),)
    assert outcome.used_premises == (0,)


def test_a_refutation_needs_witnesses_and_a_detail(runtime):
    conclusion = equation(runtime, variable(runtime), T.number(1))
    with pytest.raises(ValueError):
        Refuted(conclusion, (), "no witnesses")
    with pytest.raises(ValueError):
        Refuted(conclusion, (T.number(1),), "")


def test_unverified_and_invalid_evidence_are_distinct():
    unknown = Unverified(Reason.BUDGET, "exhausted")
    assert unknown.reason is Reason.BUDGET
    assert unknown.detail == "exhausted"
    invalid = InvalidEvidence("malformed certificate")
    assert invalid.detail == "malformed certificate"


def test_a_check_request_is_a_value():
    request = CheckRequest(FrameId(0), (), (), "certificate")
    assert request.frame == FrameId(0)
    assert request.certificate == "certificate"


def test_a_checker_cannot_trust_a_basis_from_another_world():
    other = BasisRef(
        "other", BasisKind.STANDARD_LIBRARY, "1", "digest", WorldId(1)
    )
    with pytest.raises(ValueError):
        spec(GoodChecker(), deps=(other,))


def test_a_certificate_schema_needs_a_certificate_type():
    with pytest.raises(TypeError):
        CertificateSchema("test", "1", "not a type")


def test_a_verification_context_reads_only_its_own_world_and_chain(runtime):
    context = VerificationContext(
        runtime.world.id, runtime.frame.id, runtime.frames
    )
    local = runtime_proposition(runtime, T.TRUE)
    assert context.readable(local)
    assert context.readable(
        typed_in(
            runtime.frames,
            runtime.frame.id,
            runtime.signature,
            variable(runtime),
        )
    )
    other = bootstrap()
    assert other.frame.id == runtime.frame.id
    foreign = runtime_proposition(other, T.TRUE)
    assert not context.readable(foreign)
    child = runtime.frames.create(runtime.frame.id)
    child_proposition = runtime_proposition(runtime, T.TRUE, child.id)
    assert not context.readable(child_proposition)


def problem(runtime, *, region=None):
    return ProblemSpec(
        "test.problem",
        (
            typed_in(
                runtime.frames,
                runtime.frame.id,
                runtime.signature,
                variable(runtime),
            ),
        ),
        runtime.request.roles,
        region,
        ResultLanguage.EXPRESSION,
        Coverage.ONE_VERIFIED,
        domain_requirement=DomainRequirement(
            coefficient=runtime.request.coefficient_domain,
            values=runtime.request.value_domain,
        ),
    )


def request_for(runtime, problem_spec):
    return CheckRequest(
        runtime.frame.id,
        (),
        (),
        None,
        problem=problem_spec,
        context=verification_context(runtime),
    )


def greater_than(runtime, value):
    return runtime_proposition(
        runtime,
        head_app(
            runtime.signature,
            StructuralHead.GT,
            variable(runtime),
            T.number(value),
        ),
    )


def test_a_definedness_service_covers_readable_linear_regions(runtime):
    service = DefinednessService(
        DecisionService(runtime.signature),
        runtime.frames,
        runtime.frame.id,
    )
    positive = greater_than(runtime, 0)
    stronger = greater_than(runtime, 1)
    negative = runtime_proposition(
        runtime,
        head_app(
            runtime.signature,
            StructuralHead.LT,
            variable(runtime),
            T.number(0),
        ),
    )
    assert service.covers(stronger, positive) is True
    assert service.covers(positive, stronger) is None
    assert service.covers(positive, negative) is False
    assert service.covers(positive, positive) is True


def test_a_definedness_service_rejects_unreadable_regions(runtime):
    service = DefinednessService(
        DecisionService(runtime.signature),
        runtime.frames,
        runtime.frame.id,
    )
    local = greater_than(runtime, 0)
    other = bootstrap()
    foreign = greater_than(other, 0)
    assert service.covers(foreign, local) is False
    assert service.covers(local, foreign) is False
    child = runtime.frames.create(runtime.frame.id)
    child_region = runtime_proposition(
        runtime,
        head_app(
            runtime.signature,
            StructuralHead.GT,
            variable(runtime),
            T.number(0),
        ),
        child.id,
    )
    assert service.covers(child_region, local) is False
    assert service.covers(local, child_region) is False
    assert service.covers(child_region, child_region) is False


def test_a_definedness_service_without_a_frame_uses_the_common_meaning_frame(
    runtime,
):
    service = DefinednessService(
        DecisionService(runtime.signature), runtime.frames
    )
    positive = greater_than(runtime, 0)
    stronger = greater_than(runtime, 1)
    assert service.covers(stronger, positive) is True
    child = runtime.frames.create(runtime.frame.id)
    child_region = runtime_proposition(
        runtime,
        head_app(
            runtime.signature,
            StructuralHead.GT,
            variable(runtime),
            T.number(0),
        ),
        child.id,
    )
    assert service.covers(child_region, positive) is False


def test_a_definedness_service_uses_its_decision(runtime):
    positive = greater_than(runtime, 0)
    stronger = greater_than(runtime, 1)
    service = DefinednessService(
        RefusingDecision(runtime.signature),
        runtime.frames,
        runtime.frame.id,
    )
    assert service.covers(stronger, positive) is None


def test_a_definedness_service_requires_definedness_premises(runtime):
    service = DefinednessService(
        DecisionService(runtime.signature),
        runtime.frames,
        runtime.frame.id,
    )
    x = variable(runtime)
    powered = head_app(
        runtime.signature, StructuralHead.POWER, x, T.number(-1)
    )
    partial = runtime_proposition(
        runtime,
        head_app(
            runtime.signature, StructuralHead.EQ, powered, powered
        ),
    )
    positive = greater_than(runtime, 0)
    assert service.covers(partial, positive) is None
    assert service.covers(positive, partial) is None
    implied = runtime_proposition(
        runtime,
        head_app(
            runtime.signature,
            StructuralHead.AND,
            head_app(
                runtime.signature, StructuralHead.GT, x, T.number(0)
            ),
            head_app(
                runtime.signature, StructuralHead.EQ, powered, powered
            ),
        ),
    )
    assert service.covers(implied, positive) is True


def test_a_definedness_service_validates_its_inputs(runtime):
    decision = DecisionService(runtime.signature)
    with pytest.raises(TypeError):
        DefinednessService(
            cast(DecisionService, object()), runtime.frames
        )
    with pytest.raises(TypeError):
        DefinednessService(decision, cast(FrameStore, object()))
    with pytest.raises(TypeError):
        DefinednessService(
            decision, runtime.frames, cast(FrameId, "frame")
        )
    service = DefinednessService(
        decision, runtime.frames, runtime.frame.id
    )
    with pytest.raises(TypeError):
        service.covers(
            cast(Proposition, object()), greater_than(runtime, 0)
        )
    with pytest.raises(TypeError):
        service.covers(
            greater_than(runtime, 0), cast(Proposition, object())
        )


def test_a_verification_context_carries_the_definedness_service(runtime):
    decision = DecisionService(runtime.signature)
    service = DefinednessService(
        decision, runtime.frames, runtime.frame.id
    )
    context = VerificationContext(
        runtime.world.id,
        runtime.frame.id,
        runtime.frames,
        decision=decision,
        definedness=service,
    )
    assert context.definedness is service
    with pytest.raises(TypeError):
        VerificationContext(
            runtime.world.id,
            runtime.frame.id,
            runtime.frames,
            definedness=cast(DefinednessService, object()),
        )


def test_problem_mismatch_without_a_region_keeps_its_old_behavior(runtime):
    assert problem_mismatch(request_for(runtime, problem(runtime))) is None


def test_problem_mismatch_checks_roles_interpretation_and_exactness(runtime):
    fixed = problem(runtime)
    request = request_for(runtime, fixed)
    assert (
        problem_mismatch(
            request,
            roles=runtime.request.roles,
            exactness=Exactness.EXACT,
        )
        is None
    )
    other_sort = replace(
        runtime.request.roles,
        target_sort=S.RATIONAL,
    )
    mismatch = problem_mismatch(request, roles=other_sort)
    assert mismatch is not None
    assert "roles" in mismatch
    mismatch = problem_mismatch(
        request,
        interpretation_requirement=InterpretationRequirement.FORMAL,
    )
    assert mismatch is not None
    assert "interpretation" in mismatch
    object.__setattr__(fixed, "exactness", Exactness.APPROXIMATE)
    mismatch = problem_mismatch(request, exactness=Exactness.EXACT)
    assert mismatch is not None
    assert "exactness" in mismatch


def test_problem_mismatch_checks_region_coverage(runtime):
    unbounded = problem(runtime)
    assert (
        problem_mismatch(
            request_for(runtime, unbounded), region=T.TRUE
        )
        is None
    )
    assert (
        problem_mismatch(
            request_for(runtime, unbounded),
            region=greater_than(runtime, 0).term,
        )
        is not None
    )
    narrower = problem(runtime, region=greater_than(runtime, 1))
    assert (
        problem_mismatch(
            request_for(runtime, narrower),
            region=greater_than(runtime, 0).term,
        )
        is None
    )
    wider = problem(runtime, region=greater_than(runtime, 0))
    mismatch = problem_mismatch(
        request_for(runtime, wider),
        region=greater_than(runtime, 1).term,
    )
    assert mismatch is not None
    assert "not covered" in mismatch


def test_problem_mismatch_uses_the_context_decision_service(runtime):
    narrower = problem(runtime, region=greater_than(runtime, 1))
    region = greater_than(runtime, 0).term
    accepted = CheckRequest(
        runtime.frame.id,
        (),
        (),
        None,
        problem=narrower,
        context=VerificationContext(
            runtime.world.id,
            runtime.frame.id,
            runtime.frames,
            decision=DecisionService(runtime.signature),
        ),
    )
    assert problem_mismatch(accepted, region=region) is None
    refusing = CheckRequest(
        runtime.frame.id,
        (),
        (),
        None,
        problem=narrower,
        context=VerificationContext(
            runtime.world.id,
            runtime.frame.id,
            runtime.frames,
            decision=RefusingDecision(runtime.signature),
        ),
    )
    mismatch = problem_mismatch(refusing, region=region)
    assert mismatch is not None
    assert "not covered" in mismatch


def test_problem_mismatch_rejects_an_input_from_another_world(runtime):
    other = bootstrap()
    foreign_input = typed_in(
        other.frames,
        other.frame.id,
        other.signature,
        variable(other),
    )
    foreign_problem = ProblemSpec(
        "test.problem",
        (foreign_input,),
        other.request.roles,
        None,
        ResultLanguage.EXPRESSION,
        Coverage.ONE_VERIFIED,
        domain_requirement=DomainRequirement(
            coefficient=other.request.coefficient_domain,
            values=other.request.value_domain,
        ),
    )
    mismatch = problem_mismatch(request_for(runtime, foreign_problem))
    assert mismatch is not None
    assert "another meaning world" in mismatch


def test_an_inference_record_names_its_certificate_schema():
    record = InferenceRecord(
        InferenceId(0), FrameId(0), "checker", "1", (), (), None
    )
    assert record.certificate_schema == "unrecorded"
    assert record.certificate_schema_version == "unrecorded"
    with pytest.raises(ValueError):
        InferenceRecord(
            InferenceId(0),
            FrameId(0),
            "checker",
            "1",
            (),
            (),
            None,
            certificate_schema="",
        )
    with pytest.raises(ValueError):
        InferenceRecord(
            InferenceId(0),
            FrameId(0),
            "checker",
            "1",
            (),
            (),
            None,
            certificate_schema_version="",
        )
