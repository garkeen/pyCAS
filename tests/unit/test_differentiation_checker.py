"""The HasDerivative checker: exact instances, honest refusal, independent math."""

from dataclasses import replace

import pytest
from support import (
    equation,
    head_app,
    runtime_proposition,
    typed_in,
    variable,
    verification_context,
)

from cas.algebra.polynomial import PolynomialRing
from cas.algebra.rationals import RationalField
from cas.foundation.ids import SymbolId
from cas.kernel.evidence import CheckRequest, InvalidEvidence, Refuted, Unverified, Verified
from cas.language import sorts as S
from cas.language.decisions import Reason
from cas.language.problems import (
    Coverage,
    DomainRequirement,
    ProblemSpec,
    ResultLanguage,
)
from cas.language.roles import CandidateRole
from cas.language.signatures import StructuralHead
from cas.math.calculus.differentiation.checker import (
    DerivativeCertificate,
    DerivativeChecker,
)
from cas.math.calculus.differentiation.specification import has_derivative
from cas.semantics.frames import Declaration
from cas.semantics.specialization import Specialization
from cas.syntax import term as T


def source_term(runtime) -> T.Apply:
    x = variable(runtime)
    return head_app(
        runtime.signature,
        StructuralHead.PLUS,
        head_app(
            runtime.signature, StructuralHead.POWER, x, T.number(3)
        ),
        head_app(
            runtime.signature, StructuralHead.TIMES, T.number(-3), x
        ),
    )


def candidate_term(runtime) -> T.Apply:
    x = variable(runtime)
    return head_app(
        runtime.signature,
        StructuralHead.PLUS,
        head_app(
            runtime.signature,
            StructuralHead.TIMES,
            T.number(3),
            head_app(
                runtime.signature, StructuralHead.POWER, x, T.number(2)
            ),
        ),
        T.number(-3),
    )


def claim_term(
    runtime,
    source: T.Term,
    candidate: T.Term,
    variable_term: T.Term | None = None,
    region: T.Term = T.TRUE,
) -> T.Term:
    return has_derivative(
        runtime.vocabulary,
        region,
        source,
        variable(runtime) if variable_term is None else variable_term,
        candidate,
    )


def request(
    runtime,
    proposition,
    certificate,
    candidate,
    frame=None,
    role=CandidateRole.RESULT,
) -> CheckRequest:
    frame_id = runtime.frame.id if frame is None else frame
    return CheckRequest(
        frame_id,
        (proposition,),
        (),
        certificate,
        candidate=candidate,
        candidate_role=role,
        context=verification_context(runtime, frame_id, algebra=runtime.request),
    )


def certificate(
    runtime,
    source: T.Term,
    candidate: T.Term,
    variable_id: SymbolId | None = None,
    region: T.Term = T.TRUE,
) -> DerivativeCertificate:
    return DerivativeCertificate(
        region,
        source,
        runtime.variable if variable_id is None else variable_id,
        candidate,
    )


def test_a_correct_instance_is_verified(runtime):
    source, candidate = source_term(runtime), candidate_term(runtime)
    proposition = runtime_proposition(
        runtime, claim_term(runtime, source, candidate)
    )
    outcome = runtime.checker.check(
        request(
            runtime,
            proposition,
            certificate(runtime, source, candidate),
            candidate,
        )
    )
    assert isinstance(outcome, Verified)
    assert outcome.checked == (proposition,)


def test_a_missing_candidate_is_invalid_evidence(runtime):
    source, candidate = source_term(runtime), candidate_term(runtime)
    proposition = runtime_proposition(
        runtime, claim_term(runtime, source, candidate)
    )
    outcome = runtime.checker.check(
        request(
            runtime,
            proposition,
            certificate(runtime, source, candidate),
            None,
        )
    )
    assert isinstance(outcome, InvalidEvidence)
    assert "candidate" in outcome.detail


def test_a_candidate_different_from_the_claim_is_invalid_evidence(runtime):
    source, candidate = source_term(runtime), candidate_term(runtime)
    proposition = runtime_proposition(
        runtime, claim_term(runtime, source, candidate)
    )
    outcome = runtime.checker.check(
        request(
            runtime,
            proposition,
            certificate(runtime, source, candidate),
            T.number(0),
        )
    )
    assert isinstance(outcome, InvalidEvidence)
    assert "candidate" in outcome.detail


def test_a_missing_candidate_role_is_invalid_evidence(runtime):
    source, candidate = source_term(runtime), candidate_term(runtime)
    proposition = runtime_proposition(
        runtime, claim_term(runtime, source, candidate)
    )
    outcome = runtime.checker.check(
        request(
            runtime,
            proposition,
            certificate(runtime, source, candidate),
            candidate,
            role=None,
        )
    )
    assert isinstance(outcome, InvalidEvidence)
    assert "candidate role" in outcome.detail


def test_a_wrong_candidate_role_is_invalid_evidence(runtime):
    source, candidate = source_term(runtime), candidate_term(runtime)
    proposition = runtime_proposition(
        runtime, claim_term(runtime, source, candidate)
    )
    outcome = runtime.checker.check(
        request(
            runtime,
            proposition,
            certificate(runtime, source, candidate),
            candidate,
            role=CandidateRole.SET,
        )
    )
    assert isinstance(outcome, InvalidEvidence)
    assert "candidate role" in outcome.detail


def test_the_source_role_publishes_the_antiderivative(runtime):
    source, candidate = source_term(runtime), candidate_term(runtime)
    proposition = runtime_proposition(
        runtime, claim_term(runtime, source, candidate)
    )
    outcome = runtime.checker.check(
        request(
            runtime,
            proposition,
            certificate(runtime, source, candidate),
            source,
            role=CandidateRole.SOURCE,
        )
    )
    assert isinstance(outcome, Verified)


def test_a_wrong_candidate_is_refuted_with_witnesses(runtime):
    source = source_term(runtime)
    candidate = head_app(
        runtime.signature,
        StructuralHead.PLUS,
        candidate_term(runtime),
        T.number(1),
    )
    proposition = runtime_proposition(
        runtime, claim_term(runtime, source, candidate)
    )
    outcome = runtime.checker.check(
        request(
            runtime,
            proposition,
            certificate(runtime, source, candidate),
            candidate,
        )
    )
    assert isinstance(outcome, Refuted)
    assert outcome.proposition == proposition
    assert outcome.witnesses == (source, candidate)


def test_a_conclusion_that_is_not_a_derivative_claim_is_invalid_evidence(runtime):
    proposition = equation(runtime, variable(runtime), T.number(1))
    outcome = runtime.checker.check(
        request(
            runtime,
            proposition,
            certificate(runtime, variable(runtime), T.number(1)),
            T.number(1),
        )
    )
    assert isinstance(outcome, InvalidEvidence)


def test_the_certificate_is_required_and_must_match(runtime):
    source, candidate = source_term(runtime), candidate_term(runtime)
    proposition = runtime_proposition(
        runtime, claim_term(runtime, source, candidate)
    )
    for bad in (
        None,
        "not a certificate",
        certificate(runtime, source, T.number(0)),
        certificate(runtime, T.number(0), candidate),
        certificate(runtime, source, candidate, region=T.FALSE),
        certificate(runtime, source, candidate, variable_id=SymbolId(10_000)),
    ):
        outcome = runtime.checker.check(
            request(runtime, proposition, bad, candidate)
        )
        assert isinstance(outcome, InvalidEvidence), bad


def test_an_empty_region_is_not_admitted(runtime):
    source, candidate = source_term(runtime), candidate_term(runtime)
    proposition = runtime_proposition(
        runtime,
        claim_term(runtime, source, candidate, region=T.FALSE),
    )
    outcome = runtime.checker.check(
        request(
            runtime,
            proposition,
            certificate(runtime, source, candidate, region=T.FALSE),
            candidate,
        )
    )
    assert isinstance(outcome, Unverified)
    assert outcome.reason is Reason.GUARDED


def test_a_claim_in_another_variable_is_outside_the_fragment(runtime):
    w = runtime.table.intern("w")
    child = runtime.frames.create(
        runtime.frame.id, declarations=(Declaration(w, "w", S.REAL),)
    )
    source, candidate = source_term(runtime), candidate_term(runtime)
    proposition = runtime_proposition(
        runtime,
        claim_term(
            runtime, source, candidate, variable_term=T.symbol(w, "w")
        ),
        child.id,
    )
    outcome = runtime.checker.check(
        request(
            runtime,
            proposition,
            certificate(runtime, source, candidate, variable_id=w),
            candidate,
            frame=child.id,
        )
    )
    assert isinstance(outcome, Unverified)
    assert outcome.reason is Reason.FRAGMENT


def test_a_source_or_candidate_outside_the_fragment_is_unverified(runtime):
    w = runtime.table.intern("w")
    child = runtime.frames.create(
        runtime.frame.id, declarations=(Declaration(w, "w", S.REAL),)
    )
    w_term = T.symbol(w, "w")
    for source, candidate in (
        (w_term, T.number(1)),
        (variable(runtime), w_term),
    ):
        proposition = runtime_proposition(
            runtime, claim_term(runtime, source, candidate), child.id
        )
        outcome = runtime.checker.check(
            request(
                runtime,
                proposition,
                certificate(runtime, source, candidate),
                candidate,
                frame=child.id,
            )
        )
        assert isinstance(outcome, Unverified)
        assert outcome.reason is Reason.FRAGMENT
        assert "symbol_mapping" in outcome.missing


def test_a_multivariate_ring_is_refused_at_construction(runtime):
    ring = PolynomialRing(
        (runtime.variable, SymbolId(10_000)), RationalField()
    )
    with pytest.raises(TypeError):
        DerivativeChecker(
            ring,
            runtime.signature,
            runtime.vocabulary,
            runtime.bridge,
            runtime.frames,
            runtime.request,
        )


def test_all_conclusions_must_match_the_same_certificate(runtime):
    source, candidate = source_term(runtime), candidate_term(runtime)
    proposition = runtime_proposition(
        runtime, claim_term(runtime, source, candidate)
    )
    checker = runtime.checker
    verified = checker.check(
        CheckRequest(
            runtime.frame.id,
            (proposition, proposition),
            (),
            certificate(runtime, source, candidate),
            candidate=candidate,
            candidate_role=CandidateRole.RESULT,
            context=verification_context(runtime, algebra=runtime.request),
        )
    )
    assert isinstance(verified, Verified)
    other = runtime_proposition(
        runtime, claim_term(runtime, variable(runtime), T.number(1))
    )
    mixed = checker.check(
        CheckRequest(
            runtime.frame.id,
            (proposition, other),
            (),
            certificate(runtime, source, candidate),
            candidate=candidate,
            candidate_role=CandidateRole.RESULT,
            context=verification_context(runtime, algebra=runtime.request),
        )
    )
    assert isinstance(mixed, InvalidEvidence)


class RingWithoutDerivative:
    """A proxy that fails loudly if the checker asks for the ring derivative."""

    def __init__(self, ring):
        self._ring = ring

    def __getattr__(self, name):
        if name == "derivative":
            raise AssertionError("the checker called the ring derivative")
        return getattr(self._ring, name)


def test_the_checker_does_not_generate_the_answer(runtime):
    source, candidate = source_term(runtime), candidate_term(runtime)
    proposition = runtime_proposition(
        runtime, claim_term(runtime, source, candidate)
    )
    checker = DerivativeChecker(
        RingWithoutDerivative(runtime.ring),
        runtime.signature,
        runtime.vocabulary,
        runtime.bridge,
        runtime.frames,
        runtime.request,
    )
    outcome = checker.check(
        request(
            runtime,
            proposition,
            certificate(runtime, source, candidate),
            candidate,
        )
    )
    assert isinstance(outcome, Verified)


def test_global_verification_can_establish_a_regional_claim(runtime):
    source, candidate = source_term(runtime), candidate_term(runtime)
    region = head_app(runtime.signature, StructuralHead.GT, variable(runtime), T.number(0))
    proposition = runtime_proposition(runtime, claim_term(runtime, source, candidate, region=region))
    outcome = runtime.checker.check(
        request(
            runtime,
            proposition,
            certificate(runtime, source, candidate, region=region),
            candidate,
        )
    )
    assert isinstance(outcome, Verified)


def test_global_coefficient_mismatch_does_not_refute_pointwise_derivative_values(runtime):
    x = variable(runtime)
    source = head_app(runtime.signature, StructuralHead.POWER, x, T.number(2))
    region = head_app(runtime.signature, StructuralHead.EQ, x, T.number(0))
    proposition = runtime_proposition(runtime, claim_term(runtime, source, T.number(0), region=region))
    outcome = runtime.checker.check(
        request(
            runtime,
            proposition,
            certificate(runtime, source, T.number(0), region=region),
            T.number(0),
        )
    )
    assert isinstance(outcome, Unverified)


def problem_with_region(runtime, source, region):
    return ProblemSpec(
        "differentiate",
        (
            typed_in(
                runtime.frames,
                runtime.frame.id,
                runtime.signature,
                source,
            ),
        ),
        runtime.request.roles,
        runtime_proposition(runtime, region),
        ResultLanguage.EXPRESSION,
        Coverage.ONE_VERIFIED,
        interpretation_requirement=(
            runtime.request.interpretation_requirement
        ),
        domain_requirement=DomainRequirement(
            coefficient=runtime.request.coefficient_domain,
            values=runtime.request.value_domain,
        ),
    )


def test_the_problem_region_binds_the_claim_region(runtime):
    x = variable(runtime)
    source, candidate = source_term(runtime), candidate_term(runtime)
    positive = head_app(
        runtime.signature, StructuralHead.GT, x, T.number(0)
    )
    negative = head_app(
        runtime.signature, StructuralHead.LT, x, T.number(0)
    )
    proposition = runtime_proposition(
        runtime, claim_term(runtime, source, candidate, region=positive)
    )
    cert = certificate(runtime, source, candidate, region=positive)
    rejected = runtime.checker.check(
        CheckRequest(
            runtime.frame.id,
            (proposition,),
            (),
            cert,
            problem=problem_with_region(runtime, source, negative),
            candidate=candidate,
            candidate_role=CandidateRole.RESULT,
            context=verification_context(runtime, algebra=runtime.request),
        )
    )
    assert isinstance(rejected, InvalidEvidence)
    assert "region" in rejected.detail
    verified = runtime.checker.check(
        CheckRequest(
            runtime.frame.id,
            (proposition,),
            (),
            cert,
            problem=problem_with_region(runtime, source, positive),
            candidate=candidate,
            candidate_role=CandidateRole.RESULT,
            context=verification_context(runtime, algebra=runtime.request),
        )
    )
    assert isinstance(verified, Verified)


def specialization_setup(runtime):
    a = runtime.table.intern("a")
    child = runtime.frames.create(
        runtime.frame.id, declarations=(Declaration(a, "a", S.REAL),)
    )
    x = variable(runtime)
    a_term = T.symbol(a, "a")
    generic = head_app(
        runtime.signature,
        StructuralHead.TIMES,
        a_term,
        head_app(runtime.signature, StructuralHead.POWER, x, T.number(3)),
    )
    roles = runtime.request.roles
    problem = ProblemSpec(
        "specialize",
        (
            typed_in(
                runtime.frames, child.id, runtime.signature, generic
            ),
        ),
        roles,
        None,
        ResultLanguage.EXPRESSION,
        Coverage.ONE_VERIFIED,
        interpretation_requirement=(
            runtime.request.interpretation_requirement
        ),
        domain_requirement=DomainRequirement(
            coefficient=runtime.request.coefficient_domain,
            values=runtime.request.value_domain,
        ),
    )
    return child, a, x, generic, problem


def test_a_specialize_problem_binds_the_generic_source_and_mapping(runtime):
    child, a, x, generic, problem = specialization_setup(runtime)
    specialized = head_app(
        runtime.signature,
        StructuralHead.TIMES,
        T.number(2),
        head_app(runtime.signature, StructuralHead.POWER, x, T.number(3)),
    )
    candidate = head_app(
        runtime.signature,
        StructuralHead.TIMES,
        T.number(6),
        head_app(runtime.signature, StructuralHead.POWER, x, T.number(2)),
    )
    proposition = runtime_proposition(
        runtime, claim_term(runtime, specialized, candidate), child.id
    )
    certificate = DerivativeCertificate(
        T.TRUE,
        specialized,
        runtime.variable,
        candidate,
        generic_source=generic,
        specialization=Specialization({a: 2}),
    )
    request_with_problem = CheckRequest(
        child.id,
        (proposition,),
        (),
        certificate,
        problem=problem,
        candidate=candidate,
        candidate_role=CandidateRole.RESULT,
        context=verification_context(runtime, child.id, algebra=runtime.request),
    )
    verified = runtime.checker.check(request_with_problem)
    assert isinstance(verified, Verified)

    wrong_generic = head_app(
        runtime.signature,
        StructuralHead.TIMES,
        T.symbol(a, "a"),
        head_app(runtime.signature, StructuralHead.POWER, x, T.number(4)),
    )
    mismatched = DerivativeCertificate(
        T.TRUE,
        specialized,
        runtime.variable,
        candidate,
        generic_source=generic,
        specialization=Specialization({a: 3}),
    )
    refused = runtime.checker.check(
        CheckRequest(
            child.id,
            (proposition,),
            (),
            mismatched,
            problem=problem,
            candidate=candidate,
            candidate_role=CandidateRole.RESULT,
            context=verification_context(runtime, child.id, algebra=runtime.request),
        )
    )
    assert isinstance(refused, InvalidEvidence)
    assert "specialized source" in refused.detail

    foreign_problem = replace(
        problem,
        inputs=(
            typed_in(
                runtime.frames,
                child.id,
                runtime.signature,
                wrong_generic,
            ),
        ),
    )
    foreign = runtime.checker.check(
        CheckRequest(
            child.id,
            (proposition,),
            (),
            DerivativeCertificate(
                T.TRUE,
                specialized,
                runtime.variable,
                candidate,
                generic_source=wrong_generic,
                specialization=Specialization({a: 2}),
            ),
            problem=foreign_problem,
            candidate=candidate,
            candidate_role=CandidateRole.RESULT,
            context=verification_context(runtime, child.id, algebra=runtime.request),
        )
    )
    assert isinstance(foreign, InvalidEvidence)
    assert "specialized source" in foreign.detail

    for incomplete in (
        DerivativeCertificate(
            T.TRUE, specialized, runtime.variable, candidate
        ),
        DerivativeCertificate(
            T.TRUE,
            specialized,
            runtime.variable,
            candidate,
            generic_source=generic,
        ),
    ):
        missing = runtime.checker.check(
            CheckRequest(
                child.id,
                (proposition,),
                (),
                incomplete,
                problem=problem,
                candidate=candidate,
                candidate_role=CandidateRole.RESULT,
                context=verification_context(runtime, child.id, algebra=runtime.request),
            )
        )
        assert isinstance(missing, InvalidEvidence)
        assert "generic source" in missing.detail
