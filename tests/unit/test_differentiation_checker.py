"""The HasDerivative checker: exact instances, honest refusal, independent math."""

import pytest
from support import (
    equation,
    head_app,
    runtime_proposition,
    variable,
)

from cas.algebra.polynomial import PolynomialRing
from cas.algebra.rationals import RationalField
from cas.foundation.ids import SymbolId
from cas.kernel.evidence import CheckRequest, InvalidEvidence, Refuted, Unverified, Verified
from cas.language import sorts as S
from cas.language.decisions import Reason
from cas.language.signatures import StructuralHead
from cas.math.calculus.differentiation.checker import (
    DerivativeCertificate,
    DerivativeChecker,
)
from cas.math.calculus.differentiation.specification import has_derivative
from cas.semantics.frames import Declaration
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


def request(runtime, proposition, certificate, frame=None) -> CheckRequest:
    frame_id = runtime.frame.id if frame is None else frame
    return CheckRequest(frame_id, (proposition,), (), certificate)


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
        request(runtime, proposition, certificate(runtime, source, candidate))
    )
    assert isinstance(outcome, Verified)
    assert outcome.checked == (proposition,)


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
        request(runtime, proposition, certificate(runtime, source, candidate))
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
        outcome = runtime.checker.check(request(runtime, proposition, bad))
        assert isinstance(outcome, InvalidEvidence), bad


def test_only_the_whole_domain_region_is_verified(runtime):
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
        )
    )
    assert isinstance(outcome, Unverified)
    assert outcome.reason is Reason.GUARDED


def test_a_claim_in_another_variable_is_outside_the_fragment(runtime):
    y = runtime.table.intern("y")
    child = runtime.frames.create(
        runtime.frame.id, declarations=(Declaration(y, "y", S.REAL),)
    )
    source, candidate = source_term(runtime), candidate_term(runtime)
    proposition = runtime_proposition(
        runtime,
        claim_term(
            runtime, source, candidate, variable_term=T.symbol(y, "y")
        ),
        child.id,
    )
    outcome = runtime.checker.check(
        request(
            runtime,
            proposition,
            certificate(runtime, source, candidate, variable_id=y),
            frame=child.id,
        )
    )
    assert isinstance(outcome, Unverified)
    assert outcome.reason is Reason.FRAGMENT


def test_a_source_or_candidate_outside_the_fragment_is_unverified(runtime):
    y = runtime.table.intern("y")
    child = runtime.frames.create(
        runtime.frame.id, declarations=(Declaration(y, "y", S.REAL),)
    )
    y_term = T.symbol(y, "y")
    for source, candidate in (
        (y_term, T.number(1)),
        (variable(runtime), y_term),
    ):
        proposition = runtime_proposition(
            runtime, claim_term(runtime, source, candidate), child.id
        )
        outcome = runtime.checker.check(
            request(
                runtime,
                proposition,
                certificate(runtime, source, candidate),
                frame=child.id,
            )
        )
        assert isinstance(outcome, Unverified)
        assert outcome.reason is Reason.FRAGMENT


def test_a_multivariate_ring_is_refused_at_construction(runtime):
    ring = PolynomialRing(
        (runtime.variable, SymbolId(10_000)), RationalField()
    )
    with pytest.raises(TypeError):
        DerivativeChecker(ring, runtime.signature, runtime.vocabulary)


def test_all_conclusions_must_match_the_same_certificate(runtime):
    source, candidate = source_term(runtime), candidate_term(runtime)
    proposition = runtime_proposition(
        runtime, claim_term(runtime, source, candidate)
    )
    checker = runtime.checker
    verified = checker.check(
        CheckRequest(
            runtime.frame.id, (proposition, proposition), (), certificate(runtime, source, candidate)
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
    )
    outcome = checker.check(
        request(runtime, proposition, certificate(runtime, source, candidate))
    )
    assert isinstance(outcome, Verified)
