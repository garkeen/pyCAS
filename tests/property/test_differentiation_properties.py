"""Randomized derivative acceptance and refusal through independent checks."""

import random
from fractions import Fraction

from support import (
    render_value,
    runtime_proposition,
    variable,
    verification_context,
    view_of,
)

from cas.kernel.evidence import CheckRequest, Refuted, Verified
from cas.language.roles import CandidateRole
from cas.math.calculus.differentiation.certificate import DerivativeCertificate
from cas.math.calculus.differentiation.specification import has_derivative
from cas.math.calculus.differentiation.verify import verify_derivative
from cas.runtime.bootstrap import new_workspace
from cas.syntax import term as T
from cas.workflow.records import OperationStatus

SEED = 20261026


def random_polynomial(
    rng: random.Random,
    ring,
    *,
    max_degree: int = 5,
    max_terms: int = 5,
):
    value = ring.zero()
    for _ in range(rng.randint(1, max_terms)):
        exponents = (rng.randint(0, max_degree),)
        coefficient = Fraction(rng.randint(-4, 4), rng.randint(1, 3))
        value = ring.add(value, ring.monomial(exponents, coefficient))
    return value


def render(runtime, value) -> T.Term:
    return render_value(runtime, value)


def claim(runtime, source: T.Term, candidate: T.Term):
    return runtime_proposition(
        runtime,
        has_derivative(
            runtime.vocabulary,
            T.TRUE,
            source,
            variable(runtime),
            candidate,
        ),
    )


def check(runtime, proposition, source: T.Term, candidate: T.Term):
    certificate = DerivativeCertificate(
        T.TRUE, source, runtime.variable, candidate
    )
    return runtime.checker.check(
        CheckRequest(
            runtime.frame.id,
            (proposition,),
            (),
            certificate,
            candidate=candidate,
            candidate_role=CandidateRole.RESULT,
            context=verification_context(runtime, algebra=runtime.request),
        )
    )


def test_the_verifier_accepts_every_ring_derivative(runtime):
    rng = random.Random(SEED)
    for _ in range(300):
        source = random_polynomial(rng, runtime.ring)
        candidate = runtime.ring.derivative(source, 0)
        assert verify_derivative(runtime.ring, source, candidate, 0)


def test_the_verifier_rejects_perturbed_candidates(runtime):
    rng = random.Random(SEED + 1)
    for _ in range(200):
        source = random_polynomial(rng, runtime.ring)
        candidate = runtime.ring.add(
            runtime.ring.derivative(source, 0), runtime.ring.one()
        )
        assert not verify_derivative(runtime.ring, source, candidate, 0)


def test_the_verifier_confirms_linearity_and_leibniz(runtime):
    rng = random.Random(SEED + 2)
    for _ in range(200):
        first = random_polynomial(rng, runtime.ring)
        second = random_polynomial(rng, runtime.ring)
        first_derivative = runtime.ring.derivative(first, 0)
        second_derivative = runtime.ring.derivative(second, 0)
        assert verify_derivative(
            runtime.ring,
            runtime.ring.add(first, second),
            runtime.ring.add(first_derivative, second_derivative),
            0,
        )
        assert verify_derivative(
            runtime.ring,
            runtime.ring.mul(first, second),
            runtime.ring.add(
                runtime.ring.mul(first_derivative, second),
                runtime.ring.mul(first, second_derivative),
            ),
            0,
        )


def test_the_checker_accepts_correct_and_refutes_perturbed_candidates(runtime):
    rng = random.Random(SEED + 3)
    for _ in range(80):
        source = random_polynomial(rng, runtime.ring)
        derivative = runtime.ring.derivative(source, 0)
        source_term = render(runtime, source)
        candidate_term = render(runtime, derivative)
        outcome = check(
            runtime,
            claim(runtime, source_term, candidate_term),
            source_term,
            candidate_term,
        )
        assert isinstance(outcome, Verified)

        wrong_term = render(
            runtime, runtime.ring.add(derivative, runtime.ring.one())
        )
        wrong = check(
            runtime,
            claim(runtime, source_term, wrong_term),
            source_term,
            wrong_term,
        )
        assert isinstance(wrong, Refuted)


def test_the_workspace_publishes_random_derivatives(runtime):
    rng = random.Random(SEED + 4)
    workspace = new_workspace(runtime)
    for _ in range(40):
        source = random_polynomial(rng, runtime.ring)
        source_term = render(runtime, source)
        expression = workspace.intake(source_term)
        result = workspace.differentiate(expression, runtime.variable)
        assert result.status is OperationStatus.VERIFIED
        value = view_of(runtime, result.result.term).value
        assert runtime.ring.equal(value, runtime.ring.derivative(source, 0))
