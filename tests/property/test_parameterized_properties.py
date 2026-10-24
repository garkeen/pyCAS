"""Randomized parameterized differentiation, verified independently."""

import random
from fractions import Fraction

from support import runtime_proposition, variable

from cas.kernel.evidence import CheckRequest, Refuted, Verified
from cas.language.problems import ParameterMode
from cas.math.calculus.differentiation.checker import DerivativeCertificate
from cas.math.calculus.differentiation.specification import has_derivative
from cas.math.calculus.differentiation.verify import verify_derivative
from cas.runtime import bootstrap_parameterized
from cas.semantics.specialization import (
    Applied,
    CoverageClaim,
    GenericResult,
    Specialization,
    specialize,
)
from cas.syntax import binding as B
from cas.syntax import term as T

SEED = 20261027


def random_parameter_polynomial(
    rng: random.Random, ring, *,
    max_degree: int = 3, max_terms: int = 3,
):
    value = ring.zero()
    for _ in range(rng.randint(1, max_terms)):
        exponent = rng.randint(0, max_degree)
        coefficient = Fraction(rng.randint(-3, 3), rng.randint(1, 3))
        value = ring.add(
            value, ring.monomial((exponent,), coefficient)
        )
    return value


def random_target_polynomial(rng: random.Random, runtime):
    target = runtime.ring
    parameter_ring = runtime.bridge.coefficient_ring
    value = target.zero()
    for _ in range(rng.randint(1, 4)):
        exponent = rng.randint(0, 5)
        coefficient = random_parameter_polynomial(rng, parameter_ring)
        value = target.add(
            value, target.monomial((exponent,), coefficient)
        )
    return value


def test_the_verifier_accepts_random_parameterized_derivatives():
    runtime = bootstrap_parameterized()
    rng = random.Random(SEED)
    for _ in range(100):
        source = random_target_polynomial(rng, runtime)
        candidate = runtime.ring.derivative(source, 0)
        assert verify_derivative(runtime.ring, source, candidate, 0)


def test_the_checker_accepts_and_refutes_parameterized_candidates():
    runtime = bootstrap_parameterized()
    rng = random.Random(SEED + 1)
    x = variable(runtime)
    for _ in range(30):
        source = random_target_polynomial(rng, runtime)
        derivative = runtime.ring.derivative(source, 0)
        source_term = runtime.bridge.to_term(source)
        candidate_term = runtime.bridge.to_term(derivative)
        assert source_term is not None
        assert candidate_term is not None
        proposition = runtime_proposition(
            runtime,
            has_derivative(
                runtime.vocabulary,
                T.TRUE,
                source_term,
                x,
                candidate_term,
            ),
        )
        certificate = DerivativeCertificate(
            T.TRUE, source_term, runtime.variable, candidate_term
        )
        outcome = runtime.checker.check(
            CheckRequest(runtime.frame.id, (proposition,), (), certificate)
        )
        assert isinstance(outcome, Verified)

        wrong_value = runtime.ring.add(derivative, runtime.ring.one())
        wrong_term = runtime.bridge.to_term(wrong_value)
        assert wrong_term is not None
        wrong_proposition = runtime_proposition(
            runtime,
            has_derivative(
                runtime.vocabulary, T.TRUE, source_term, x, wrong_term
            ),
        )
        wrong_certificate = DerivativeCertificate(
            T.TRUE, source_term, runtime.variable, wrong_term
        )
        wrong_outcome = runtime.checker.check(
            CheckRequest(
                runtime.frame.id,
                (wrong_proposition,),
                (),
                wrong_certificate,
            )
        )
        assert isinstance(wrong_outcome, Refuted)


def test_specialization_commutes_with_differentiation():
    runtime = bootstrap_parameterized()
    specialization = runtime.specialization
    assert specialization is not None
    parameter = runtime.request.parameters[0]
    true = runtime_proposition(runtime, T.TRUE)
    rng = random.Random(SEED + 2)
    for _ in range(100):
        source = random_target_polynomial(rng, runtime)
        candidate = runtime.ring.derivative(source, 0)
        source_term = runtime.bridge.to_term(source)
        candidate_term = runtime.bridge.to_term(candidate)
        assert source_term is not None
        assert candidate_term is not None
        family = GenericResult.assemble(
            result=candidate_term,
            valid_on=true,
            excluded_cases=(),
            correctness_specification=true,
            parameter_mode=ParameterMode.ALL_PARAMETER_VALUES,
        )
        assert family.coverage_claim is CoverageClaim.ALL_VALUES

        value = Fraction(rng.randint(-4, 4), rng.randint(1, 4))
        outcome = specialize(
            family,
            runtime.request,
            Specialization({parameter: value}),
            runtime.signature,
        )
        assert isinstance(outcome, Applied)
        assert not B.free_symbols(outcome.result) & {parameter}

        specialized_source = B.substitute_free(
            source_term, {parameter: T.number(value)}
        )
        source_value = specialization.bridge.to_value(specialized_source)
        result_value = specialization.bridge.to_value(outcome.result)
        assert source_value is not None
        assert result_value is not None
        assert specialization.ring.equal(
            result_value, specialization.differential.deriv(source_value)
        )
