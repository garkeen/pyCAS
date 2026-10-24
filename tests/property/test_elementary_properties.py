"""Randomized elementary differentiation, checked independently."""

import random
from fractions import Fraction

from support import head_app, runtime_proposition, variable

from cas.kernel.evidence import CheckRequest, Verified
from cas.language.signatures import StructuralHead
from cas.math.calculus.differentiation.certificate import DerivativeCertificate
from cas.math.calculus.differentiation.specification import has_derivative
from cas.runtime import bootstrap_elementary
from cas.semantics.services import Derived
from cas.syntax import term as T

SEED = 20261102


def random_polynomial(rng: random.Random, ring, *, degree=4, terms=4):
    value = ring.zero()
    for _ in range(rng.randint(1, terms)):
        exponent = rng.randint(0, degree)
        coefficient = Fraction(rng.randint(-4, 4), rng.randint(1, 3))
        value = ring.add(value, ring.monomial((exponent,), coefficient))
    return value


def test_polynomials_agree_with_the_polynomial_view():
    runtime = bootstrap_elementary()
    rng = random.Random(SEED)
    for _ in range(100):
        source = random_polynomial(rng, runtime.ring)
        source_term = runtime.bridge.to_term(source)
        assert source_term is not None
        outcome = runtime.derivative.candidate(source_term)
        assert isinstance(outcome, Derived)
        candidate = runtime.bridge.to_value(outcome.term)
        assert candidate is not None
        assert runtime.ring.equal(
            candidate, runtime.ring.derivative(source, 0)
        )


def random_elementary(rng: random.Random, runtime, depth=0):
    x = variable(runtime)
    if depth >= 3:
        choice = rng.randrange(4)
        if choice == 0:
            return x
        if choice == 1:
            return T.number(rng.randint(-3, 3))
        if choice == 2:
            return T.number(Fraction(rng.randint(-3, 3), rng.randint(1, 3)))
        name = rng.choice(("pi", "e"))
        constant = runtime.elementary.constants[name]
        return T.symbol(constant.symbol, constant.name)
    choice = rng.randrange(6)
    if choice == 0:
        return x
    if choice == 1:
        return T.number(rng.randint(-3, 3))
    if choice == 2:
        return head_app(
            runtime.signature,
            StructuralHead.PLUS,
            random_elementary(rng, runtime, depth + 1),
            random_elementary(rng, runtime, depth + 1),
        )
    if choice == 3:
        return head_app(
            runtime.signature,
            StructuralHead.TIMES,
            random_elementary(rng, runtime, depth + 1),
            random_elementary(rng, runtime, depth + 1),
        )
    if choice == 4:
        return head_app(
            runtime.signature,
            StructuralHead.POWER,
            random_elementary(rng, runtime, depth + 1),
            T.number(rng.randint(0, 3)),
        )
    name = rng.choice(("sin", "cos", "exp"))
    function = runtime.elementary.functions[name]
    return T.app(
        T.symbol(function.symbol, function.name),
        random_elementary(rng, runtime, depth + 1),
    )


def test_random_declared_expressions_reach_the_independent_checker():
    runtime = bootstrap_elementary()
    rng = random.Random(SEED + 1)
    x = variable(runtime)
    for _ in range(30):
        source = random_elementary(rng, runtime)
        outcome = runtime.derivative.candidate(source)
        assert isinstance(outcome, Derived)
        proposition = runtime_proposition(
            runtime,
            has_derivative(
                runtime.vocabulary,
                T.TRUE if outcome.condition is None else outcome.condition,
                source,
                x,
                outcome.term,
            ),
        )
        certificate = DerivativeCertificate(
            T.TRUE if outcome.condition is None else outcome.condition,
            source,
            runtime.variable,
            outcome.term,
        )
        checked = runtime.checker.check(
            CheckRequest(runtime.frame.id, (proposition,), (), certificate)
        )
        assert isinstance(checked, Verified)


def random_conditional_expression(rng: random.Random, runtime):
    argument = random_elementary(rng, runtime, depth=2)
    name = rng.choice(("sqrt", "log"))
    function = runtime.elementary.functions[name]
    return T.app(
        T.symbol(function.symbol, function.name), argument
    )


def test_random_conditional_expressions_keep_their_region():
    runtime = bootstrap_elementary()
    rng = random.Random(SEED + 2)
    x = variable(runtime)
    conditional = 0
    checked_count = 0
    for _ in range(40):
        source = random_conditional_expression(rng, runtime)
        outcome = runtime.derivative.candidate(source)
        if not isinstance(outcome, Derived):
            continue
        checked_count += 1
        if outcome.condition is not None:
            conditional += 1
        region = T.TRUE if outcome.condition is None else outcome.condition
        proposition = runtime_proposition(
            runtime,
            has_derivative(
                runtime.vocabulary,
                region,
                source,
                x,
                outcome.term,
            ),
        )
        certificate = DerivativeCertificate(
            region, source, runtime.variable, outcome.term
        )
        checked = runtime.checker.check(
            CheckRequest(runtime.frame.id, (proposition,), (), certificate)
        )
        assert isinstance(checked, Verified)
    assert checked_count > 0
    assert conditional > 0
