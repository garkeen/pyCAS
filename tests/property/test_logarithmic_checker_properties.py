"""Fixed-seed properties of the rational-logarithmic checker."""

import random
from fractions import Fraction

from logarithmic_support import (
    LogSetup,
    check_bundle,
    linear_factor,
    log_setup,
    make_bundle,
    monic_product,
    polynomial,
)

from cas.kernel.evidence import Unverified, Verified

_SEED = 20261112
_ROOTS = tuple(range(-7, 8))
_COEFFICIENTS = (
    Fraction(1),
    Fraction(-1),
    Fraction(1, 2),
    Fraction(-1, 2),
    Fraction(2),
    Fraction(-2),
    Fraction(1, 3),
    Fraction(-1, 3),
    Fraction(3, 2),
    Fraction(-3, 2),
)


def source_value(
    setup: LogSetup,
    polynomial_part,
    entries,
):
    field = setup.bridge.field
    ring = field.polynomials
    total = field.derivative(polynomial_part)
    for coefficient, argument in entries:
        total = field.add(
            total,
            field.fraction(
                ring.mul(
                    ring.constant(coefficient),
                    ring.derivative(argument, 0),
                ),
                argument,
            ),
        )
    return total


def random_case(setup: LogSetup, rng: random.Random):
    """A random rational function whose logarithmic part is exact."""
    field = setup.bridge.field
    term_count = rng.randint(1, 3)
    coefficients = rng.sample(_COEFFICIENTS, term_count)
    available = list(_ROOTS)
    rng.shuffle(available)
    entries = []
    for coefficient in coefficients:
        size = rng.randint(1, 2)
        roots = tuple(available.pop() for _ in range(size))
        entries.append((coefficient, monic_product(setup, roots)))
    degree = rng.randint(0, 3)
    part_terms = tuple(
        (exponent, Fraction(rng.randint(-2, 2)))
        for exponent in range(degree + 1)
    )
    polynomial_part = field.of_polynomial(polynomial(setup, part_terms))
    return polynomial_part, tuple(entries), source_value(
        setup, polynomial_part, tuple(entries)
    )


def test_random_honest_decompositions_verify(runtime):
    setup = log_setup(runtime)
    rng = random.Random(_SEED)
    for _ in range(8):
        polynomial_part, entries, source = random_case(setup, rng)
        bundle = make_bundle(
            setup,
            source_value=source,
            polynomial_part_value=polynomial_part,
            entries=entries,
        )
        outcome = check_bundle(setup, bundle)
        assert isinstance(outcome, Verified), outcome
        assert outcome.checked == (bundle.proposition,)


def test_a_tampered_coefficient_is_not_verified(runtime):
    setup = log_setup(runtime)
    rng = random.Random(_SEED + 1)
    for _ in range(6):
        polynomial_part, entries, source = random_case(setup, rng)
        coefficient, argument = entries[0]
        replacement = coefficient + 1
        while replacement == 0 or replacement in {
            item[0] for item in entries
        }:
            replacement += 1
        tampered = ((replacement, argument), *entries[1:])
        bundle = make_bundle(
            setup,
            source_value=source,
            polynomial_part_value=polynomial_part,
            entries=tampered,
        )
        outcome = check_bundle(setup, bundle)
        assert not isinstance(outcome, Verified), outcome
        assert isinstance(outcome, Unverified), outcome
        assert "regional_logarithmic_identity" in outcome.missing


def test_a_tampered_argument_is_not_verified(runtime):
    setup = log_setup(runtime)
    rng = random.Random(_SEED + 2)
    for _ in range(6):
        polynomial_part, entries, source = random_case(setup, rng)
        coefficient, _ = entries[0]
        fresh = linear_factor(setup, 11)
        tampered = ((coefficient, fresh), *entries[1:])
        bundle = make_bundle(
            setup,
            source_value=source,
            polynomial_part_value=polynomial_part,
            entries=tampered,
        )
        outcome = check_bundle(setup, bundle)
        assert not isinstance(outcome, Verified), outcome
        assert isinstance(outcome, Unverified), outcome
        assert "regional_logarithmic_identity" in outcome.missing
