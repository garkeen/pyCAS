"""Exact Sturm chains and open-interval root counts over Q."""

from fractions import Fraction

import pytest

from cas.algebra.polynomial import UnivariatePolynomialRing
from cas.algebra.protocols import Field
from cas.algebra.rational import RationalFunctionField
from cas.algebra.rationals import RationalField
from cas.algebra.real_roots import (
    RealRootFragmentError,
    count_real_roots_open,
    evaluate,
    sign_at,
    sign_variations,
    sturm_chain,
)
from cas.foundation.ids import SymbolId

X = SymbolId(1)
Y = SymbolId(2)


def ring() -> UnivariatePolynomialRing[Fraction]:
    return UnivariatePolynomialRing(X, RationalField())


def q(value: int, denominator: int = 1) -> Fraction:
    return Fraction(value, denominator)


def linear_factor(
    base: UnivariatePolynomialRing[Fraction], root: Fraction
):
    return base.sub(base.generator(0), base.constant(root))


def product_of_linear(
    base: UnivariatePolynomialRing[Fraction],
    roots: tuple[Fraction, ...],
):
    value = base.one()
    for root in roots:
        value = base.mul(value, linear_factor(base, root))
    return value


def test_sturm_chain_satisfies_the_remainder_recurrence():
    base = ring()
    value = product_of_linear(base, (q(-3), q(1), q(2)))
    chain = sturm_chain(base, value)
    assert base.equal(chain[0], value)
    derivative = base.derivative(value, 0)
    assert base.equal(chain[1], derivative)
    for index in range(len(chain) - 2):
        _, remainder = base.divmod(chain[index], chain[index + 1])
        assert base.equal(chain[index + 2], base.neg(remainder))
    assert base.is_constant(chain[-1])
    assert not chain[-1].is_zero()
    degrees = [base.degree(entry, 0) for entry in chain]
    assert all(
        earlier > later for earlier, later in zip(degrees, degrees[1:])
    )


def test_sturm_chain_refuses_zero_and_non_squarefree_inputs():
    base = ring()
    with pytest.raises(RealRootFragmentError) as zero:
        sturm_chain(base, base.zero())
    assert zero.value.missing == frozenset({"nonzero_polynomial"})
    repeated = base.pow(
        base.sub(base.generator(0), base.constant(q(1))), 2
    )
    with pytest.raises(RealRootFragmentError) as nonsquare:
        sturm_chain(base, repeated)
    assert nonsquare.value.missing == frozenset({"squarefree_polynomial"})


def test_constant_polynomial_has_a_one_entry_chain_and_zero_roots():
    base = ring()
    constant = base.constant(q(7, 3))
    assert sturm_chain(base, constant) == (constant,)
    assert count_real_roots_open(base, constant, q(-10), q(10)) == 0


def test_sign_variations_skip_zero_entries():
    base = ring()
    x = base.generator(0)
    chain = (
        x,
        base.sub(x, base.one()),
        base.one(),
    )
    # At 0 the signs are [0, -1, +1]: one change among the nonzero entries.
    assert sign_variations(base, chain, q(0)) == 1
    # At 1 the signs are [+1, 0, +1]: no change.
    assert sign_variations(base, chain, q(1)) == 0
    # At 1/2 the signs are [+1, -1, +1]: two changes.
    assert sign_variations(base, chain, q(1, 2)) == 2


def test_sign_and_evaluate_are_exact_horner_values():
    base = ring()
    value = product_of_linear(base, (q(-1), q(2)))
    assert evaluate(base, value, q(3)) == q(4)
    assert sign_at(base, value, q(0)) == -1
    assert sign_at(base, value, q(-2)) == 1


def test_open_interval_excludes_both_endpoint_roots():
    base = ring()
    x = base.generator(0)
    assert count_real_roots_open(base, x, q(-1), q(1)) == 1
    assert count_real_roots_open(base, x, q(-1), q(0)) == 0
    assert count_real_roots_open(base, x, q(0), q(1)) == 0
    assert count_real_roots_open(base, x, q(-2), q(0)) == 0
    quadratic = base.mul(x, base.sub(x, base.one()))
    assert count_real_roots_open(base, quadratic, q(-1), q(2)) == 2
    assert count_real_roots_open(base, quadratic, q(0), q(2)) == 1
    assert count_real_roots_open(base, quadratic, q(-1), q(0)) == 0
    assert count_real_roots_open(base, quadratic, q(1), q(2)) == 0


def test_count_is_invariant_under_nonzero_scalar_multiplication():
    base = ring()
    value = product_of_linear(base, (q(-2), q(1, 3), q(4)))
    baseline = count_real_roots_open(base, value, q(-3), q(5))
    for scale in (q(2), q(-5), q(3, 7)):
        assert (
            count_real_roots_open(
                base, base.mul(base.constant(scale), value), q(-3), q(5)
            )
            == baseline
        )


def test_count_is_additive_across_a_split_endpoint():
    base = ring()
    value = product_of_linear(base, (q(-2), q(0), q(1, 2), q(3)))
    lower, middle, upper = q(-3), q(0), q(4)
    expected = (
        count_real_roots_open(base, value, lower, middle)
        + count_real_roots_open(base, value, middle, upper)
        + (1 if evaluate(base, value, middle) == 0 else 0)
    )
    assert (
        count_real_roots_open(base, value, lower, upper) == expected
    )


def test_count_refuses_reversed_intervals():
    base = ring()
    with pytest.raises(RealRootFragmentError) as reversed_interval:
        count_real_roots_open(base, base.generator(0), q(1), q(-1))
    assert reversed_interval.value.missing == frozenset(
        {"ordered_endpoints"}
    )


def test_count_refuses_a_non_ordered_coefficient_field():
    outer_ring = UnivariatePolynomialRing(Y, RationalField())
    coefficients = RationalFunctionField(outer_ring)
    base = UnivariatePolynomialRing(X, coefficients)
    value = base.sub(
        base.pow(base.generator(0), 2),
        base.constant(coefficients.one()),
    )
    with pytest.raises(RealRootFragmentError) as not_ordered:
        count_real_roots_open(
            base, value, coefficients.zero(), coefficients.one()
        )
    assert not_ordered.value.missing == frozenset(
        {"ordered_coefficient_field"}
    )


class ParityField(Field[int]):
    """GF(2) as a test-only field of positive characteristic."""

    def zero(self) -> int:
        return 0

    def one(self) -> int:
        return 1

    def add(self, left: int, right: int) -> int:
        return (left + right) % 2

    def neg(self, value: int) -> int:
        return value

    def mul(self, left: int, right: int) -> int:
        return (left * right) % 2

    def contains(self, value: object) -> bool:
        return value in (0, 1)

    def equal(self, left: int, right: int) -> bool:
        return left == right

    def inv(self, value: int) -> int:
        if value == 0:
            raise ZeroDivisionError("zero has no inverse in GF(2)")
        return 1

    @property
    def characteristic(self) -> int:
        return 2


def test_sturm_chain_refuses_positive_characteristic():
    base = UnivariatePolynomialRing(SymbolId(3), ParityField())
    with pytest.raises(RealRootFragmentError) as positive:
        sturm_chain(base, base.generator(0))
    assert positive.value.missing == frozenset(
        {"characteristic_zero_field"}
    )
