"""Zero-to-zero power remains undecided in every channel."""

import pytest

from cas.api import domain_normal_form
from cas.frontend.parser import parse
from cas.math.domains.poly import from_term as poly_from_term
from cas.math.domains.q import Q_RING
from cas.math.domains.qarith import EvalNumError, eval_exact, fold
from cas.math.domains.ratfunc import rf_from_term
from cas.math.domains.z import Z_DOMAIN, Z_RING
from cas.math.project import project, zero_of
from cas.runtime import Runtime
from cas.syntax import term as T


def test_fold_keeps_zero_to_zero_interned(runtime: Runtime) -> None:
    assert fold(parse(runtime, "0^0")) is parse(runtime, "0^0")


def test_fold_nonzero_numeric_base_to_zero_is_one(runtime: Runtime) -> None:
    assert fold(parse(runtime, "2^0")) is T.ONE
    assert fold(parse(runtime, "(1/2)^0")) is T.ONE


def test_fold_symbolic_base_to_zero_stays_interned(runtime: Runtime) -> None:
    assert fold(parse(runtime, "x^0")) is parse(runtime, "x^0")


def test_eval_exact_refuses_zero_to_zero(runtime: Runtime) -> None:
    with pytest.raises(EvalNumError):
        eval_exact(parse(runtime, "0^0"), {})


def test_eval_exact_nonzero_to_zero_is_one(runtime: Runtime) -> None:
    from fractions import Fraction

    assert eval_exact(parse(runtime, "2^0"), {}) == Fraction(1)


def test_constant_domains_refuse_zero_to_zero(runtime: Runtime) -> None:
    assert Z_DOMAIN.member(parse(runtime, "0^0")) is False
    assert Z_DOMAIN.equal(parse(runtime, "0^0"), T.ONE) is None


def test_constant_domains_agree_on_nonzero_to_zero(runtime: Runtime) -> None:
    assert Z_DOMAIN.member(parse(runtime, "2^0")) is True
    assert Z_DOMAIN.equal(parse(runtime, "2^0"), T.ONE) is True


def test_poly_projection_refuses_zero_to_zero(runtime: Runtime) -> None:
    x = parse(runtime, "x")
    assert poly_from_term(Z_RING, parse(runtime, "0^0"), ()) is None
    assert poly_from_term(Z_RING, parse(runtime, "x + 0^0"), (x,)) is None


def test_ratfunc_projection_refuses_zero_to_zero(runtime: Runtime) -> None:
    x = parse(runtime, "x")
    assert rf_from_term(Q_RING, parse(runtime, "0^0"), (x,)) is None
    assert rf_from_term(Q_RING, parse(runtime, "x + 0^0"), (x,)) is None


def test_projection_misses_zero_to_zero(runtime: Runtime) -> None:
    assert project(runtime.math, parse(runtime, "0^0")) is None
    assert project(runtime.math, parse(runtime, "x + 0^0")) is None


def test_normal_form_leaves_zero_to_zero_in_place(runtime: Runtime) -> None:
    assert domain_normal_form(runtime, parse(runtime, "0^0")) is parse(
        runtime, "0^0"
    )
    assert domain_normal_form(runtime, parse(runtime, "x + 0^0")) is parse(
        runtime, "x + 0^0"
    )


def test_normal_form_folds_nonzero_to_zero(runtime: Runtime) -> None:
    assert domain_normal_form(runtime, parse(runtime, "2^0")) is T.ONE
    assert domain_normal_form(runtime, parse(runtime, "x^0")) is T.ONE


def test_zero_test_is_undecided_for_zero_to_zero_identity(runtime: Runtime) -> None:
    difference = T.plus(
        parse(runtime, "x + 0^0"),
        T.neg(parse(runtime, "x + 1")),
    )
    assert zero_of(runtime.math, difference) is None
