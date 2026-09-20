# -*- coding: utf-8 -*-
"""Nail tests for the zero-power edge case.

`0^0` is contentious and must be refused by every channel rather than silently
answered as 1; a nonzero numeric base to the zero is 1 and the constant domains'
member / normalize / equal trio must agree on both. These tests pin the fix so
the four channels (term fold, exact evaluation, polynomial projection,
rational-function projection) cannot silently diverge again.
"""

import pytest

from cas.runtime import bootstrap, get_runtime
from cas.runtime.dispatch import install
from cas.frontend.parser import parse
from cas.runtime.dispatch import domain_normal_form
from cas.math.domains.qarith import fold, eval_exact, EvalNumError
from cas.math.project import zero_of, project
from cas.math.domains.poly import from_term as poly_from_term
from cas.math.domains.ratfunc import rf_from_term
from cas.math.domains.z import Z_RING, Z_DOMAIN
from cas.math.domains.q import Q_RING
from cas.syntax import term as T

install(bootstrap())


def _ctx():
    """The installed math context: the projection channels read it explicitly."""
    return get_runtime().math


def _x():
    return parse("x")


def test_fold_keeps_zero_to_zero_interned():
    # 0^0 is contentious: the term layer leaves it for the domain layer.
    assert fold(parse("0^0")) is parse("0^0")


def test_fold_nonzero_numeric_base_to_zero_is_one():
    assert fold(parse("2^0")) is T.ONE
    assert fold(parse("(1/2)^0")) is T.ONE


def test_fold_symbolic_base_to_zero_stays_interned():
    # not an all-numeric subtree; the polynomial domain handles x^0 = 1.
    assert fold(parse("x^0")) is parse("x^0")


def test_eval_exact_refuses_zero_to_zero():
    with pytest.raises(EvalNumError):
        eval_exact(parse("0^0"), {})


def test_eval_exact_nonzero_to_zero_is_one():
    from fractions import Fraction as Fr
    assert eval_exact(parse("2^0"), {}) == Fr(1)


def test_constant_domains_refuse_zero_to_zero():
    assert Z_DOMAIN.member(parse("0^0")) is False
    assert Z_DOMAIN.equal(parse("0^0"), T.ONE) is None


def test_constant_domains_agree_on_nonzero_to_zero():
    assert Z_DOMAIN.member(parse("2^0")) is True
    assert Z_DOMAIN.equal(parse("2^0"), T.ONE) is True


def test_poly_projection_refuses_zero_to_zero():
    assert poly_from_term(Z_RING, parse("0^0"), ()) is None
    assert poly_from_term(Z_RING, parse("x + 0^0"), (_x(),)) is None


def test_ratfunc_projection_refuses_zero_to_zero():
    assert rf_from_term(Q_RING, parse("0^0"), (_x(),)) is None
    assert rf_from_term(Q_RING, parse("x + 0^0"), (_x(),)) is None


def test_projection_misses_zero_to_zero():
    # no projection hit: honestly undecided, never silently 1.
    assert project(_ctx(), parse("0^0")) is None
    assert project(_ctx(), parse("x + 0^0")) is None


def test_normal_form_leaves_zero_to_zero_in_place():
    assert domain_normal_form(parse("0^0")) is parse("0^0")
    assert domain_normal_form(parse("x + 0^0")) is parse("x + 0^0")


def test_normal_form_folds_nonzero_to_zero():
    assert domain_normal_form(parse("2^0")) is T.ONE
    assert domain_normal_form(parse("x^0")) is T.ONE


def test_zero_test_is_undecided_for_zero_to_zero_identity():
    # x + 0^0 is NOT provably equal to x + 1: zero_of is None (undecided),
    # never True. This is the regression the fix prevents.
    diff = T.plus(parse("x + 0^0"), T.neg(parse("x + 1")))
    assert zero_of(_ctx(), diff) is None
