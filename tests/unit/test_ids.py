"""Issuer behavior: monotone ids, one namespace stream per owner."""

import pytest

from cas.foundation.ids import IdIssuer


def test_issuer_starts_at_zero_and_is_monotone():
    issuer = IdIssuer()
    assert issuer.issued == 0
    assert [issuer.issue() for _ in range(3)] == [0, 1, 2]
    assert issuer.issued == 3


def test_issuer_honours_an_explicit_start():
    issuer = IdIssuer(10)
    assert issuer.issue() == 10
    assert issuer.issued == 11


def test_issuer_refuses_a_negative_start():
    with pytest.raises(ValueError):
        IdIssuer(-1)


def test_issuers_are_independent():
    first = IdIssuer()
    second = IdIssuer()
    first.issue()
    first.issue()
    assert second.issue() == 0
