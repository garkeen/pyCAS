"""Exact numeric rules shared by declaration and condition evaluation.

`0^0` and `0^negative` have no value in this language. Keeping the rule here
prevents the declaration loader and the condition service from drifting apart.
"""

from __future__ import annotations

from fractions import Fraction


def exact_power(base: Fraction, exponent: int) -> Fraction | None:
    """`base ** exponent`, or None for the undefined zero-power cases."""
    if base == 0 and exponent <= 0:
        return None
    return base**exponent


__all__ = ["exact_power"]
