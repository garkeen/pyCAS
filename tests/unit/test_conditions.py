"""Exact ground evaluation and structural condition composition."""

from fractions import Fraction

from support import head_app

from cas.foundation.ids import SymbolId
from cas.language.signatures import StructuralHead
from cas.semantics.conditions import (
    and_all,
    condition_truth,
    equivalent,
    ground_value,
    implies,
    simplify,
)
from cas.semantics.symbols import SymbolTable, standard_language
from cas.syntax import term as T


def setup():
    table = SymbolTable()
    signature = standard_language(table)
    x = T.symbol(table.intern("x"), "x")
    return signature, x


def test_ground_values_are_exact():
    signature, _ = setup()
    assert ground_value(T.number(3), signature) == 3
    assert ground_value(T.number(Fraction(1, 2)), signature) == Fraction(1, 2)
    assert ground_value(T.TRUE, signature) is True
    assert ground_value(T.FALSE, signature) is False
    assert ground_value(
        head_app(signature, StructuralHead.PLUS, T.number(1), T.number(2)),
        signature,
    ) == 3
    assert ground_value(
        head_app(signature, StructuralHead.TIMES, T.number(2), T.number(3)),
        signature,
    ) == 6
    assert ground_value(
        head_app(signature, StructuralHead.POWER, T.number(2), T.number(3)),
        signature,
    ) == 8
    assert ground_value(
        head_app(signature, StructuralHead.POWER, T.number(2), T.number(-1)),
        signature,
    ) == Fraction(1, 2)
    assert (
        ground_value(
            head_app(
                signature, StructuralHead.POWER, T.number(0), T.number(-1)
            ),
            signature,
        )
        is None
    )


def test_comparisons_and_logic_are_three_valued():
    signature, x = setup()
    gt = head_app(signature, StructuralHead.GT, T.number(2), T.number(1))
    lt = head_app(signature, StructuralHead.LT, T.number(2), T.number(1))
    unknown = head_app(signature, StructuralHead.GT, x, T.number(0))
    assert condition_truth(gt, signature) is True
    assert condition_truth(lt, signature) is False
    assert condition_truth(unknown, signature) is None

    assert condition_truth(
        head_app(signature, StructuralHead.AND, T.FALSE, unknown), signature
    ) is False
    assert condition_truth(
        head_app(signature, StructuralHead.OR, T.TRUE, unknown), signature
    ) is True
    assert condition_truth(
        head_app(signature, StructuralHead.AND, T.TRUE, unknown), signature
    ) is None
    assert condition_truth(
        head_app(signature, StructuralHead.NOT, unknown), signature
    ) is None
    assert condition_truth(
        head_app(signature, StructuralHead.IMPLIES, T.FALSE, unknown),
        signature,
    ) is True


def test_and_all_folds_deduplicates_and_flattens():
    signature, x = setup()
    first = head_app(signature, StructuralHead.GT, x, T.number(0))
    second = head_app(signature, StructuralHead.GE, x, T.number(0))
    assert and_all(signature) == T.TRUE
    assert and_all(signature, None, T.TRUE) == T.TRUE
    assert and_all(signature, first) == first
    assert and_all(signature, first, first) == first
    assert and_all(signature, first, T.TRUE, second) == first
    assert and_all(
        signature,
        head_app(signature, StructuralHead.AND, first, second),
        first,
    ) == first
    assert and_all(signature, first, T.FALSE) == T.FALSE


def test_ground_conditions_collapse_in_conjunctions():
    signature, _ = setup()
    true_comparison = head_app(
        signature, StructuralHead.GE, T.number(1), T.number(0)
    )
    false_comparison = head_app(
        signature, StructuralHead.GT, T.number(0), T.number(0)
    )
    assert and_all(signature, true_comparison) == T.TRUE
    assert and_all(signature, false_comparison) == T.FALSE
    assert simplify(true_comparison, signature) == T.TRUE
    assert simplify(false_comparison, signature) == T.FALSE


def comparison(signature, head, left, right):
    return head_app(signature, head, left, right)


def test_bounds_are_normalized_and_contradictions_are_detected():
    signature, x = setup()
    assert and_all(
        signature,
        comparison(signature, StructuralHead.GE, x, T.number(0)),
        comparison(signature, StructuralHead.GT, x, T.number(0)),
    ) == comparison(signature, StructuralHead.GT, x, T.number(0))
    assert and_all(
        signature,
        comparison(signature, StructuralHead.GT, x, T.number(0)),
        comparison(signature, StructuralHead.LT, x, T.number(0)),
    ) == T.FALSE
    assert and_all(
        signature,
        comparison(signature, StructuralHead.GT, x, T.number(1)),
        comparison(signature, StructuralHead.LT, x, T.number(0)),
    ) == T.FALSE
    assert and_all(
        signature,
        comparison(signature, StructuralHead.EQ, x, T.number(0)),
        comparison(signature, StructuralHead.GT, x, T.number(0)),
    ) == T.FALSE
    assert and_all(
        signature,
        comparison(signature, StructuralHead.EQ, x, T.number(0)),
        comparison(signature, StructuralHead.EQ, x, T.number(1)),
    ) == T.FALSE
    assert and_all(
        signature,
        comparison(signature, StructuralHead.EQ, x, T.number(0)),
        comparison(signature, StructuralHead.NE, x, T.number(0)),
    ) == T.FALSE
    assert and_all(
        signature,
        comparison(signature, StructuralHead.GE, x, T.number(0)),
        comparison(signature, StructuralHead.LE, x, T.number(0)),
        comparison(signature, StructuralHead.NE, x, T.number(0)),
    ) == T.FALSE


def test_bounds_are_tightened_and_redundant_disequalities_are_dropped():
    signature, x = setup()
    gt = comparison(signature, StructuralHead.GT, x, T.number(0))
    ge = comparison(signature, StructuralHead.GE, x, T.number(0))
    assert and_all(signature, ge, gt) == gt
    assert and_all(
        signature, gt, comparison(signature, StructuralHead.NE, x, T.number(-1))
    ) == gt
    assert and_all(
        signature,
        comparison(signature, StructuralHead.GE, x, T.number(0)),
        comparison(signature, StructuralHead.LE, x, T.number(0)),
    ) == comparison(signature, StructuralHead.EQ, x, T.number(0))


def test_linear_expressions_normalize_to_the_same_bound():
    signature, x = setup()
    shifted = head_app(
        signature, StructuralHead.PLUS, x, T.number(1)
    )
    shifted_condition = comparison(
        signature, StructuralHead.GT, shifted, T.number(0)
    )
    direct = comparison(signature, StructuralHead.GT, x, T.number(-1))
    assert equivalent(shifted_condition, direct, signature) is True
    doubled = comparison(
        signature,
        StructuralHead.GT,
        head_app(signature, StructuralHead.TIMES, T.number(2), x),
        T.number(0),
    )
    assert equivalent(
        doubled, comparison(signature, StructuralHead.GT, x, T.number(0)),
        signature,
    ) is True
    assert equivalent(
        doubled, comparison(signature, StructuralHead.LT, x, T.number(0)),
        signature,
    ) is False
    negated = comparison(
        signature,
        StructuralHead.GT,
        head_app(signature, StructuralHead.TIMES, T.number(-1), x),
        T.number(0),
    )
    assert equivalent(
        negated, comparison(signature, StructuralHead.LT, x, T.number(0)),
        signature,
    ) is True


def test_restricted_implication_and_equivalence():
    signature, x = setup()
    y = T.symbol(SymbolId(10_000), "y")
    gt = comparison(signature, StructuralHead.GT, x, T.number(0))
    ge = comparison(signature, StructuralHead.GE, x, T.number(0))
    assert implies(gt, ge, signature) is True
    assert implies(ge, gt, signature) is None
    assert equivalent(gt, ge, signature) is None
    assert equivalent(
        head_app(signature, StructuralHead.AND, ge, gt), gt, signature
    ) is True
    assert implies(T.FALSE, gt, signature) is True
    assert implies(gt, T.TRUE, signature) is True
    assert implies(gt, T.FALSE, signature) is False
    assert equivalent(
        gt,
        comparison(signature, StructuralHead.GT, y, T.number(0)),
        signature,
    ) is None
    not_lt = head_app(
        signature,
        StructuralHead.NOT,
        comparison(signature, StructuralHead.LT, x, T.number(0)),
    )
    assert equivalent(not_lt, ge, signature) is True
    either = head_app(signature, StructuralHead.OR, ge, gt)
    assert implies(gt, either, signature) is True
    contradictory = head_app(
        signature,
        StructuralHead.AND,
        gt,
        comparison(signature, StructuralHead.LT, x, T.number(0)),
    )
    assert implies(contradictory, gt, signature) is True
    assert equivalent(contradictory, T.FALSE, signature) is True
