"""Exact ground evaluation and structural condition composition."""

from fractions import Fraction

from support import head_app

from cas.foundation.ids import SymbolId
from cas.language import sorts as S
from cas.language.signatures import StructuralHead
from cas.semantics.conditions import (
    and_all,
    condition_truth,
    equivalent,
    ground_value,
    implies,
    is_empty_condition,
    is_subregion,
    simplify,
)
from cas.semantics.symbols import SymbolTable, standard_language
from cas.syntax import term as T


def setup():
    table = SymbolTable()
    signature = standard_language(table)
    x = T.symbol(table.intern("x"), "x")
    return signature, x


class _OneSort:
    """One declared symbol and no others, for equality square facts."""

    def __init__(self, symbol: T.SymbolRef, sort: S.Sort) -> None:
        self._symbol = symbol.symbol_id
        self._sort = sort

    def sort_of(self, symbol_id: SymbolId) -> S.Sort | None:
        if symbol_id == self._symbol:
            return self._sort
        return None


def real_environment(x: T.SymbolRef) -> _OneSort:
    return _OneSort(x, S.REAL)


def complex_environment(x: T.SymbolRef) -> _OneSort:
    return _OneSort(x, S.COMPLEX)


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


def test_empty_regions_are_rejected_before_implication():
    signature, x = setup()
    gt = comparison(signature, StructuralHead.GT, x, T.number(0))
    contradictory = head_app(
        signature,
        StructuralHead.AND,
        gt,
        comparison(signature, StructuralHead.LT, x, T.number(0)),
    )
    assert is_empty_condition(T.FALSE, signature) is True
    assert is_empty_condition(contradictory, signature) is True
    assert is_empty_condition(gt, signature) is False
    assert is_subregion(T.FALSE, gt, signature) is False
    assert is_subregion(contradictory, gt, signature) is False
    assert is_subregion(gt, T.TRUE, signature) is True
    assert is_subregion(gt, contradictory, signature) is False


def test_region_inclusion_is_orientation_sensitive():
    signature, x = setup()
    gt = comparison(signature, StructuralHead.GT, x, T.number(0))
    ge = comparison(signature, StructuralHead.GE, x, T.number(0))
    assert is_subregion(gt, ge, signature) is True
    assert is_subregion(ge, gt, signature) is None
    assert is_subregion(gt, gt, signature) is True


def test_not_is_not_pushed_through_a_partial_comparison():
    signature, x = setup()
    partial = T.app(T.symbol(SymbolId(10_000), "f"), x)
    less = comparison(signature, StructuralHead.LT, partial, T.number(0))
    greater_equal = comparison(
        signature, StructuralHead.GE, partial, T.number(0)
    )
    negated = head_app(signature, StructuralHead.NOT, less)
    assert equivalent(negated, greater_equal, signature) is not True
    assert implies(negated, greater_equal, signature) is None


def test_not_is_not_pushed_through_a_zero_power_comparison():
    signature, x = setup()
    zero_power = head_app(
        signature, StructuralHead.POWER, x, T.number(0)
    )
    less = comparison(signature, StructuralHead.LT, zero_power, T.number(0))
    greater_equal = comparison(
        signature, StructuralHead.GE, zero_power, T.number(0)
    )
    negated = head_app(signature, StructuralHead.NOT, less)
    assert equivalent(negated, greater_equal, signature) is not True


def test_zero_to_the_zero_is_not_a_ground_value():
    signature, _ = setup()
    assert ground_value(
        head_app(signature, StructuralHead.POWER, T.number(0), T.number(0)),
        signature,
    ) is None
    assert ground_value(
        head_app(signature, StructuralHead.POWER, T.number(0), T.number(-1)),
        signature,
    ) is None
    assert ground_value(
        head_app(signature, StructuralHead.POWER, T.number(2), T.number(0)),
        signature,
    ) == 1


def test_a_ground_zero_product_with_a_partial_factor_is_not_absorbed():
    signature, x = setup()
    partial = T.app(T.symbol(SymbolId(10_000), "f"), x)
    zero_times_partial = head_app(
        signature, StructuralHead.TIMES, T.number(0), partial
    )
    with_partial = comparison(
        signature,
        StructuralHead.GT,
        head_app(
            signature, StructuralHead.PLUS, zero_times_partial, x
        ),
        T.number(0),
    )
    goal = comparison(signature, StructuralHead.GT, x, T.number(0))
    assert is_subregion(with_partial, goal, signature) is not True
    assert implies(with_partial, goal, signature) is not True
    assert is_empty_condition(with_partial, signature) is False


def test_a_ground_zero_product_of_total_factors_still_collapses():
    signature, x = setup()
    total = head_app(
        signature, StructuralHead.PLUS, x, T.number(1)
    )
    zero_times_total = head_app(
        signature, StructuralHead.TIMES, T.number(0), total
    )
    condition = comparison(
        signature,
        StructuralHead.GT,
        head_app(signature, StructuralHead.PLUS, zero_times_total, x),
        T.number(0),
    )
    goal = comparison(signature, StructuralHead.GT, x, T.number(0))
    assert equivalent(condition, goal, signature) is True


def square(signature, term):
    return head_app(
        signature, StructuralHead.POWER, term, T.number(2)
    )


def test_a_conjunction_proves_its_own_normalized_disequality():
    signature, x = setup()
    squared = square(signature, x)
    assumption = head_app(
        signature,
        StructuralHead.AND,
        comparison(signature, StructuralHead.NE, squared, T.number(1)),
        comparison(signature, StructuralHead.GT, x, T.number(1)),
    )
    shifted = head_app(
        signature, StructuralHead.PLUS, squared, T.number(-1)
    )
    assert implies(
        assumption,
        comparison(signature, StructuralHead.NE, shifted, T.number(0)),
        signature,
    ) is True
    assert implies(
        assumption,
        comparison(signature, StructuralHead.EQ, squared, T.number(1)),
        signature,
    ) is False


def test_a_positive_lower_bound_proves_square_facts():
    signature, x = setup()
    squared = square(signature, x)
    environment = real_environment(x)
    positive = comparison(signature, StructuralHead.GT, x, T.number(1))
    assert implies(
        positive,
        comparison(signature, StructuralHead.GT, squared, T.number(1)),
        signature,
        environment,
    ) is True
    assert implies(
        positive,
        comparison(signature, StructuralHead.NE, squared, T.number(1)),
        signature,
        environment,
    ) is True
    assert implies(
        positive,
        comparison(signature, StructuralHead.GT, squared, T.number(0)),
        signature,
        environment,
    ) is True
    nonnegative = comparison(
        signature, StructuralHead.GE, x, T.number(0)
    )
    assert implies(
        nonnegative,
        comparison(signature, StructuralHead.GE, squared, T.number(0)),
        signature,
        environment,
    ) is True
    assert implies(
        nonnegative,
        comparison(signature, StructuralHead.NE, squared, T.number(0)),
        signature,
        environment,
    ) is None


def test_a_negative_lower_bound_does_not_prove_a_square_lower_bound():
    signature, x = setup()
    squared = square(signature, x)
    environment = real_environment(x)
    negative = comparison(
        signature, StructuralHead.GT, x, T.number(-2)
    )
    assert implies(
        negative,
        comparison(signature, StructuralHead.GT, squared, T.number(4)),
        signature,
        environment,
    ) is None
    assert implies(
        negative,
        comparison(signature, StructuralHead.NE, squared, T.number(4)),
        signature,
        environment,
    ) is None
    assert implies(
        negative,
        comparison(signature, StructuralHead.GE, squared, T.number(0)),
        signature,
        environment,
    ) is True


def test_a_negative_upper_bound_proves_square_facts():
    signature, x = setup()
    squared = square(signature, x)
    environment = real_environment(x)
    strict = comparison(signature, StructuralHead.LT, x, T.number(-1))
    nonstrict = comparison(signature, StructuralHead.LE, x, T.number(-1))
    assert implies(
        strict,
        comparison(signature, StructuralHead.GT, squared, T.number(1)),
        signature,
        environment,
    ) is True
    assert implies(
        strict,
        comparison(signature, StructuralHead.NE, squared, T.number(1)),
        signature,
        environment,
    ) is True
    assert implies(
        nonstrict,
        comparison(signature, StructuralHead.GT, squared, T.number(1)),
        signature,
        environment,
    ) is None
    assert implies(
        nonstrict,
        comparison(signature, StructuralHead.NE, squared, T.number(1)),
        signature,
        environment,
    ) is None
    assert implies(
        nonstrict,
        comparison(signature, StructuralHead.GE, squared, T.number(1)),
        signature,
        environment,
    ) is True
    assert implies(
        strict,
        comparison(signature, StructuralHead.EQ, squared, T.number(1)),
        signature,
        environment,
    ) is False


def test_square_nonnegativity_is_exact_for_negative_bounds():
    signature, x = setup()
    squared = square(signature, x)
    environment = real_environment(x)
    assert condition_truth(
        comparison(signature, StructuralHead.GT, squared, T.number(-1)),
        signature,
        environment,
    ) is True
    assert condition_truth(
        comparison(signature, StructuralHead.NE, squared, T.number(-1)),
        signature,
        environment,
    ) is True
    assert condition_truth(
        comparison(signature, StructuralHead.LT, squared, T.number(-1)),
        signature,
        environment,
    ) is False
    assert condition_truth(
        comparison(signature, StructuralHead.LE, squared, T.number(-1)),
        signature,
        environment,
    ) is False
    assert condition_truth(
        comparison(signature, StructuralHead.EQ, squared, T.number(-1)),
        signature,
        environment,
    ) is False
    assert condition_truth(
        comparison(signature, StructuralHead.GT, squared, T.number(0)),
        signature,
        environment,
    ) is None
    positive = comparison(signature, StructuralHead.GT, x, T.number(1))
    assert and_all(
        signature,
        comparison(signature, StructuralHead.GT, squared, T.number(-1)),
        positive,
    ) == positive


def test_complex_square_equality_is_not_decided_by_real_nonnegativity():
    signature, x = setup()
    squared = square(signature, x)
    environment = complex_environment(x)
    equation = comparison(
        signature, StructuralHead.EQ, squared, T.number(-1)
    )
    disequation = comparison(
        signature, StructuralHead.NE, squared, T.number(-1)
    )
    assert condition_truth(equation, signature, environment) is None
    assert condition_truth(disequation, signature, environment) is None
    assert (
        condition_truth(
            comparison(
                signature, StructuralHead.GT, squared, T.number(-1)
            ),
            signature,
            environment,
        )
        is None
    )
    assert is_empty_condition(equation, signature, environment) is False
    assert (
        implies(
            comparison(signature, StructuralHead.NE, x, T.number(0)),
            disequation,
            signature,
            environment,
        )
        is not True
    )
    assert (
        is_subregion(
            T.TRUE, disequation, signature, environment
        )
        is not True
    )
    conjunction = and_all(
        signature, equation, comparison(
            signature, StructuralHead.NE, x, T.number(0)
        ), environment=environment
    )
    assert conjunction != T.FALSE
    real = real_environment(x)
    assert condition_truth(equation, signature, real) is False
    assert condition_truth(disequation, signature, real) is True


def test_square_facts_do_not_cross_atoms_or_partial_bases():
    signature, x = setup()
    y = T.symbol(SymbolId(10_000), "y")
    assert implies(
        comparison(signature, StructuralHead.GT, x, T.number(1)),
        comparison(
            signature, StructuralHead.GT, square(signature, y), T.number(1)
        ),
        signature,
    ) is None
    partial = T.app(T.symbol(SymbolId(10_001), "f"), x)
    assert condition_truth(
        comparison(
            signature, StructuralHead.GT, square(signature, partial), T.number(-1)
        ),
        signature,
    ) is None
def test_an_order_comparison_excludes_equality_for_compound_atoms():
    signature, x = setup()
    compound = head_app(
        signature,
        StructuralHead.PLUS,
        square(signature, x),
        x,
        T.number(1),
    )
    for head in (
        StructuralHead.GT,
        StructuralHead.LT,
    ):
        assert implies(
            comparison(signature, head, compound, T.number(0)),
            comparison(signature, StructuralHead.NE, compound, T.number(0)),
            signature,
        ) is True
    for head in (
        StructuralHead.GE,
        StructuralHead.LE,
    ):
        assert implies(
            comparison(signature, head, compound, T.number(0)),
            comparison(signature, StructuralHead.NE, compound, T.number(0)),
            signature,
        ) is not True
    assert implies(
        comparison(signature, StructuralHead.GT, T.number(0), compound),
        comparison(signature, StructuralHead.NE, compound, T.number(0)),
        signature,
    ) is True
    for head in (
        StructuralHead.GE,
        StructuralHead.LE,
    ):
        assert implies(
            comparison(signature, head, x, T.number(0)),
            comparison(signature, StructuralHead.NE, x, T.number(0)),
            signature,
        ) is not True
    other = head_app(
        signature,
        StructuralHead.PLUS,
        square(signature, x),
        T.number(-1),
    )
    assert implies(
        comparison(signature, StructuralHead.GT, compound, T.number(0)),
        comparison(signature, StructuralHead.NE, other, T.number(0)),
        signature,
    ) is None
