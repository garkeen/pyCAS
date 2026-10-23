"""Binding: de Bruijn shifting, instantiation, abstraction and substitution."""

import pytest

from cas.foundation.ids import SymbolId
from cas.syntax import binding as B
from cas.syntax import term as T

X = SymbolId(1)
Y = SymbolId(2)
Z = SymbolId(3)
F = SymbolId(99)


def x(name: str = "x") -> T.SymbolRef:
    return T.symbol(X, name)


def y(name: str = "y") -> T.SymbolRef:
    return T.symbol(Y, name)


def f(*arguments: T.Term) -> T.Apply:
    return T.app(T.symbol(F, "f"), *arguments)


# --- shift -----------------------------------------------------------------


def test_shift_moves_indices_at_or_above_the_cutoff():
    assert B.shift(T.BoundVar(0), 2) == T.BoundVar(2)
    assert B.shift(T.BoundVar(1), 1, cutoff=1) == T.BoundVar(2)


def test_shift_leaves_indices_below_the_cutoff_alone():
    variable = T.BoundVar(0)
    assert B.shift(variable, 1, cutoff=1) is variable


def test_shift_raises_on_a_negative_result():
    with pytest.raises(ValueError):
        B.shift(T.BoundVar(0), -1)


def test_shift_zero_returns_the_same_object():
    term = f(x(), T.BoundVar(0))
    assert B.shift(term, 0) is term


def test_shift_respects_binder_depth_and_annotations():
    term = T.binder("Sum", 1, f(T.BoundVar(0), T.BoundVar(1)), T.BoundVar(0))
    shifted = B.shift(term, 1)
    assert isinstance(shifted, T.Binder)
    # the body's #0 is bound by the binder and stays put; #1 is free and moves
    assert shifted.body == f(T.BoundVar(0), T.BoundVar(2))
    # annotations live in the outer context, so their #0 moves
    assert shifted.annotations[0] == T.BoundVar(1)


def test_shift_preserves_untouched_structure_by_identity():
    term = f(x(), T.number(1))
    assert B.shift(term, 1) is term


# --- instantiate -----------------------------------------------------------


def test_instantiate_replaces_the_bound_variable():
    binder = T.binder("Lam", 1, f(T.BoundVar(0)))
    assert B.instantiate(binder, (T.number(5),)) == f(T.number(5))


def test_instantiate_drops_an_unused_variable():
    binder = T.binder("Lam", 1, x())
    assert B.instantiate(binder, (T.number(5),)) is binder.body


def test_instantiate_checks_the_argument_count():
    binder = T.binder("Lam", 1, T.BoundVar(0))
    with pytest.raises(ValueError):
        B.instantiate(binder, ())


def test_instantiate_shifts_under_a_nested_binder():
    nested = T.binder(
        "Outer",
        1,
        T.binder("Inner", 1, f(T.BoundVar(1), T.BoundVar(0))),
    )
    result = B.instantiate(nested, (T.BoundVar(0),))
    assert isinstance(result, T.Binder)
    # the substituted variable now lives one binder deeper
    assert result.body == f(T.BoundVar(1), T.BoundVar(0))
    assert not B.well_scoped(result)


def test_instantiate_handles_multiple_variables_and_inner_binders():
    binder = T.binder("Pair", 2, T.BoundVar(0))
    assert B.instantiate(binder, (x(), y())) == x()

    nested = T.binder(
        "Pair",
        2,
        T.binder("Mu", 1, f(T.BoundVar(2), T.BoundVar(0))),
    )
    result = B.instantiate(nested, (x(), y()))
    assert isinstance(result, T.Binder)
    assert result.body == f(y(), T.BoundVar(0))


# --- abstract --------------------------------------------------------------


def test_abstract_binds_the_listed_symbols_in_order():
    term = f(x(), f(y(), x()))
    assert B.abstract(term, (X, Y)) == f(
        T.BoundVar(0), f(T.BoundVar(1), T.BoundVar(0))
    )


def test_abstract_raises_depth_under_a_binder():
    term = T.binder("Lam", 1, f(x(), T.BoundVar(0)))
    abstracted = B.abstract(term, (X,))
    assert isinstance(abstracted, T.Binder)
    assert abstracted.body == f(T.BoundVar(1), T.BoundVar(0))


def test_abstract_evaluates_annotations_at_the_outer_depth():
    term = T.binder("Ann", 1, x(), x())
    abstracted = B.abstract(term, (X,))
    assert isinstance(abstracted, T.Binder)
    # the body sees the binder's own variable at #0, so the free x is #1;
    # the annotation sees the outer context, where the same x is #0
    assert abstracted.body == T.BoundVar(1)
    assert abstracted.annotations[0] == T.BoundVar(0)


def test_abstract_with_no_symbols_returns_the_same_object():
    term = f(x())
    assert B.abstract(term, ()) is term


def test_abstract_then_instantiate_round_trips():
    term = f(x(), y())
    body = B.abstract(term, (X, Y))
    binder = T.binder("Pair", 2, body)
    assert B.instantiate(binder, (x(), y())) == term


# --- free substitution -----------------------------------------------------


def test_substitute_free_is_simultaneous():
    term = f(x(), y())
    assert B.substitute_free(term, {X: y(), Y: x()}) == f(y(), x())


def test_substitute_free_does_not_revisit_inserted_terms():
    assert B.substitute_free(x(), {X: y(), Y: x()}) == y()


def test_substitute_free_shifts_inserted_terms_under_binders():
    term = T.binder("Lam", 1, f(T.BoundVar(0), x()))
    replaced = B.substitute_free(term, {X: T.BoundVar(0)})
    assert isinstance(replaced, T.Binder)
    assert replaced.body == f(T.BoundVar(0), T.BoundVar(1))


def test_substitute_free_treats_annotations_at_the_outer_depth():
    term = T.binder("Ann", 1, x(), x())
    replaced = B.substitute_free(term, {X: T.BoundVar(0)})
    assert isinstance(replaced, T.Binder)
    assert replaced.body == T.BoundVar(1)
    assert replaced.annotations[0] == T.BoundVar(0)


def test_substitute_free_with_an_empty_mapping_returns_the_same_object():
    term = f(x())
    assert B.substitute_free(term, {}) is term


# --- free symbols and scope ------------------------------------------------


def test_free_symbols_include_operators_arguments_and_annotations():
    term = T.binder("Ann", 1, f(x()), y())
    assert B.free_symbols(term) == frozenset({F, X, Y})


def test_free_symbols_exclude_bound_variables_and_quoted_content():
    term = T.binder("Lam", 1, f(T.BoundVar(0)))
    assert B.free_symbols(term) == frozenset({F})
    quoted = T.quote(f(x(), T.BoundVar(0)))
    assert B.free_symbols(quoted) == frozenset()


def test_well_scoped_accepts_bound_indices_and_rejects_escapes():
    assert B.well_scoped(T.binder("Lam", 1, T.BoundVar(0)))
    assert not B.well_scoped(T.BoundVar(0))
    assert B.well_scoped(T.BoundVar(0), depth=1)
    nested = T.binder("Outer", 1, T.binder("Inner", 1, T.BoundVar(1)))
    assert B.well_scoped(nested)


def test_well_scoped_checks_annotations_at_the_outer_depth():
    invalid = T.binder("Ann", 1, x(), T.BoundVar(0))
    assert not B.well_scoped(invalid)
    valid = T.binder("Outer", 1, T.binder("Ann", 1, x(), T.BoundVar(0)))
    assert B.well_scoped(valid)


def test_quoted_content_is_inert_for_every_binding_operation():
    quoted = T.quote(f(x(), T.BoundVar(0)))
    assert B.shift(quoted, 1) is quoted
    assert B.abstract(quoted, (X,)) is quoted
    assert B.substitute_free(quoted, {X: y()}) is quoted
    assert B.well_scoped(quoted)
