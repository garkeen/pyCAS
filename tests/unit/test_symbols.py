"""The session symbol table and the standard language signature."""

import pytest

from cas.language import sorts as S
from cas.language.signatures import OperatorSignature, StructuralHead
from cas.semantics.symbols import SymbolTable, standard_language


def test_intern_returns_a_stable_id_for_a_name():
    table = SymbolTable()
    first = table.intern("x")
    second = table.intern("x")
    assert first == second
    assert table.name_of(first) == "x"
    assert table.lookup("x") == first
    assert table.lookup("missing") is None
    assert len(table) == 1


def test_fresh_shadows_the_current_name_without_renaming_the_old_id():
    table = SymbolTable()
    old = table.intern("x")
    new = table.fresh("x")
    assert old != new
    assert table.intern("x") == new
    assert table.name_of(old) == "x"
    assert table.name_of(new) == "x"
    assert len(table) == 2


def test_names_must_not_be_empty():
    table = SymbolTable()
    with pytest.raises(ValueError):
        table.intern("")
    with pytest.raises(ValueError):
        table.fresh("")


def test_standard_language_interns_every_structural_head():
    table = SymbolTable()
    signature = standard_language(table)
    for head in StructuralHead:
        identifier = signature.symbol_of(head)
        assert identifier is not None
        assert table.name_of(identifier) == head.value
    assert len(table) == len(StructuralHead)


def test_standard_language_accepts_declared_operators():
    table = SymbolTable()
    predicate = table.intern("HasDerivative")
    declared = OperatorSignature((), S.PROPOSITION)
    signature = standard_language(table, operators={predicate: declared})
    assert signature.operator_of(predicate) == declared
    assert len(table) == len(StructuralHead) + 1
