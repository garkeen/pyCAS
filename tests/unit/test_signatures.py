"""The structural language signature and its arity records."""

import pytest

from cas.foundation.ids import SymbolId
from cas.language import sorts as S
from cas.language.signatures import (
    Arity,
    BindingSignature,
    LanguageSignature,
    OperatorSignature,
    StructuralHead,
)
from cas.semantics.symbols import SymbolTable, standard_language


def test_every_structural_head_has_exactly_one_symbol():
    table = SymbolTable()
    signature = standard_language(table)
    identifiers = []
    for head in StructuralHead:
        identifier = signature.symbol_of(head)
        assert identifier is not None
        assert signature.head_of(identifier) is head
        identifiers.append(identifier)
    assert len(set(identifiers)) == len(StructuralHead)
    assert len(signature.heads) == len(StructuralHead)


def test_unknown_symbols_have_no_head_and_unknown_heads_have_no_symbol():
    signature = standard_language(SymbolTable())
    assert signature.head_of(SymbolId(10_000)) is None
    bare = LanguageSignature.build({})
    assert bare.symbol_of(StructuralHead.PLUS) is None


def test_structural_arities():
    signature = standard_language(SymbolTable())
    plus = signature.arity_of(StructuralHead.PLUS)
    assert plus.minimum == 2 and plus.maximum is None
    assert plus.accepts(2) and plus.accepts(7) and not plus.accepts(1)
    power = signature.arity_of(StructuralHead.POWER)
    assert power.accepts(2) and not power.accepts(3)
    assert power.describe() == "exactly 2 arguments"
    assert Arity(1, 1).describe() == "exactly 1 arguments"


def test_arity_validates_its_range():
    with pytest.raises(ValueError):
        Arity(0)
    with pytest.raises(ValueError):
        Arity(2, 1)
    assert Arity(2, 4).describe() == "2..4 arguments"


def test_binding_signature_validates_its_shape():
    signature = BindingSignature("Integral", 1)
    assert signature.arity == 1
    with pytest.raises(ValueError):
        BindingSignature("", 1)
    with pytest.raises(ValueError):
        BindingSignature("Integral", 0)


def test_binding_signature_can_declare_parameter_sorts_and_result():
    function_binder = BindingSignature("Lambda", 1, (S.REAL,))
    assert function_binder.parameter_sorts == (S.REAL,)
    assert function_binder.result is None
    value_binder = BindingSignature("Integral", 1, (S.REAL,), S.REAL)
    assert value_binder.result is S.REAL
    with pytest.raises(ValueError):
        BindingSignature("Pair", 2, (S.REAL,))


def test_binders_are_looked_up_by_name():
    built = LanguageSignature.build(
        {}, binders={"Integral": BindingSignature("Integral", 1)}
    )
    assert built.binder_of("Integral") is not None
    assert built.binder_of("Missing") is None


def test_declared_operator_signatures_are_looked_up_by_symbol():
    table = SymbolTable()
    predicate = table.intern("Prime")
    signature = standard_language(
        table,
        operators={predicate: OperatorSignature((S.INTEGER,), S.PROPOSITION)},
    )
    assert signature.operator_of(predicate) == OperatorSignature(
        (S.INTEGER,), S.PROPOSITION
    )
    assert signature.operator_of(table.intern("Other")) is None


def test_the_signature_copies_its_input_mappings():
    head_id = SymbolId(1)
    heads = {head_id: StructuralHead.PLUS}
    built = LanguageSignature.build(heads)
    heads[head_id] = StructuralHead.TIMES
    assert built.head_of(head_id) is StructuralHead.PLUS


def test_signature_tables_are_read_only():
    signature = standard_language(SymbolTable())
    with pytest.raises(TypeError):
        signature.heads[SymbolId(10_000)] = StructuralHead.PLUS
