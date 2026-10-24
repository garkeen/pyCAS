"""Binder elaboration: declared parameter sorts, local indices and results."""


from support import MapEnvironment, head_app

from cas.foundation.ids import SymbolId, WorldId
from cas.language import sorts as S
from cas.language import typing as Ty
from cas.language.signatures import (
    BindingSignature,
    LanguageSignature,
    StructuralHead,
)
from cas.semantics.frames import Declaration, FrameSorts, FrameStore, World
from cas.semantics.symbols import SymbolTable
from cas.syntax import term as T


def setup():
    table = SymbolTable()
    signature = LanguageSignature.build(
        {table.intern(head.value): head for head in StructuralHead},
        binders={
            "Lambda": BindingSignature("Lambda", 1, (S.REAL,)),
            "Pair": BindingSignature("Pair", 2, (S.REAL, S.INTEGER)),
            "Integral": BindingSignature(
                "Integral", 1, (S.REAL,), S.REAL
            ),
            "Opaque": BindingSignature("Opaque", 1),
        },
    )
    environment = MapEnvironment()
    x = environment.declare(table.intern("x"), S.REAL)
    return table, signature, environment, x


def infer(term, signature, environment):
    return Ty.infer(term, signature, environment)


def plus(signature, *arguments):
    return head_app(signature, StructuralHead.PLUS, *arguments)


def test_a_free_bound_index_is_ill_typed():
    _, signature, environment, _ = setup()
    assert isinstance(infer(T.BoundVar(0), signature, environment), Ty.IllTyped)


def test_a_lambda_returns_a_function_sort():
    _, signature, environment, _ = setup()
    binder = T.binder(
        "Lambda",
        1,
        plus(signature, T.BoundVar(0), T.number(1)),
    )
    assert infer(binder, signature, environment) == Ty.Typed(
        S.FunctionSort((S.REAL,), S.REAL)
    )


def test_multi_parameter_binders_follow_declared_index_order():
    _, signature, environment, _ = setup()
    sum_body = T.binder(
        "Pair",
        2,
        plus(signature, T.BoundVar(0), T.BoundVar(1)),
    )
    assert infer(sum_body, signature, environment) == Ty.Typed(
        S.FunctionSort((S.REAL, S.INTEGER), S.REAL)
    )
    second = T.binder("Pair", 2, T.BoundVar(1))
    assert infer(second, signature, environment) == Ty.Typed(
        S.FunctionSort((S.REAL, S.INTEGER), S.INTEGER)
    )


def test_nested_binders_shift_outer_indices():
    _, signature, environment, _ = setup()
    inner = T.binder(
        "Lambda",
        1,
        plus(signature, T.BoundVar(1), T.BoundVar(0)),
    )
    outer = T.binder("Lambda", 1, inner)
    assert infer(outer, signature, environment) == Ty.Typed(
        S.FunctionSort(
            (S.REAL,),
            S.FunctionSort((S.REAL,), S.REAL),
        )
    )


def test_an_out_of_range_index_is_ill_typed():
    _, signature, environment, _ = setup()
    binder = T.binder("Lambda", 1, T.BoundVar(1))
    assert isinstance(infer(binder, signature, environment), Ty.IllTyped)


def test_a_value_binder_requires_the_body_to_embed_into_its_result():
    _, signature, environment, _ = setup()
    valid = T.binder("Integral", 1, T.BoundVar(0))
    assert infer(valid, signature, environment) == Ty.Typed(S.REAL)
    integer_body = T.binder("Integral", 1, T.number(1))
    assert infer(integer_body, signature, environment) == Ty.Typed(S.REAL)
    invalid = T.binder("Integral", 1, T.TRUE)
    assert isinstance(infer(invalid, signature, environment), Ty.IllTyped)


def test_binder_arity_must_match_the_declaration():
    _, signature, environment, _ = setup()
    binder = T.binder("Lambda", 2, T.BoundVar(0))
    assert isinstance(infer(binder, signature, environment), Ty.IllTyped)


def test_a_missing_binder_declaration_is_unsupported():
    _, signature, environment, _ = setup()
    binder = T.binder("Missing", 1, T.BoundVar(0))
    assert isinstance(infer(binder, signature, environment), Ty.Unsupported)


def test_a_declaration_without_parameter_sorts_is_unsupported():
    _, signature, environment, _ = setup()
    binder = T.binder("Opaque", 1, T.BoundVar(0))
    assert isinstance(infer(binder, signature, environment), Ty.Unsupported)


def test_annotations_are_typed_in_the_outer_context():
    table, signature, environment, _ = setup()
    valid = T.binder("Lambda", 1, T.BoundVar(0), T.number(1))
    assert infer(valid, signature, environment) == Ty.Typed(
        S.FunctionSort((S.REAL,), S.REAL)
    )
    foreign = T.symbol(SymbolId(10_000), "u")
    undeclared = T.binder("Lambda", 1, T.BoundVar(0), foreign)
    assert isinstance(
        infer(undeclared, signature, environment), Ty.NeedsDeclaration
    )
    escaping = T.binder("Lambda", 1, T.BoundVar(0), T.BoundVar(0))
    assert isinstance(infer(escaping, signature, environment), Ty.IllTyped)


def test_an_inner_annotation_may_use_an_outer_bound_variable():
    _, signature, environment, _ = setup()
    inner = T.binder("Lambda", 1, T.BoundVar(0), T.BoundVar(0))
    outer = T.binder("Lambda", 1, inner)
    assert infer(outer, signature, environment) == Ty.Typed(
        S.FunctionSort(
            (S.REAL,),
            S.FunctionSort((S.REAL,), S.REAL),
        )
    )


def test_binder_elaboration_works_with_a_frame_environment():
    table = SymbolTable()
    signature = LanguageSignature.build(
        {table.intern(head.value): head for head in StructuralHead},
        binders={"Lambda": BindingSignature("Lambda", 1, (S.REAL,))},
    )
    frames = FrameStore(World(WorldId(0), signature))
    x = table.intern("x")
    frame = frames.create(
        frames.root.id, declarations=(Declaration(x, "x", S.REAL),)
    )
    binder = T.binder(
        "Lambda",
        1,
        plus(signature, T.BoundVar(0), T.symbol(x, "x")),
    )
    assert Ty.infer(binder, signature, FrameSorts(frames, frame.id)) == Ty.Typed(
        S.FunctionSort((S.REAL,), S.REAL)
    )
