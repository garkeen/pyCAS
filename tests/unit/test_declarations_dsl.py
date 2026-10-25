"""The data-only declaration DSL and its language builder."""

import pytest
from support import MapEnvironment, head_app

from cas.language import sorts as S
from cas.language import typing as Ty
from cas.language.declarations import (
    Compare,
    ConstantDeclaration,
    DeclarationError,
    DeclarationOrigin,
    DeclarationSet,
    FunctionDeclaration,
    Junction,
    LawDeclaration,
    Name,
    Num,
    Power,
    build_language,
    law_children,
    load_declarations,
    load_declarations_file,
)
from cas.language.signatures import OperatorSignature, StructuralHead
from cas.semantics.symbols import SymbolTable
from cas.syntax import term as T

TEXT = """
# language declarations
operator Sin (Real) -> Real
operator pi () -> Real

binder Lambda (Real) -> function
binder Integral (Real, Rational) -> Real
"""


def setup():
    declarations = load_declarations(TEXT)
    table = SymbolTable()
    signature = build_language(table.intern, declarations)
    environment = MapEnvironment()
    x = environment.declare(table.intern("x"), S.REAL)
    return declarations, table, signature, environment, x


def test_the_loader_keeps_declarations_and_ignores_comments_and_blanks():
    declarations, _, _, _, _ = setup()
    assert [operator.name for operator in declarations.operators] == [
        "Sin",
        "pi",
    ]
    sin, pi = declarations.operators
    assert sin.arguments == (S.REAL,) and sin.result is S.REAL
    assert pi.arguments == () and pi.result is S.REAL
    assert [binder.name for binder in declarations.binders] == [
        "Lambda",
        "Integral",
    ]
    lam, integral = declarations.binders
    assert lam.parameter_sorts == (S.REAL,) and lam.result is None
    assert lam.arity == 1
    assert integral.parameter_sorts == (S.REAL, S.RATIONAL)
    assert integral.result is S.REAL
    assert integral.arity == 2


def test_the_builder_integrates_operators_and_binders():
    _, table, signature, _, _ = setup()
    assert signature.head_of(table.lookup("Sin")) is None
    sin = signature.operator_of(table.lookup("Sin"))
    assert sin is not None
    assert sin.arguments == (S.REAL,) and sin.result is S.REAL
    pi = signature.operator_of(table.lookup("pi"))
    assert pi is not None and pi.arguments == ()
    binder = signature.binder_of("Lambda")
    assert binder is not None
    assert binder.arity == 1
    assert binder.parameter_sorts == (S.REAL,)
    assert binder.result is None
    integral = signature.binder_of("Integral")
    assert integral is not None
    assert integral.parameter_sorts == (S.REAL, S.RATIONAL)
    assert integral.result is S.REAL
    assert signature.symbol_of(StructuralHead.PLUS) is not None


def test_declared_operators_type_through_the_signature():
    _, table, signature, environment, x = setup()
    sin = T.symbol(table.lookup("Sin"), "Sin")
    assert Ty.infer(T.app(sin, T.number(1)), signature, environment) == Ty.Typed(
        S.REAL
    )
    assert isinstance(
        Ty.infer(T.app(sin, T.TRUE), signature, environment), Ty.IllTyped
    )
    pi = T.symbol(table.lookup("pi"), "pi")
    assert Ty.infer(T.app(pi), signature, environment) == Ty.Typed(S.REAL)
    assert isinstance(
        Ty.infer(T.app(pi, T.number(1)), signature, environment), Ty.IllTyped
    )
    unknown = T.app(T.symbol(table.intern("Other"), "Other"), T.number(1))
    assert isinstance(
        Ty.infer(unknown, signature, environment), Ty.NeedsDeclaration
    )


def test_declared_binders_type_through_the_signature():
    _, _, signature, environment, _ = setup()
    body = head_app(
        signature, StructuralHead.PLUS, T.BoundVar(0), T.number(1)
    )
    binder = T.binder("Lambda", 1, body)
    assert Ty.infer(binder, signature, environment) == Ty.Typed(
        S.FunctionSort((S.REAL,), S.REAL)
    )
    integral_body = T.binder(
        "Integral",
        2,
        head_app(
            signature,
            StructuralHead.PLUS,
            T.BoundVar(0),
            T.BoundVar(1),
        ),
    )
    assert Ty.infer(integral_body, signature, environment) == Ty.Typed(S.REAL)


def test_a_multi_argument_function_cannot_have_a_domain():
    with pytest.raises(DeclarationError) as caught:
        load_declarations("function F : Real, Real -> Real on u >= 0")
    assert "unary" in str(caught.value)


def test_an_empty_file_is_an_empty_declaration_set():
    declarations = load_declarations("# nothing\n\n")
    assert declarations.operators == ()
    assert declarations.binders == ()


def test_a_directly_constructed_declaration_set_is_validated():
    with pytest.raises(DeclarationError, match="duplicate"):
        DeclarationSet(
            constants=(ConstantDeclaration("a", S.REAL, 1),),
            functions=(
                FunctionDeclaration("a", (S.REAL,), S.REAL, None, 2),
            ),
        )
    with pytest.raises(DeclarationError, match="unknown function"):
        DeclarationSet(
            laws=(
                LawDeclaration(
                    "F", "u", Name("u"), None, DeclarationOrigin.BASIS, 1
                ),
            )
        )


def test_law_children_is_the_single_traversal_owner():
    u = Name("u")
    assert law_children(u) == ()
    assert law_children(Power(u, Num(2))) == (u, Num(2))
    assert law_children(Compare(">=", u, Num(0))) == (u, Num(0))


def test_constants_are_names_not_zero_arity_operators():
    declarations = load_declarations("constant q : Real")
    table = SymbolTable()
    signature = build_language(table.intern, declarations)
    assert signature.operator_of(table.intern("q")) is None


def test_the_builder_refuses_an_operator_that_reuses_a_constant_symbol():
    declarations = load_declarations("constant q : Real")
    table = SymbolTable()
    with pytest.raises(ValueError, match="constant"):
        build_language(
            table.intern,
            declarations,
            {table.intern("q"): OperatorSignature((), S.PROPOSITION)},
        )


def test_a_directly_constructed_law_body_must_use_a_known_connective():
    with pytest.raises(DeclarationError, match="logical connective"):
        DeclarationSet(
            functions=(
                FunctionDeclaration("F", (S.REAL,), S.REAL, None, 1),
            ),
            laws=(
                LawDeclaration(
                    "F",
                    "u",
                    Junction("xor", (Name("u"),)),
                    None,
                    DeclarationOrigin.BASIS,
                    2,
                ),
            ),
        )


def test_declarations_can_be_loaded_from_a_file(tmp_path):
    path = tmp_path / "language.dsl"
    path.write_text(TEXT, encoding="utf-8")
    declarations = load_declarations_file(path)
    assert [operator.name for operator in declarations.operators] == [
        "Sin",
        "pi",
    ]


@pytest.mark.parametrize(
    ("text", "line", "fragment"),
    [
        ("operator Sin Real -> Real", 1, "expected"),
        ("binder Lambda () -> function", 1, "at least one parameter"),
        ("operator F (Real) -> function", 1, "function-valued"),
        ("operator F (Real,) -> Real", 1, "empty parameter"),
        ("operator Plus (Real) -> Real", 1, "structural head"),
        ("operator F (Imaginary) -> Real", 1, "unknown sort"),
        (
            "operator F (Real) -> Real\noperator F (Real) -> Real",
            2,
            "duplicate",
        ),
        (
            "operator X (Real) -> Real\nbinder X (Real) -> function",
            2,
            "duplicate",
        ),
        ("operator F (Real) -> Real extra", 1, "expected"),
    ],
)
def test_declaration_errors_carry_a_line(text, line, fragment):
    with pytest.raises(DeclarationError) as caught:
        load_declarations(text)
    assert caught.value.line == line
    assert fragment in str(caught.value)


def test_comment_lines_do_not_shift_error_lines():
    text = "# heading\n\noperator F (Imaginary) -> Real\n"
    with pytest.raises(DeclarationError) as caught:
        load_declarations(text)
    assert caught.value.line == 3
