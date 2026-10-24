"""Elementary declarations: data, domains, laws and their admission."""

from fractions import Fraction

import pytest
from support import elementary_basis, head_app

from cas.language import sorts as S
from cas.language.signatures import StructuralHead
from cas.math.calculus.differentiation.specification import DerivativeVocabulary
from cas.math.elementary.declarations import (
    ElementaryDeclarationError,
    ElementarySource,
    FunctionSource,
    LawOrigin,
    LawSource,
    Name,
    Num,
    Power,
    Product,
    build_elementary,
    default_elementary_source,
    load_elementary,
    load_elementary_file,
    numeric_value,
)
from cas.semantics.symbols import SymbolTable, standard_language
from cas.syntax import term as T


def setup(text=None):
    source = (
        default_elementary_source()
        if text is None
        else load_elementary(text, origin=LawOrigin.BASIS)
    )
    table = SymbolTable()
    predicate = table.intern("HasDerivative")
    vocabulary = DerivativeVocabulary(predicate, "HasDerivative")
    library = build_elementary(
        table.intern,
        source,
        reserved=frozenset({"x", "HasDerivative"}),
        basis=elementary_basis(source),
    )
    signature = standard_language(
        table,
        operators={predicate: vocabulary.signature, **library.operators},
    )
    return table, library, signature


def test_the_default_library_is_a_trusted_basis():
    source = default_elementary_source()
    assert [constant.name for constant in source.constants] == ["pi", "e"]
    assert [function.name for function in source.functions] == [
        "sin",
        "cos",
        "exp",
        "sqrt",
        "log",
    ]
    assert all(law.origin is LawOrigin.BASIS for law in source.laws)
    laws = {law.function: law for law in source.laws}
    assert laws["sin"].condition is None
    assert laws["cos"].condition is None
    assert laws["exp"].condition is None
    assert laws["sqrt"].condition is not None
    assert laws["log"].condition is not None


def test_function_domains_are_kept_as_conditions():
    source = default_elementary_source()
    functions = {function.name: function for function in source.functions}
    assert functions["sin"].domain is None
    assert functions["sqrt"].domain is not None
    assert functions["log"].domain is not None


def test_the_builder_keys_names_by_stable_ids():
    table, library, signature = setup()
    pi = library.constants["pi"]
    assert pi.symbol == table.lookup("pi")
    assert library.is_constant(pi.symbol)
    assert library.constant_for(pi.symbol) is pi
    assert table.name_of(pi.symbol) == "pi"

    sin = library.functions["sin"]
    assert sin.symbol == table.lookup("sin")
    assert library.function_for(sin.symbol) is sin
    assert signature.operator_of(sin.symbol) is not None
    assert signature.head_of(sin.symbol) is None
    assert sin.law is not None and sin.law.is_unconditional
    assert library.admissible_law(sin) is sin.law


def test_conditional_and_user_axiom_laws_are_not_admissible():
    text = """
function F : Real -> Real
derivative F(u) = 1 on u > 0
"""
    source = load_elementary(text, origin=LawOrigin.USER_AXIOM)
    table = SymbolTable()
    library = build_elementary(
        table.intern, source, reserved=frozenset({"x", "HasDerivative"})
    )
    function = library.functions["F"]
    assert function.law is not None
    assert function.law.origin is LawOrigin.USER_AXIOM
    assert library.admissible_law(function) is None

    text = """
function F : Real -> Real
derivative F(u) = 1 on u > 0
"""
    source = load_elementary(text, origin=LawOrigin.BASIS)
    table = SymbolTable()
    library = build_elementary(
        table.intern,
        source,
        reserved=frozenset({"x", "HasDerivative"}),
        basis=elementary_basis(source),
    )
    assert library.admissible_law(library.functions["F"]) is None


def test_declarations_can_be_loaded_from_a_file(tmp_path):
    path = tmp_path / "elementary.dsl"
    path.write_text(
        "constant q : Real\n"
        "function F : Real -> Real\n"
        "derivative F(u) = u\n",
        encoding="utf-8",
    )
    source = load_elementary_file(path, origin=LawOrigin.BASIS)
    assert [constant.name for constant in source.constants] == ["q"]
    assert [function.name for function in source.functions] == ["F"]
    assert [law.function for law in source.laws] == ["F"]


def test_an_empty_file_is_an_empty_source():
    source = load_elementary("# nothing\n\n")
    assert source.constants == ()
    assert source.functions == ()
    assert source.laws == ()


@pytest.mark.parametrize(
    ("text", "line", "fragment"),
    [
        ("constant q : Imaginary", 1, "unknown sort"),
        ("function F : Imaginary -> Real", 1, "unknown sort"),
        ("function F : Real -> Imaginary", 1, "unknown sort"),
        (
            "constant q : Real\nconstant q : Real",
            2,
            "duplicate declaration",
        ),
        (
            "function F : Real -> Real\nfunction F : Real -> Real",
            2,
            "duplicate declaration",
        ),
        ("function F Real -> Real", 1, "expected"),
        ("derivative F(u) =", 1, "expected"),
        ("derivative F(u) = u^", 1, "expected"),
        ("function F : Real -> Real on u >", 1, "expected"),
    ],
)
def test_loader_errors_carry_a_line(text, line, fragment):
    with pytest.raises(ElementaryDeclarationError) as caught:
        load_elementary(text)
    assert caught.value.line == line
    assert fragment in str(caught.value)


def build(text, *, origin=LawOrigin.BASIS):
    source = load_elementary(text, origin=origin)
    table = SymbolTable()
    basis = (
        elementary_basis(source)
        if any(law.origin is LawOrigin.BASIS for law in source.laws)
        else None
    )
    return table, build_elementary(
        table.intern,
        source,
        reserved=frozenset({"x", "HasDerivative"}),
        basis=basis,
    )


@pytest.mark.parametrize(
    ("text", "fragment"),
    [
        (
            "function F : Real -> Real\n"
            "derivative G(u) = u",
            "unknown function",
        ),
        (
            "function F : Real -> Real\n"
            "derivative F(u) = H(u)",
            "unknown function",
        ),
        (
            "function F : Real -> Real\n"
            "derivative F(u) = q",
            "unknown name",
        ),
        (
            "function F : Real -> Real\n"
            "derivative F(u) = u^v",
            "exponent",
        ),
        (
            "function F : Real -> Real\n"
            "derivative F(u) = u\n"
            "derivative F(u) = u",
            "duplicate derivative law",
        ),
        (
            "function F : Real -> Real\n"
            "derivative F(u) = F(u, u)",
            "takes 1 arguments",
        ),
        (
            "function F : Real -> Real on v > 0\n"
            "derivative F(u) = u",
            "unknown name",
        ),
        (
            "function u : Real -> Real\n"
            "function F : Real -> Real\n"
            "derivative F(u) = u",
            "fresh law argument",
        ),
        (
            "function F : Real -> Real\n"
            "derivative F(u) = u^(-1)",
            "negative or non-integral",
        ),
        (
            "function F : Real -> Real\n"
            "derivative F(u) = u^(1/2)",
            "non-integral",
        ),
        (
            "function G : Real -> Real on u >= 0\n"
            "function F : Real -> Real\n"
            "derivative F(u) = G(u)",
            "outside its declared domain",
        ),
    ],
)
def test_build_errors_are_explicit(text, fragment):
    with pytest.raises(ElementaryDeclarationError) as caught:
        build(text)
    assert fragment in str(caught.value)


def test_a_reserved_name_is_refused():
    with pytest.raises(ValueError):
        build("function Plus : Real -> Real")
    with pytest.raises(ValueError):
        build("constant x : Real")
    with pytest.raises(ValueError):
        build("function HasDerivative : Real -> Real")


def test_a_binary_function_cannot_have_a_unary_law():
    source = ElementarySource(
        constants=(),
        functions=(
            FunctionSource(
                "F", (S.REAL, S.REAL), S.REAL, None, 1
            ),
        ),
        laws=(
            LawSource(
                "F", "u", Name("u"), None, LawOrigin.BASIS, 2
            ),
        ),
    )
    table = SymbolTable()
    with pytest.raises(ElementaryDeclarationError) as caught:
        build_elementary(table.intern, source)
    assert "unary" in str(caught.value)


def test_instantiation_builds_terms_and_conditions():
    table, library, signature = setup()
    x = T.symbol(table.intern("x"), "x")
    sin_law = library.functions["sin"].law
    assert sin_law is not None
    body = library.instantiate(
        sin_law.body, sin_law.argument, x, signature
    )
    cos = library.functions["cos"]
    assert body == T.app(T.symbol(cos.symbol, cos.name), x)

    sqrt_law = library.functions["sqrt"].law
    assert sqrt_law is not None and sqrt_law.condition is not None
    conditional_body = library.instantiate(
        sqrt_law.body, sqrt_law.argument, x, signature
    )
    assert conditional_body.operator.symbol_id == signature.symbol_of(
        StructuralHead.TIMES
    )
    condition = library.instantiate(
        sqrt_law.condition, sqrt_law.argument, x, signature
    )
    assert condition == head_app(
        signature, StructuralHead.GT, x, T.number(0)
    )


def test_numeric_value_is_exact():
    body = load_elementary(
        "function F : Real -> Real\n"
        "derivative F(u) = u"
    ).laws[0].body
    assert body == Name("u")
    assert numeric_value(Num(3)) == 3
    assert numeric_value(Product((Num(3), Num(2)))) == 6
    assert numeric_value(Power(Num(2), Num(-1))) == Fraction(1, 2)
    assert numeric_value(
        Power(Num(2), Num(Fraction(1, 2)))
    ) is None
    assert numeric_value(
        Product((Num(1), Power(Num(2), Num(-1))))
    ) == Fraction(1, 2)
    assert numeric_value(Name("u")) is None


def test_a_basis_reference_must_match_the_loaded_source():
    from cas.foundation.ids import WorldId
    from cas.kernel.model import BasisKind, BasisRef

    text = "function F : Real -> Real\nderivative F(u) = 1\n"
    source = load_elementary(
        text, origin=LawOrigin.BASIS, source_name="test.dsl"
    )
    assert source.name == "test.dsl"
    assert len(source.digest) == 64
    basis = BasisRef(
        source.name,
        BasisKind.DECLARATION_FILE,
        "1",
        source.digest,
        WorldId(0),
    )
    table = SymbolTable()
    library = build_elementary(table.intern, source, basis=basis)
    assert library.basis is basis

    wrong = BasisRef(
        source.name,
        BasisKind.DECLARATION_FILE,
        "1",
        "0" * 64,
        WorldId(0),
    )
    with pytest.raises(ValueError):
        build_elementary(table.intern, source, basis=wrong)


def test_a_source_without_a_digest_cannot_become_a_basis():
    from cas.foundation.ids import WorldId
    from cas.kernel.model import BasisKind, BasisRef

    source = ElementarySource((), (), ())
    basis = BasisRef(
        "test.dsl", BasisKind.DECLARATION_FILE, "1", "digest", WorldId(0)
    )
    table = SymbolTable()
    with pytest.raises(ValueError):
        build_elementary(table.intern, source, basis=basis)


def test_a_basis_law_cannot_be_built_without_an_admitted_basis():
    source = load_elementary(
        "function F : Real -> Real\n"
        "derivative F(u) = 1\n",
        origin=LawOrigin.BASIS,
    )
    table = SymbolTable()
    with pytest.raises(ValueError, match="BasisRef"):
        build_elementary(table.intern, source)
