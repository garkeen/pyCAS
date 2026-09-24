# -*- coding: utf-8 -*-
"""Surface names are declared data, and the source form re-parses.

Nails:
1. The parser capitalized a multi-letter lowercase word (`foo(x)` became `Foo`), so
   `foo` and `Foo` could never be two different heads and a DSL `function foo`
   declaration was unreachable from the surface syntax.
2. The bound-form heads were a set inside the parser, so a word other than
   integrate/Integrate was never bound and a newly declared binder was impossible.
3. `to_str(..., src=True)` promised a re-parseable source form while it lowercased an
   undeclared head and emitted container notation the lexer rejects.
4. The printer still held a table of binder heads and their surface words, so the
   source form of a merely declared binder lost its binding and a renamed surface
   word printed a dead word; binder rendering now asks the runtime, and the source
   form is the canonical head with body and variable.

The inventory walk at the end lists every spelling the source form emits together
with the declared route that maps it back. Notation has two boundaries and both are
pinned below instead of being hidden: an atom the lexer has no notation for (the empty
solution set) re-parses as a parse refusal, and a literal the grammar writes with an
operator (a rational, a negated exponent) rebuilds the un-folded literal shape, which
the numeric folding layer collapses back to the exact term.
"""

from fractions import Fraction as Fr

import pytest

from cas.errors import ParseError
from cas.frontend.parser import parse
from cas.frontend.pprint import to_str
from cas.math.domains.qarith import fold
from cas.math.loader import parse_declarations
from cas.runtime import bootstrap
from cas.syntax import term as T
from cas.syntax.parse import Parser, tokenize
from cas.syntax.term import Bound, C, N, S, mk

RUNTIME = bootstrap()


X = S("x")


def _head(t):
    return t.head.name


# ---------------------------------------------------------------------------
# 1. No implicit case rewriting
# ---------------------------------------------------------------------------

def test_multi_letter_lowercase_word_is_not_capitalized():
    assert _head(parse(RUNTIME, "foo(x)")) == "foo"
    assert _head(parse(RUNTIME, "Foo(x)")) == "Foo"
    assert parse(RUNTIME, "foo(x)") != parse(RUNTIME, "Foo(x)")


def test_single_letter_case_is_still_distinct():
    assert _head(parse(RUNTIME, "f(x)")) == "f"
    assert _head(parse(RUNTIME, "F(x)")) == "F"
    assert parse(RUNTIME, "f(x)") != parse(RUNTIME, "F(x)")


def test_case_variant_of_a_declared_name_is_not_that_name():
    """Only the declared surface word resolves: `Ln`/`SQRT` are heads of their own,
    not spellings of Log/Sqrt."""
    assert _head(parse(RUNTIME, "ln(x)")) == "Log"
    assert _head(parse(RUNTIME, "Ln(x)")) == "Ln"
    assert _head(parse(RUNTIME, "sqrt(x)")) == "Sqrt"
    assert _head(parse(RUNTIME, "SQRT(x)")) == "SQRT"


def test_dsl_declared_lowercase_head_is_reachable():
    """A declared head is spelled exactly as declared, so the surface word of a
    `function foo` declaration reaches the declared head."""
    d = parse_declarations('function foo print "foo" arity 1')
    name = d.functions[0].name
    assert name == "foo"
    assert _head(parse(RUNTIME, f"{name}(x)")) == name


# ---------------------------------------------------------------------------
# 2. Declared surface names resolve to canonical heads
# ---------------------------------------------------------------------------

def test_declared_surface_names_resolve_to_canonical_heads():
    for word, head in [("sin", "Sin"), ("cos", "Cos"), ("tan", "Tan"),
                       ("sinh", "Sinh"), ("cosh", "Cosh"), ("tanh", "Tanh"),
                       ("exp", "Exp"), ("log", "Log"), ("ln", "Log"),
                       ("sqrt", "Sqrt"), ("abs", "Abs"), ("atan", "Atan")]:
        assert RUNTIME.alias_head(word) == head, word
        assert _head(parse(RUNTIME, f"{word}(x)")) == head, word


def test_binder_words_produce_bound_forms():
    for word, head in [("integrate", "Integrate"), ("sum", "Sum"),
                       ("product", "Product"), ("limit", "Limit")]:
        t = parse(RUNTIME, f"{word}(x^2, x)")
        assert _head(t) == head and len(t.args) == 1, word
        assert isinstance(t.args[0], Bound), word
        var, body = T.open_bound(t.args[0])
        assert var.name == "x" and body is parse(RUNTIME, "x^2"), word
        # the canonical spelling is the same declared binder, not a second table
        assert parse(RUNTIME, f"{head}(x^2, x)") == t, word


def test_undeclared_case_variant_is_not_a_binder_word():
    t = parse(RUNTIME, "INTEGRATE(x^2, x)")
    assert _head(t) == "INTEGRATE" and len(t.args) == 2


def test_binder_table_is_declaration_data():
    """A binder declared in DSL text is recognized: the syntax layer receives the
    query by injection, so it holds no binder list of its own."""
    d = parse_declarations("binder Frobnicate")
    assert tuple(record.head for record in d.binders) == ("Frobnicate",)
    binders = {record.head for record in d.binders}
    body, var = parse(RUNTIME, "x^2"), S("x")
    bound = Parser(tokenize("Frobnicate(x^2, x)"),
                   binder_fn=lambda name: name in binders).parse()
    assert _head(bound) == "Frobnicate"
    assert bound.args[0] == T.mk_bound(var, body)
    # with no declaration the same word is an ordinary call
    plain = Parser(tokenize("Frobnicate(x^2, x)")).parse()
    assert _head(plain) == "Frobnicate" and len(plain.args) == 2


def test_definite_integral_word_binds_body_and_limits():
    """The extra arguments of a bound word follow the bound body, which is how the
    definite integral re-parses to a three-argument term."""
    t = parse(RUNTIME, "int(x^2, x, 0, 1)")
    assert _head(t) == "DefIntegrate" and len(t.args) == 3
    var, body = T.open_bound(t.args[0])
    assert var.name == "x" and body is parse(RUNTIME, "x^2")
    assert t.args[1:] == (N(0), N(1))


def test_runtime_exposes_declared_binders():
    assert RUNTIME.is_binder("Integrate") is True
    assert RUNTIME.is_binder("DefIntegrate") is True
    assert RUNTIME.is_binder("Sin") is False
    assert RUNTIME.is_binder("__nope__") is False


def test_declared_binder_source_form_round_trips():
    """A declared binder keeps its binding in the reparsable source form."""
    x = X
    body = parse(RUNTIME, "x^2")
    t = mk(S("Integrate"), (T.mk_bound(x, body),))
    assert to_str(RUNTIME, t, src=True) == "Integrate(x^2, x)"
    assert parse(RUNTIME, to_str(RUNTIME, t, src=True)) == t
    assert parse(RUNTIME, "integrate(x^2, x)") == t
    # An undeclared head has no notation that could re-parse a binding.
    plain = mk(S("Wibble"), (T.mk_bound(x, body),))
    assert to_str(RUNTIME, plain, src=True) == "Wibble(@0^2)"
    assert parse(RUNTIME, to_str(RUNTIME, plain, src=True)) != plain


def test_canonical_binder_alias_still_produces_a_re_parsable_form():
    """The source form uses the canonical head, while the declared alias parses too."""
    x = X
    body = parse(RUNTIME, "x^2")
    t = mk(S("Integrate"), (T.mk_bound(x, body),))
    out = to_str(RUNTIME, t, src=True)
    assert out == "Integrate(x^2, x)"
    assert parse(RUNTIME, out) == t
    assert parse(RUNTIME, "integrate(x^2, x)") == t


def test_declared_binder_display_keeps_the_friendly_symbols():
    """Display mode is presentation, not the source promise: the traditional
    symbols and the definite-integral limits form stay."""
    x = X
    body = mk(S("Sin"), (x,))
    for head, want in (("Integrate", "∫[sin(x)] dx"), ("Sum", "Σ[sin(x)] dx"),
                       ("Product", "Π[sin(x)] dx"), ("Limit", "lim[sin(x)] dx")):
        assert to_str(RUNTIME, mk(S(head), (T.mk_bound(x, body),))) == want, head
    def_int = mk(S("DefIntegrate"), (T.mk_bound(x, body), N(0), N(1)))
    assert to_str(RUNTIME, def_int) == "∫_0^1[sin(x)] dx"
    assert to_str(RUNTIME, def_int, src=True) == "DefIntegrate(sin(x), x, 0, 1)"


# ---------------------------------------------------------------------------
# 3. Every source-form spelling maps back to the same term
# ---------------------------------------------------------------------------

def _inventory():
    """(label, term, source spelling, how that spelling maps back).

    Route kinds: a declared alias, a declared binder head (spelled by its canonical
    name, since alias resolution maps the surface word there and binder recognition
    runs on it), a canonical head name (the parser reproduces a call of any head by
    that name), the language's own quote syntax, or a declared constant name.
    """
    x = X
    sin_x = mk(S("Sin"), (x,))
    def_int = mk(S("DefIntegrate"), (T.mk_bound(x, sin_x), N(0), N(1)))
    interval = mk(S("Interval"), (N(0), N(1), T.FALSE, T.TRUE))
    return (
        ("Sin", mk(S("Sin"), (x,)), "sin(x)", "declared alias"),
        ("Cos", mk(S("Cos"), (x,)), "cos(x)", "declared alias"),
        ("Tan", mk(S("Tan"), (x,)), "tan(x)", "declared alias"),
        ("Sinh", mk(S("Sinh"), (x,)), "sinh(x)", "declared alias"),
        ("Cosh", mk(S("Cosh"), (x,)), "cosh(x)", "declared alias"),
        ("Tanh", mk(S("Tanh"), (x,)), "tanh(x)", "declared alias"),
        ("Exp", mk(S("Exp"), (x,)), "exp(x)", "declared alias"),
        ("Log", mk(S("Log"), (x,)), "log(x)", "declared alias"),
        ("Sqrt", mk(S("Sqrt"), (x,)), "sqrt(x)", "declared alias"),
        ("Abs", mk(S("Abs"), (x,)), "abs(x)", "declared alias"),
        ("Atan", mk(S("Atan"), (x,)), "atan(x)", "declared alias"),
        ("pi", C("pi"), "pi", "declared constant name"),
        ("e", C("e"), "e", "declared constant name"),
        ("gamma", C("gamma"), "gamma", "declared constant name"),
        ("i", C("i"), "i", "declared constant name"),
        ("Integrate", mk(S("Integrate"), (T.mk_bound(x, sin_x),)),
         "Integrate(sin(x), x)", "declared binder head (canonical name)"),
        ("Sum", mk(S("Sum"), (T.mk_bound(x, sin_x),)),
         "Sum(sin(x), x)", "declared binder head (canonical name)"),
        ("Product", mk(S("Product"), (T.mk_bound(x, sin_x),)),
         "Product(sin(x), x)", "declared binder head (canonical name)"),
        ("Limit", mk(S("Limit"), (T.mk_bound(x, sin_x),)),
         "Limit(sin(x), x)", "declared binder head (canonical name)"),
        ("DefIntegrate", def_int,
         "DefIntegrate(sin(x), x, 0, 1)", "declared binder head (canonical name)"),
        ("RootOf", mk(S("RootOf"), (x, N(2))), "RootOf(x, 2)", "canonical name"),
        ("Piecewise", mk(S("Piecewise"), (x, mk(S("Gt"), (x, N(0))))),
         "Piecewise(x, x > 0)", "canonical name"),
        ("FiniteSet", mk(S("FiniteSet"), (x, N(1))), "FiniteSet(x, 1)", "canonical name"),
        ("Interval", interval, "Interval(0, 1, false, true)", "canonical name"),
        ("Union", mk(S("Union"), (interval, mk(S("FiniteSet"), (x,)))),
         "Union(Interval(0, 1, false, true), FiniteSet(x))", "canonical name"),
        ("O", mk(S("O"), (x,)), "O(x)", "canonical name"),
        ("Quote", T.quote(x), "'x", "quote syntax"),
        ("Foobar", mk(S("Foobar"), (x,)), "Foobar(x)", "canonical name (undeclared head)"),
        ("Foo", mk(S("Foo"), (x,)), "Foo(x)", "canonical name (undeclared head)"),
        ("f", mk(S("f"), (x,)), "f(x)", "canonical name (undeclared head)"),
    )


def test_source_form_round_trip_inventory():
    for label, t, spelling, route in _inventory():
        s = to_str(RUNTIME, t, src=True)
        assert s == spelling, f"{label}: source form changed, route {route}: {s!r}"
        assert parse(RUNTIME, s) == t, f"{label}: {s!r} re-parsed to a different term"


def test_every_declared_function_source_form_round_trips():
    """Generalized inventory: any function the DSL declares must have a source
    spelling that resolves back, so a new declaration cannot break the round trip
    silently."""
    for decl in RUNTIME.all_functions():
        t = mk(S(decl.name), (X,))
        s = to_str(RUNTIME, t, src=True)
        assert parse(RUNTIME, s) == t, f"{decl.name}: {s!r} did not re-parse to the same term"


def test_structural_notation_source_form_round_trips():
    """Structure the parser builds for itself comes back: ring signature, comparisons,
    boolean structure, quote, containers and bound words. These need no alias; the
    check is here because the source form has to reproduce them exactly."""
    for s in ("x + 1", "2*x + 1", "1/x^2", "x^(1/2)", "x/3", "-x",
              "x == 1", "x != 0", "x < 1 && y >= 2", "x > 0 || y > 0",
              "'cos(x)/cos(x)^2", "e^(i*pi)", "sqrt(x)*ln(x)",
              "FiniteSet(x, 1)", "Interval(0, 1, false, true)",
              "Piecewise(x, x > 0)", "int(x^2, x, 0, 1)",
              "integrate(x^2, x)", "sin(x) + cos(x)*tan(x)"):
        t = parse(RUNTIME, s)
        out = to_str(RUNTIME, t, src=True)
        assert parse(RUNTIME, out) == t, f"{s!r} printed as {out!r}"


def test_boolean_structure_prints_as_a_call():
    """And/Or/Not are not infix in the source form; they print as canonical calls."""
    gt = mk(S("Gt"), (X, N(0)))
    for t in (mk(S("And"), (X, gt)), mk(S("Or"), (X, gt)), mk(S("Not"), (gt,))):
        out = to_str(RUNTIME, t, src=True)
        assert parse(RUNTIME, out) == t, f"{t.head.name} printed as {out!r}"


def test_de_bruijn_placeholder_source_form_uses_the_lexer_notation():
    """`@0` is the placeholder the lexer accepts; `#0` is the template display form."""
    assert to_str(RUNTIME, T.DB_(0)) == "#0"
    assert to_str(RUNTIME, T.DB_(0), src=True) == "@0"
    assert parse(RUNTIME, to_str(RUNTIME, T.DB_(0), src=True)) is T.DB_(0)


def test_literal_shapes_reach_the_term_through_the_numeric_folding_layer():
    """A literal the grammar writes with an operator parses back as that operator form:
    a rational is a quotient, an integer exponent written `^-2` is -1*2. The numeric
    folding layer collapses both to the exact literal the printer was given."""
    for t in (N(Fr(3, 4)), mk(S("Power"), (X, N(-2)))):
        s = to_str(RUNTIME, t, src=True)
        assert parse(RUNTIME, s) != t, f"{s!r} re-parsed exactly, so the pin is stale"
        assert fold(parse(RUNTIME, s)) is t, f"{s!r} did not fold back to the term"


def test_display_form_stays_friendly():
    """The display form may be non-parseable notation; only the source form is
    promised to re-parse."""
    assert to_str(RUNTIME, mk(S("Foo"), (X,))) == "foo(x)"
    assert to_str(RUNTIME, mk(S("Sin"), (X,))) == "sin(x)"
    assert to_str(RUNTIME, mk(S("FiniteSet"), (X, N(1)))) == "{x, 1}"
    assert to_str(RUNTIME, mk(S("Interval"), (N(0), N(1), T.FALSE, T.TRUE))) == "[0, 1)"


def test_root_of_round_trips_without_a_folding_workaround():
    """The canonical name is emitted as-is, so no case workaround is needed."""
    t = mk(S("RootOf"), (X, N(2)))
    assert to_str(RUNTIME, t, src=True) == "RootOf(x, 2)"
    assert parse(RUNTIME, to_str(RUNTIME, t, src=True)) == t


def test_infinity_atom_uses_the_notation_the_lexer_accepts():
    assert to_str(RUNTIME, T.INFINITY) == "Infinity"
    assert to_str(RUNTIME, T.INFINITY, src=True) == "infinity"
    assert parse(RUNTIME, to_str(RUNTIME, T.INFINITY, src=True)) is T.INFINITY


def test_atoms_without_a_surface_notation_are_refused_not_misread():
    """The empty solution set has no spelling the lexer accepts: its source form
    falls back to the display spelling and re-parsing refuses it with a ParseError
    rather than silently producing a different term."""
    assert to_str(RUNTIME, T.EMPTY_SET, src=True) == "{}"
    with pytest.raises(ParseError):
        parse(RUNTIME, "{}")
