"""Elaboration: expand aliases first, then type or issue a proposition."""

from support import head_app

from cas.language import propositions as Pr
from cas.language import sorts as S
from cas.language import typing as Ty
from cas.language.signatures import StructuralHead
from cas.semantics import elaborate
from cas.semantics.frames import Definition
from cas.syntax import term as T


def x_term(runtime) -> T.SymbolRef:
    return T.symbol(runtime.variable, "x")


def alias(runtime, name: str, body: T.Term):
    symbol = runtime.table.intern(name)
    frame = runtime.frames.create(
        runtime.frame.id, definitions=(Definition(symbol, name, body),)
    )
    return symbol, frame


def test_typing_sees_through_an_alias(runtime):
    u, frame = alias(runtime, "u", x_term(runtime))
    term = head_app(
        runtime.signature,
        StructuralHead.PLUS,
        T.symbol(u, "u"),
        T.number(1),
    )
    outcome = elaborate.typing(
        term, runtime.frames, frame.id, runtime.signature
    )
    assert outcome == Ty.Typed(S.REAL)


def test_typing_takes_the_sort_of_the_expanded_body(runtime):
    u, frame = alias(runtime, "u", T.number(1))
    outcome = elaborate.typing(
        T.symbol(u, "u"), runtime.frames, frame.id, runtime.signature
    )
    assert outcome == Ty.Typed(S.INTEGER)


def test_typing_follows_a_chain_of_aliases(runtime):
    u = runtime.table.intern("u")
    v = runtime.table.intern("v")
    frame = runtime.frames.create(
        runtime.frame.id,
        definitions=(
            Definition(u, "u", x_term(runtime)),
            Definition(v, "v", T.symbol(u, "u")),
        ),
    )
    outcome = elaborate.typing(
        T.symbol(v, "v"), runtime.frames, frame.id, runtime.signature
    )
    assert outcome == Ty.Typed(S.REAL)


def test_a_proposition_is_stored_alias_free(runtime):
    u, frame = alias(runtime, "u", x_term(runtime))
    term = head_app(
        runtime.signature, StructuralHead.EQ, T.symbol(u, "u"), T.number(1)
    )
    outcome = elaborate.proposition(
        term, runtime.frames, frame.id, runtime.signature
    )
    assert isinstance(outcome, Pr.Proposition)
    assert outcome.term == head_app(
        runtime.signature,
        StructuralHead.EQ,
        x_term(runtime),
        T.number(1),
    )
    assert outcome.meaning == frame.meaning


def test_elaboration_reports_undeclared_symbols(runtime):
    foreign = runtime.table.intern("foreign")
    outcome = elaborate.typing(
        T.symbol(foreign, "foreign"),
        runtime.frames,
        runtime.frame.id,
        runtime.signature,
    )
    assert isinstance(outcome, Ty.NeedsDeclaration)
    assert outcome.symbol_id == foreign


def test_elaboration_reports_ill_typed_terms(runtime):
    term = head_app(
        runtime.signature,
        StructuralHead.PLUS,
        x_term(runtime),
        T.TRUE,
    )
    outcome = elaborate.proposition(
        term, runtime.frames, runtime.frame.id, runtime.signature
    )
    assert isinstance(outcome, Ty.IllTyped)


def test_elaboration_reports_ill_scoped_terms(runtime):
    term = head_app(
        runtime.signature,
        StructuralHead.EQ,
        T.BoundVar(0),
        T.number(1),
    )
    outcome = elaborate.proposition(
        term, runtime.frames, runtime.frame.id, runtime.signature
    )
    assert isinstance(outcome, Pr.IllScoped)


def test_elaboration_does_not_mutate_the_input_term(runtime):
    u, frame = alias(runtime, "u", x_term(runtime))
    term = T.symbol(u, "u")
    elaborate.typing(term, runtime.frames, frame.id, runtime.signature)
    assert term == T.symbol(u, "u")
