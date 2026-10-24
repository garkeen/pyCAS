"""Core scope rules: a hypothesis is exactly the proposition it introduced."""

from support import head_app, proposition_in

from cas.foundation.ids import WorldId
from cas.kernel.context_rules import HypothesisChecker
from cas.kernel.evidence import CheckRequest, Unverified, Verified
from cas.language import sorts as S
from cas.language.signatures import StructuralHead
from cas.semantics.frames import Declaration, FrameStore, Hypothesis, World
from cas.semantics.symbols import SymbolTable, standard_language
from cas.syntax import term as T


def setup():
    table = SymbolTable()
    signature = standard_language(table)
    frames = FrameStore(World(WorldId(0), signature))
    x = table.intern("x")
    x_term = T.symbol(x, "x")
    base = frames.create(
        frames.root.id, declarations=(Declaration(x, "x", S.REAL),)
    )
    proposition = proposition_in(
        frames,
        base.id,
        signature,
        head_app(signature, StructuralHead.GT, x_term, T.number(0)),
    )
    child = frames.create(
        base.id, hypotheses=(Hypothesis(proposition),)
    )
    return frames, signature, x_term, proposition, child


def check(frames, frame, conclusions):
    return HypothesisChecker(frames).check(
        CheckRequest(frame.id, tuple(conclusions), (), None)
    )


def test_a_hypothesis_verifies_exactly_itself():
    frames, _, _, proposition, child = setup()
    outcome = check(frames, child, (proposition,))
    assert isinstance(outcome, Verified)
    assert outcome.checked == (proposition,)


def test_a_different_proposition_is_not_verified():
    frames, signature, x_term, _, child = setup()
    other = proposition_in(
        frames,
        child.id,
        signature,
        head_app(signature, StructuralHead.GT, x_term, T.number(1)),
    )
    outcome = check(frames, child, (other,))
    assert isinstance(outcome, Unverified)


def test_the_same_text_in_a_different_meaning_is_not_the_hypothesis():
    frames, signature, x_term, _, child = setup()
    same_text = proposition_in(
        frames,
        child.id,
        signature,
        head_app(signature, StructuralHead.GT, x_term, T.number(0)),
    )
    outcome = check(frames, child, (same_text,))
    assert isinstance(outcome, Unverified)


def test_every_conclusion_must_be_an_assumption():
    frames, _, _, proposition, child = setup()
    outcome = check(frames, child, (proposition, T.TRUE))
    assert isinstance(outcome, Unverified)
