"""Three-valued verdicts: explicit evidence, no truthiness."""

import pytest

from cas.language.decisions import YES, No, Reason, Unknown, Verdict, Yes
from cas.syntax import term as T


def test_a_verdict_never_converts_to_a_boolean():
    for verdict in (Yes(), No((T.number(1),), "not equal"), Unknown(Reason.FRAGMENT)):
        with pytest.raises(TypeError):
            bool(verdict)


def test_verdict_variants_are_distinguishable():
    assert Yes().is_yes()
    assert not Yes().is_no()
    assert not Yes().is_unknown()
    assert Unknown(Reason.FRAGMENT).is_unknown()
    assert No((T.number(1),), "different").is_no()
    assert isinstance(YES, Verdict)
    assert YES.is_yes()


def test_a_refutation_needs_witnesses_and_an_explanation():
    with pytest.raises(ValueError):
        No((), "nothing to show")
    with pytest.raises(ValueError):
        No((T.number(1),), "")
    refutation = No((T.number(1), T.number(2)), "1 is not 2")
    assert refutation.witnesses == (T.number(1), T.number(2))
    assert refutation.detail == "1 is not 2"


def test_unknown_names_one_of_the_four_reasons():
    assert {reason.value for reason in Reason} == {
        "fragment",
        "guarded",
        "undecidable",
        "budget",
    }
    unknown = Unknown(Reason.BUDGET, "budget exhausted")
    assert unknown.reason is Reason.BUDGET
    assert unknown.detail == "budget exhausted"
    assert Unknown(Reason.GUARDED).detail == ""


def test_verdicts_are_structural_values():
    assert Yes() == Yes()
    assert Unknown(Reason.FRAGMENT, "a") == Unknown(Reason.FRAGMENT, "a")
    assert Unknown(Reason.FRAGMENT, "a") != Unknown(Reason.BUDGET, "a")
