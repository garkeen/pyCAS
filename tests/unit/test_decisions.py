"""The closed set of reasons a checker or candidate may leave undecided."""

from cas.language.decisions import Reason


def test_the_undecided_reasons_are_the_four_contract_classes():
    assert {reason.value for reason in Reason} == {
        "fragment",
        "guarded",
        "undecidable",
        "budget",
    }
