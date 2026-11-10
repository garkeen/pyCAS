"""Structured refusals always explain themselves and validate their payloads."""

import pytest
from support import runtime_proposition

from cas.kernel.commit import Deferred
from cas.language.decisions import Blocker, Reason
from cas.language.execution import ExecutionBudget
from cas.operations.protocols import ProblemUnsupported, ProposalUnsupported
from cas.semantics.bridge import RenderRefused, ViewRefused
from cas.semantics.services import DerivationUnsupported
from cas.syntax import term as T

REFUSALS = (
    ViewRefused,
    RenderRefused,
    Blocker,
    DerivationUnsupported,
    ProblemUnsupported,
    ProposalUnsupported,
)


@pytest.mark.parametrize("refusal", REFUSALS)
def test_a_refusal_needs_a_non_empty_detail(refusal):
    with pytest.raises(ValueError):
        refusal(Reason.FRAGMENT, "")


@pytest.mark.parametrize("refusal", REFUSALS)
def test_a_refusal_detail_must_be_a_string(refusal):
    with pytest.raises(TypeError):
        refusal(Reason.FRAGMENT, 1)


def test_a_deferred_result_validates_its_payload():
    with pytest.raises(ValueError):
        Deferred(Reason.FRAGMENT, "")
    with pytest.raises(TypeError):
        Deferred("fragment", "detail")  # type: ignore[arg-type]
    with pytest.raises(TypeError):
        Deferred(
            Reason.FRAGMENT,
            "detail",
            conditions=(object(),),  # type: ignore[arg-type]
        )
    with pytest.raises(TypeError):
        Deferred(Reason.FRAGMENT, "detail", missing=frozenset({""}))


def test_a_blocker_target_must_be_a_proposition():
    with pytest.raises(TypeError):
        Blocker(Reason.FRAGMENT, "detail", target=T.TRUE)


def test_a_blocker_budget_must_be_an_execution_budget():
    with pytest.raises(TypeError):
        Blocker(Reason.FRAGMENT, "detail", budget=3)


def test_a_blocker_defaults_leave_target_and_budget_unset():
    blocker = Blocker(Reason.FRAGMENT, "detail")
    assert blocker.target is None
    assert blocker.budget is None


def test_a_blocker_records_its_target_and_budget(runtime):
    target = runtime_proposition(runtime, T.TRUE)
    budget = ExecutionBudget(max_nodes=4, max_depth=2)
    blocker = Blocker(
        Reason.FRAGMENT, "detail", target=target, budget=budget
    )
    assert blocker.target == target
    assert blocker.budget == budget


@pytest.mark.parametrize(
    "refusal", (ProblemUnsupported, ProposalUnsupported)
)
def test_an_unsupported_outcome_validates_its_payload(refusal):
    with pytest.raises(TypeError):
        refusal(Reason.FRAGMENT, "detail", missing=frozenset({""}))
    with pytest.raises(TypeError):
        refusal(Reason.FRAGMENT, "detail", missing=frozenset({1}))
    with pytest.raises(TypeError):
        refusal(Reason.FRAGMENT, "detail", conditions=(object(),))
    with pytest.raises(TypeError):
        refusal(Reason.FRAGMENT, "detail", attempted=("",))
    with pytest.raises(TypeError):
        refusal(Reason.FRAGMENT, "detail", attempted=(1,))
