"""Checker protocol, outcomes and the frozen checker registry."""

import pytest
from support import equation, variable

from cas.foundation.ids import FrameId
from cas.kernel.evidence import (
    CheckerRegistry,
    CheckRequest,
    InvalidEvidence,
    ObligationReport,
    Refuted,
    Unverified,
    Verified,
)
from cas.kernel.model import ObligationReason
from cas.language.decisions import Reason
from cas.syntax import term as T


class GoodChecker:
    id = "test.good"
    version = "1"

    def check(self, request: CheckRequest) -> Verified:
        return Verified(tuple(request.conclusions))


class NoVersion(GoodChecker):
    version = ""


def test_the_registry_returns_registered_checkers():
    checker = GoodChecker()
    registry = CheckerRegistry({checker.id: checker})
    assert registry.get(checker.id) is checker
    assert registry.get("missing") is None
    assert len(registry) == 1


def test_the_registry_refuses_a_key_that_disagrees_with_the_checker_id():
    with pytest.raises(ValueError):
        CheckerRegistry({"another.id": GoodChecker()})


def test_the_registry_refuses_an_empty_version():
    with pytest.raises(ValueError):
        CheckerRegistry({"test.good": NoVersion()})


def test_a_verified_outcome_reports_exactly_what_it_checked(runtime):
    conclusion = equation(runtime, variable(runtime), T.number(1))
    report = ObligationReport(conclusion, ObligationReason.DEFINEDNESS)
    outcome = Verified((conclusion,), (report,), (("domain", "Q"),), (0,))
    assert outcome.checked == (conclusion,)
    assert outcome.obligations == (report,)
    assert outcome.reads == (("domain", "Q"),)
    assert outcome.used_premises == (0,)


def test_a_refutation_needs_witnesses_and_a_detail(runtime):
    conclusion = equation(runtime, variable(runtime), T.number(1))
    with pytest.raises(ValueError):
        Refuted(conclusion, (), "no witnesses")
    with pytest.raises(ValueError):
        Refuted(conclusion, (T.number(1),), "")


def test_unverified_and_invalid_evidence_are_distinct():
    unknown = Unverified(Reason.BUDGET, "exhausted")
    assert unknown.reason is Reason.BUDGET
    assert unknown.detail == "exhausted"
    invalid = InvalidEvidence("malformed certificate")
    assert invalid.detail == "malformed certificate"


def test_a_check_request_is_a_value():
    request = CheckRequest(FrameId(0), (), (), "certificate")
    assert request.frame == FrameId(0)
    assert request.certificate == "certificate"
