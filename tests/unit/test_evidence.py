"""Checker protocol, outcomes and the frozen checker registry."""

import pytest
from support import equation, variable

from cas.foundation.ids import FrameId, WorldId
from cas.kernel.evidence import (
    CheckerRegistry,
    CheckerSpec,
    CheckRequest,
    InvalidEvidence,
    ObligationReport,
    Refuted,
    Unverified,
    Verified,
)
from cas.kernel.model import ObligationReason
from cas.kernel.trust import BasisKind, BasisRef, CertificateSchema
from cas.language.decisions import Reason
from cas.syntax import term as T


class GoodChecker:
    id = "test.good"
    version = "1"

    def check(self, request: CheckRequest) -> Verified:
        return Verified(tuple(request.conclusions))


class NoVersion(GoodChecker):
    version = ""


def spec(checker, *, deps=()):
    return CheckerSpec(
        checker,
        CertificateSchema("test", "1", type(None)),
        frozenset({"test.problem"}),
        frozenset({"test.specification"}),
        WorldId(0),
        deps,
    )


def basis(name="library"):
    return BasisRef(
        name, BasisKind.STANDARD_LIBRARY, "1", "digest", WorldId(0)
    )


def test_a_certificate_schema_enforces_a_structural_budget():
    schema = CertificateSchema(
        "test", "1", tuple, max_nodes=4, max_depth=3
    )
    assert schema.within_budget((1, 2))
    assert not schema.within_budget((1, 2, 3, 4, 5))
    deep = ((((1,),),),)
    assert schema.accepts(deep)
    assert not schema.within_budget(deep)


def test_a_certificate_budget_refuses_unmeasurable_or_cyclic_values():
    schema = CertificateSchema("test", "1", object)
    assert not schema.within_budget(object())
    cyclic: list[object] = []
    cyclic.append(cyclic)
    assert schema.accepts(cyclic)
    assert not schema.within_budget(cyclic)


def test_trust_records_validate_their_kinds():
    with pytest.raises(TypeError):
        BasisRef(
            "library",
            "standard_library",
            "1",
            "digest",
            WorldId(0),
        )
    with pytest.raises(TypeError):
        CheckerSpec(
            GoodChecker(),
            CertificateSchema("test", "1", type(None)),
            ["test.problem"],
            frozenset({"test.specification"}),
            WorldId(0),
        )


def test_check_outcomes_validate_their_payloads():
    with pytest.raises(TypeError):
        Verified((T.TRUE,))  # type: ignore[arg-type]
    with pytest.raises(TypeError):
        Refuted(T.TRUE, (T.number(1),), "not a proposition")  # type: ignore[arg-type]
    with pytest.raises(TypeError):
        Unverified("fragment")  # type: ignore[arg-type]


def test_check_requests_and_obligation_reports_validate_their_data():
    assert CheckRequest(FrameId(0), (), (), None).conclusions == ()
    with pytest.raises(TypeError):
        CheckRequest(FrameId(0), (T.TRUE,), (), None)  # type: ignore[arg-type]
    with pytest.raises(TypeError):
        ObligationReport(T.TRUE, ObligationReason.DEFINEDNESS)  # type: ignore[arg-type]


def test_the_registry_returns_registered_checkers():
    checker = GoodChecker()
    registration = spec(checker)
    registry = CheckerRegistry({checker.id: registration})
    assert registry.get(checker.id) is checker
    assert registry.spec(checker.id) is registration
    assert registry.get("missing") is None
    assert registry.spec("missing") is None
    assert len(registry) == 1


def test_the_registry_refuses_a_key_that_disagrees_with_the_checker_id():
    with pytest.raises(ValueError):
        CheckerRegistry({"another.id": spec(GoodChecker())})


def test_the_registry_refuses_an_empty_version():
    with pytest.raises(ValueError):
        CheckerRegistry({"test.good": spec(NoVersion())})


def test_a_checker_spec_needs_kinds_and_a_schema():
    with pytest.raises(ValueError):
        CheckerSpec(
            GoodChecker(),
            CertificateSchema("test", "1", type(None)),
            frozenset(),
            frozenset({"test.specification"}),
            WorldId(0),
        )
    with pytest.raises(ValueError):
        CheckerSpec(
            GoodChecker(),
            CertificateSchema("test", "1", type(None)),
            frozenset({"test.problem"}),
            frozenset(),
            WorldId(0),
        )
    with pytest.raises(ValueError):
        CertificateSchema("", "1", type(None))
    with pytest.raises(ValueError):
        CertificateSchema("test", "", type(None))


def test_a_basis_reference_records_kind_version_scope_and_digest():
    reference = basis()
    assert reference.name == "library"
    assert reference.kind is BasisKind.STANDARD_LIBRARY
    assert reference.version == "1"
    assert reference.digest == "digest"
    assert reference.world == WorldId(0)
    with pytest.raises(ValueError):
        BasisRef("", BasisKind.STANDARD_LIBRARY, "1", "d", WorldId(0))
    with pytest.raises(ValueError):
        BasisRef("b", BasisKind.STANDARD_LIBRARY, "", "d", WorldId(0))
    with pytest.raises(ValueError):
        BasisRef("b", BasisKind.STANDARD_LIBRARY, "1", "", WorldId(0))


def test_a_checker_spec_does_not_repeat_trusted_dependencies():
    with pytest.raises(ValueError):
        spec(GoodChecker(), deps=(basis(), basis()))


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


def test_a_checker_cannot_trust_a_basis_from_another_world():
    other = BasisRef(
        "other", BasisKind.STANDARD_LIBRARY, "1", "digest", WorldId(1)
    )
    with pytest.raises(ValueError):
        spec(GoodChecker(), deps=(other,))


def test_a_certificate_schema_needs_a_certificate_type():
    with pytest.raises(TypeError):
        CertificateSchema("test", "1", "not a type")
