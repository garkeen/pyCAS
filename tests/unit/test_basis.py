"""The admitted-basis registry and its use at the commit boundary."""

from dataclasses import replace

import pytest
from support import equation, variable

from cas.foundation.ids import WorldId
from cas.kernel.commit import (
    CommitProposal,
    Rejected,
    ValidatedCommitBatch,
    validate_commit,
)
from cas.kernel.evidence import (
    CheckerRegistry,
    CheckerSpec,
    Verified,
)
from cas.kernel.store import KernelStore
from cas.kernel.trust import (
    AxiomRef,
    BasisKind,
    BasisRef,
    BasisRegistry,
    CertificateSchema,
)
from cas.kernel.verdict import VerdictYes, decide
from cas.syntax import term as T


def basis(world: WorldId = WorldId(0)) -> BasisRef:
    return BasisRef(
        "test-library",
        BasisKind.STANDARD_LIBRARY,
        "1",
        "digest",
        world,
    )


def test_the_registry_verifies_an_admitted_basis_exactly():
    reference = basis()
    registry = BasisRegistry((reference,))
    assert registry.verify(reference)
    assert len(registry) == 1
    assert (
        registry.get("test-library", BasisKind.STANDARD_LIBRARY)
        is reference
    )
    assert registry.get("missing", BasisKind.STANDARD_LIBRARY) is None


@pytest.mark.parametrize(
    "changed",
    [
        replace(basis(), version="2"),
        replace(basis(), digest="other"),
        replace(basis(), world=WorldId(1)),
        replace(basis(), kind=BasisKind.DECLARATION_FILE),
    ],
)
def test_the_registry_refuses_a_basis_that_differs_in_any_field(changed):
    assert not BasisRegistry((basis(),)).verify(changed)


def test_the_registry_keys_on_both_name_and_kind():
    reference = basis()
    other_kind = replace(reference, kind=BasisKind.DECLARATION_FILE)
    registry = BasisRegistry((reference, other_kind))
    assert registry.verify(reference)
    assert registry.verify(other_kind)
    assert len(registry) == 2


def test_the_registry_refuses_a_repeated_name_and_kind():
    with pytest.raises(ValueError):
        BasisRegistry((basis(), basis()))
    with pytest.raises(ValueError):
        BasisRegistry((basis(), replace(basis(), version="2")))


def test_the_registry_refuses_non_basis_values():
    with pytest.raises(TypeError):
        BasisRegistry((object(),))  # type: ignore[arg-type]
    with pytest.raises(TypeError):
        BasisRegistry([basis()])  # type: ignore[arg-type]
    registry = BasisRegistry((basis(),))
    with pytest.raises(TypeError):
        registry.verify("test-library")  # type: ignore[arg-type]


def test_a_store_without_an_explicit_registry_admits_nothing(runtime):
    store = KernelStore(runtime.frames, CheckerRegistry({}))
    assert len(store.bases) == 0
    assert store.stats()["bases"] == 0


def test_a_store_rejects_a_non_registry(runtime):
    with pytest.raises(TypeError):
        KernelStore(
            runtime.frames,
            CheckerRegistry({}),
            bases="bases",  # type: ignore[arg-type]
        )


class StubChecker:
    id = "test.basis.checker"
    version = "1"

    def __init__(self) -> None:
        self.outcome = None
        self.requests = []

    def check(self, request):
        self.requests.append(request)
        return self.outcome


def store_for(
    runtime,
    trusted: BasisRef,
    registry: BasisRegistry,
) -> tuple[KernelStore, StubChecker]:
    checker = StubChecker()
    spec = CheckerSpec(
        checker,
        CertificateSchema("test", "1", str),
        frozenset({"test.problem"}),
        frozenset({"test.specification"}),
        runtime.world.id,
        (trusted,),
    )
    store = KernelStore(
        runtime.frames,
        CheckerRegistry({checker.id: spec}),
        bases=registry,
    )
    return store, checker


def proposal(runtime, proposition):
    return CommitProposal(
        frame=runtime.frame.id,
        conclusions=(proposition,),
        checker_id=StubChecker.id,
        problem_kind="test.problem",
        specification_kind="test.specification",
        certificate="certificate",
    )


def test_validate_commit_accepts_an_admitted_basis(runtime):
    reference = basis(runtime.world.id)
    store, checker = store_for(
        runtime, reference, BasisRegistry((reference,))
    )
    proposition = equation(runtime, variable(runtime), T.number(1))
    checker.outcome = Verified((proposition,))
    batch = validate_commit(store, proposal(runtime, proposition))
    assert isinstance(batch, ValidatedCommitBatch)
    assert batch.inference.basis == (reference,)


def test_validate_commit_records_an_admitted_basis_as_an_axiom(runtime):
    reference = basis(runtime.world.id)
    store, checker = store_for(
        runtime, reference, BasisRegistry((reference,))
    )
    proposition = equation(runtime, variable(runtime), T.number(1))
    checker.outcome = Verified((proposition,))
    batch = validate_commit(store, proposal(runtime, proposition))
    assert isinstance(batch, ValidatedCommitBatch)
    context = checker.requests[0].context
    assert context is not None
    assert context.axioms == (AxiomRef.from_basis(reference),)


def test_decide_receipt_records_an_admitted_basis_as_an_axiom(runtime):
    reference = basis(runtime.world.id)
    store, checker = store_for(
        runtime, reference, BasisRegistry((reference,))
    )
    proposition = equation(runtime, variable(runtime), T.number(1))
    checker.outcome = Verified((proposition,))
    verdict = decide(store, proposal(runtime, proposition))
    assert isinstance(verdict, VerdictYes)
    assert verdict.receipt.context.axioms == (
        AxiomRef.from_basis(reference),
    )


def test_validate_commit_rejects_a_basis_with_another_digest(runtime):
    reference = basis(runtime.world.id)
    altered = replace(reference, digest="other")
    store, checker = store_for(
        runtime, reference, BasisRegistry((altered,))
    )
    proposition = equation(runtime, variable(runtime), T.number(1))
    checker.outcome = Verified((proposition,))
    result = validate_commit(store, proposal(runtime, proposition))
    assert isinstance(result, Rejected)
    assert "unadmitted basis" in result.detail
    assert checker.requests == []


def test_validate_commit_rejects_an_empty_basis_registry(runtime):
    reference = basis(runtime.world.id)
    store, checker = store_for(runtime, reference, BasisRegistry())
    proposition = equation(runtime, variable(runtime), T.number(1))
    checker.outcome = Verified((proposition,))
    result = validate_commit(store, proposal(runtime, proposition))
    assert isinstance(result, Rejected)
    assert "unadmitted basis" in result.detail
    assert checker.requests == []
