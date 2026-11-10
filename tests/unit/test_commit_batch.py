"""Two-phase commits: validation fixes a batch, publication writes it once."""

from dataclasses import replace

import pytest
from support import equation, variable

from cas.kernel.commit import (
    CommitProposal,
    Committed,
    ValidatedCommitBatch,
    publish_commit,
    validate_commit,
)
from cas.kernel.evidence import (
    CheckerRegistry,
    CheckerSpec,
    ObligationReport,
    Verified,
)
from cas.kernel.model import ObligationReason
from cas.kernel.store import KernelError, KernelStore
from cas.kernel.trust import CertificateSchema
from cas.language.execution import ConditionPolicy
from cas.runtime.bootstrap import bootstrap
from cas.syntax import term as T


class StubChecker:
    id = "test.batch.checker"
    version = "1"

    def __init__(self) -> None:
        self.outcome = None

    def check(self, request):
        return self.outcome


def setup(runtime):
    checker = StubChecker()
    registration = CheckerSpec(
        checker,
        CertificateSchema("test", "1", str),
        frozenset({"test.problem"}),
        frozenset({"test.specification"}),
        runtime.world.id,
    )
    store = KernelStore(
        runtime.frames, CheckerRegistry({checker.id: registration})
    )
    return store, checker


def proposal(runtime, proposition, **overrides):
    values = dict(
        frame=runtime.frame.id,
        conclusions=(proposition,),
        checker_id="test.batch.checker",
        problem_kind="test.problem",
        specification_kind="test.specification",
        certificate="certificate",
    )
    values.update(overrides)
    return CommitProposal(**values)


def validated(runtime):
    store, checker = setup(runtime)
    proposition = equation(runtime, variable(runtime), T.number(1))
    checker.outcome = Verified((proposition,))
    batch = validate_commit(store, proposal(runtime, proposition))
    assert isinstance(batch, ValidatedCommitBatch)
    return store, batch


def test_validation_writes_nothing_until_publication(runtime):
    store, checker = setup(runtime)
    proposition = equation(runtime, variable(runtime), T.number(1))
    condition = equation(runtime, variable(runtime), T.number(0))
    checker.outcome = Verified(
        (proposition,),
        (ObligationReport(condition, ObligationReason.DEFINEDNESS),),
    )
    before = store.stats()
    batch = validate_commit(
        store,
        proposal(
            runtime,
            proposition,
            policy=ConditionPolicy.ALLOW_CONDITIONAL,
        ),
    )
    assert isinstance(batch, ValidatedCommitBatch)
    assert batch.frame == runtime.frame.id
    assert batch.world == runtime.world.id
    assert store.stats() == before

    committed = publish_commit(store, batch)
    assert isinstance(committed, Committed)
    assert committed == batch.committed
    after = store.stats()
    assert after["judgments"] == before["judgments"] + 1
    assert after["inferences"] == before["inferences"] + 1
    assert after["obligations"] == before["obligations"] + 1
    assert after["discharges"] == before["discharges"]


def test_a_batch_cannot_be_published_twice(runtime):
    store, batch = validated(runtime)
    publish_commit(store, batch)
    after = store.stats()
    with pytest.raises(KernelError):
        publish_commit(store, batch)
    assert store.stats() == after


def test_a_batch_cannot_be_constructed_directly(runtime):
    _, batch = validated(runtime)
    with pytest.raises(ValueError):
        ValidatedCommitBatch(
            batch.frame,
            batch.world,
            batch.conclusions,
            batch.used_premises,
            batch.obligations,
            batch.judgments,
            batch.inference,
            batch.discharges,
            batch.committed,
            store_token=object(),
        )
    with pytest.raises(TypeError):
        ValidatedCommitBatch(
            batch.frame,
            batch.world,
            batch.conclusions,
            batch.used_premises,
            batch.obligations,
            batch.judgments,
            batch.inference,
            batch.discharges,
            batch.committed,
            store_token=object(),
            _seal=object(),
        )


def test_replacing_a_validated_batch_does_not_copy_the_seal(runtime):
    store, batch = validated(runtime)
    with pytest.raises(ValueError):
        replace(batch, conclusions=batch.conclusions)
    with pytest.raises(ValueError):
        replace(batch, frame=batch.frame)
    assert store.stats()["judgments"] == 0


def test_a_forged_self_consistent_batch_is_not_publishable(runtime):
    store, batch = validated(runtime)
    before = store.stats()
    forged = object.__new__(ValidatedCommitBatch)
    for name in (
        "frame",
        "world",
        "conclusions",
        "used_premises",
        "obligations",
        "judgments",
        "inference",
        "discharges",
        "committed",
        "store_token",
    ):
        object.__setattr__(forged, name, getattr(batch, name))
    with pytest.raises(ValueError):
        publish_commit(store, forged)
    assert store.stats() == before

    sealed_with_a_foreign_object = object.__new__(ValidatedCommitBatch)
    for name in (
        "frame",
        "world",
        "conclusions",
        "used_premises",
        "obligations",
        "judgments",
        "inference",
        "discharges",
        "committed",
        "store_token",
    ):
        object.__setattr__(
            sealed_with_a_foreign_object, name, getattr(batch, name)
        )
    object.__setattr__(sealed_with_a_foreign_object, "_seal", object())
    with pytest.raises(ValueError):
        publish_commit(store, sealed_with_a_foreign_object)
    assert store.stats() == before


def test_a_batch_from_another_store_is_rejected(runtime):
    _, batch = validated(runtime)
    other_store = KernelStore(runtime.frames, CheckerRegistry({}))
    before = other_store.stats()
    with pytest.raises(KernelError):
        publish_commit(other_store, batch)
    assert other_store.stats() == before


def test_a_batch_from_another_world_is_rejected(runtime):
    _, batch = validated(runtime)
    other = bootstrap()
    other_store = KernelStore(other.frames, CheckerRegistry({}))
    before = other_store.stats()
    with pytest.raises(KernelError):
        publish_commit(other_store, batch)
    assert other_store.stats() == before


def test_a_batch_for_a_discarded_frame_is_rejected(runtime):
    store, checker = setup(runtime)
    child = runtime.frames.create(runtime.frame.id)
    proposition = equation(runtime, variable(runtime), T.number(1), child.id)
    checker.outcome = Verified((proposition,))
    batch = validate_commit(
        store, proposal(runtime, proposition, frame=child.id)
    )
    assert isinstance(batch, ValidatedCommitBatch)
    runtime.frames.discard(child.id)
    with pytest.raises(KernelError):
        publish_commit(store, batch)


def test_a_batch_whose_conclusions_disagree_with_its_judgments_is_rejected(
    runtime,
):
    store, batch = validated(runtime)
    with pytest.raises(ValueError):
        replace(
            batch,
            conclusions=(
                equation(runtime, variable(runtime), T.number(2)),
            ),
        )
    assert store.stats()["judgments"] == 0


def test_a_batch_whose_premises_disagree_with_its_inference_is_rejected(
    runtime,
):
    store, batch = validated(runtime)
    with pytest.raises(ValueError):
        replace(
            batch, used_premises=(batch.committed.judgments[0],)
        )
    assert store.stats()["judgments"] == 0
