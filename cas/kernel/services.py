"""Kernel-visible decision service ports and core checker."""

from __future__ import annotations

from typing import TYPE_CHECKING, Protocol

from cas.kernel.evidence import (
    Accepted,
    CheckResult,
    RefutationRejected,
    Rejected,
    UnknownResult,
)
from cas.kernel.ids import ScopeId
from cas.kernel.verdict import No, Reason, Unknown, Verdict, unknown
from cas.syntax.term import Term

if TYPE_CHECKING:
    from cas.kernel.commit import ResolvedProposal
    from cas.kernel.context import TrackedContext
    from cas.kernel.store import KernelStore


class KernelServices(Protocol):
    """Capability surface visible to a checker and to commit."""

    def decide(self, proposition: Term, scope_id: ScopeId) -> Verdict:
        ...


class NullServices:
    """No mathematics is wired; every query is honestly unknown."""

    def decide(self, proposition: Term, scope_id: ScopeId) -> Verdict:
        return unknown()

    def lookup_definition(self, scope_id: ScopeId, symbol: Term) -> Term | None:
        return None

    def assumptions(self, scope_id: ScopeId) -> tuple[Term, ...]:
        return ()


class DecideChecker:
    """Context-bound checker that forwards exactly one proposition."""

    def check(
        self,
        proposal: ResolvedProposal,
        context: TrackedContext,
        services: KernelServices,
    ) -> CheckResult:
        if len(proposal.conclusions) != 1:
            return Rejected(Reason.FRAGMENT, "decide checker handles one conclusion only")
        verdict = services.decide(proposal.conclusions[0], proposal.scope)
        if verdict.is_yes():
            return Accepted(reads=context.read_set())
        if isinstance(verdict, No):
            return RefutationRejected(verdict.evidence)
        if not isinstance(verdict, Unknown):
            raise TypeError("decision service returned an unsupported verdict")
        return UnknownResult(verdict.reason, "decision undecided")


def register_core_checkers(store: KernelStore) -> None:
    """Register the kernel decision checker during explicit assembly."""
    store.checkers.register("kernel.decide", DecideChecker())
