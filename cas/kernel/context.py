"""Checked, read-recording context access for verifiers."""

from __future__ import annotations

from cas.kernel.ids import ScopeId
from cas.kernel.mode import DEFAULT_MODE, ExecutionMode
from cas.kernel.model import ContextReadSet, Declaration
from cas.kernel.scope import ScopeStore
from cas.kernel.services import KernelServices
from cas.kernel.verdict import Verdict
from cas.syntax.term import Term


class TrackedContext:
    """The only context-read channel exposed to a checker."""

    def __init__(
        self,
        scopes: ScopeStore,
        services: KernelServices,
        scope_id: ScopeId,
        mode: ExecutionMode | None = None,
    ) -> None:
        self._scopes = scopes
        self._services = services
        self._scope_id = scope_id
        self._mode = DEFAULT_MODE if mode is None else mode
        self._reads: list[tuple[str, str]] = []

    def _record(self, kind: str, key: str) -> None:
        if self._mode.records_reads():
            self._reads.append((kind, key))

    def lookup_definition(self, symbol: Term) -> Term | None:
        body = self._scopes.lookup_definition(self._scope_id, symbol)
        if body is not None:
            self._record("definition", repr(symbol))
        return body

    def assumptions(self) -> tuple[Term, ...]:
        assumptions = self._scopes.assumptions(self._scope_id)
        for assumption in assumptions:
            self._record("assumption", repr(assumption.proposition))
        return tuple(assumption.proposition for assumption in assumptions)

    def declarations(self) -> tuple[Declaration, ...]:
        return self._scopes.declarations(self._scope_id)

    def decide(self, proposition: Term) -> Verdict:
        for symbol in self._scopes.definition_map(self._scope_id):
            self.lookup_definition(symbol)
        self.assumptions()
        verdict = self._services.decide(proposition, self._scope_id)
        self._record("decide", repr(proposition))
        return verdict

    def read_set(self, dedupe: bool = True) -> ContextReadSet:
        entries = tuple(sorted(set(self._reads))) if dedupe else tuple(self._reads)
        return ContextReadSet(entries)
