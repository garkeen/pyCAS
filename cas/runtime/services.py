"""Runtime adapters between kernel decision ports and mathematical services."""

from __future__ import annotations

from collections import OrderedDict
from typing import TYPE_CHECKING

from cas.kernel.ids import ScopeId
from cas.kernel.scope import ScopeStore
from cas.kernel.verdict import Verdict
from cas.syntax.term import Term

if TYPE_CHECKING:
    from cas.math.context import MathContext


class ScopeServices:
    """Decide relative to one scope with a bounded version-keyed cache."""

    _CACHE_LIMIT = 128

    def __init__(self, scopes: ScopeStore, math: MathContext) -> None:
        self._scopes = scopes
        self._math = math
        self._cache: OrderedDict[tuple[ScopeId, Term], Verdict] = OrderedDict()

    def decide(self, proposition: Term, scope_id: ScopeId) -> Verdict:
        """Expand definitions in the scope frame and decide a proposition."""
        key = (scope_id, proposition)
        cached = self._cache.get(key)
        if cached is not None:
            self._cache.move_to_end(key)
            return cached
        from cas.kernel.scope import Assumptions
        from cas.math.decide import decide
        from cas.math.definitions import expand

        definitions = self._scopes.definition_map(scope_id)
        lookup = definitions.get
        frame = tuple(
            expand(lookup, assumption.proposition)
            for assumption in self._scopes.assumptions(scope_id)
        )
        verdict = decide(
            self._math,
            expand(lookup, proposition),
            Assumptions(frame),
        )
        self._cache[key] = verdict
        self._cache.move_to_end(key)
        while len(self._cache) > self._CACHE_LIMIT:
            self._cache.popitem(last=False)
        return verdict
