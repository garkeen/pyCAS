"""Runtime adapters between kernel decision ports and mathematical services."""

from __future__ import annotations

from collections import OrderedDict
from typing import TYPE_CHECKING

from cas.kernel.ids import ScopeId
from cas.kernel.scope import ScopeStore
from cas.kernel.verdict import Reason, Verdict, unknown
from cas.syntax import term as T
from cas.syntax.term import Term, is_proposition
from cas.syntax.termpath import postorder, well_scoped

if TYPE_CHECKING:
    from cas.math.context import MathContext


class ScopeServices:
    """Decide relative to one scope with a bounded version-keyed cache."""

    _CACHE_LIMIT = 128

    def __init__(self, scopes: ScopeStore, math: MathContext) -> None:
        self._scopes = scopes
        self._math = math
        self._cache: OrderedDict[tuple[ScopeId, Term], Verdict] = OrderedDict()
        self._active: set[tuple[ScopeId, Term]] = set()

    def supports_scope(self, scope_id: ScopeId) -> bool:
        # Declaration sorts are not yet consumed by the mathematical context.
        return not self._scopes.declarations(scope_id)

    def definedness(self, term: Term, scope_id: ScopeId) -> tuple[Term, ...] | None:
        from cas.math.definitions import expand
        from cas.math.domcond import dom_condition

        if not self.supports_scope(scope_id):
            return None
        expanded = expand(self._scopes.definition_map(scope_id).get, term)
        for node in postorder(expanded):
            if isinstance(node, T.Bound) or node == T.UNDEFINED:
                return None
            if isinstance(node, T.Expr) and node.head.name == "Piecewise":
                # Scalar guards cannot express first-match coverage or boundary regularity.
                return None
        return tuple(dom_condition(self._math, expanded))

    def decide(self, proposition: Term, scope_id: ScopeId) -> Verdict:
        """Expand definitions in the scope frame and decide a proposition."""
        if not self.supports_scope(scope_id) or not is_proposition(proposition) or not well_scoped(proposition):
            return unknown(Reason.FRAGMENT)
        key = (scope_id, proposition)
        cached = self._cache.get(key)
        if cached is not None:
            self._cache.move_to_end(key)
            return cached
        from cas.kernel.scope import Assumptions
        from cas.math.decide import decide
        from cas.math.definitions import expand

        if key in self._active:
            return unknown(Reason.GUARDED)
        self._active.add(key)
        try:
            conditions = self.definedness(proposition, scope_id)
            if conditions is None:
                return unknown(Reason.FRAGMENT)
            for condition in conditions:
                support = self.decide(condition, scope_id)
                if not support.is_yes():
                    return support if support.is_unknown() else unknown(Reason.GUARDED)
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
        finally:
            self._active.remove(key)
        self._cache[key] = verdict
        self._cache.move_to_end(key)
        while len(self._cache) > self._CACHE_LIMIT:
            self._cache.popitem(last=False)
        return verdict
