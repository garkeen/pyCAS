"""Runtime adapters between kernel decision ports and mathematical services."""

from collections import OrderedDict


class ScopeServices:
    """Decide relative to one scope, with a bounded version-keyed cache."""

    _CACHE_LIMIT = 128

    def __init__(self, scopes, math):
        self._scopes = scopes
        self._math = math
        self._cache = OrderedDict()

    def decide(self, proposition, scope_id):
        """Expand definitions in the scope frame and decide the proposition."""
        key = (scope_id, proposition)
        if key in self._cache:
            self._cache.move_to_end(key)
            return self._cache[key]
        from cas.kernel.scope import Assumptions
        from cas.math.decide import decide
        from cas.math.definitions import expand
        definitions = self._scopes.definition_map(scope_id)
        lookup = definitions.get
        frame = tuple(expand(lookup, assumption.proposition)
                      for assumption in self._scopes.assumptions(scope_id))
        verdict = decide(self._math, expand(lookup, proposition), Assumptions(frame))
        self._cache[key] = verdict
        self._cache.move_to_end(key)
        while len(self._cache) > self._CACHE_LIMIT:
            self._cache.popitem(last=False)
        return verdict
