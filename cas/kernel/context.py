"""The read channel a checker uses to reach the context.

Three roles are involved, with authority for assumptions separate from their
consumption:

    authority for assumptions   kernel/scope.py: Scope (immutable, parent
                                pointer) plus ScopeStore
    projection for deciding     kernel/scope.py: Assumptions (immutable set)
    checker read channel        this module: TrackedContext, which records
                                every read

The three are a separation of authority and consumption, not three parallel
implementations:

· Scope/ScopeStore decide how a symbol binds here and which assumptions are
  visible; they are the authority.
· Assumptions is the read-only projection consumed by the decision layer;
  `extended` returns a new object instead of writing in place, so no clone and
  no rollback is needed. Undo is done by moving the revision pointer.
· TrackedContext makes every context read by a checker show up in
  `Step.reads`, so a step can never depend on an assumption without recording
  it.
"""

from cas.kernel.model import ContextReadSet


class TrackedContext:
    """A checker reads this object rather than a bare context, so every
    implicit use leaves a read dependency.

    Reads accumulate into a ContextReadSet and land with the Step. Only the
    recording granularity varies with the execution mode; the decision result
    and the content read never depend on the mode.
    """

    def __init__(self, scopes, services, scope_id, mode=None):
        from cas.kernel.mode import DEFAULT_MODE
        self._scopes = scopes
        self._services = services
        self._sid = scope_id
        self._mode = mode if mode is not None else DEFAULT_MODE
        self._reads = []

    def _record(self, kind, key):
        if self._mode.records_reads():
            self._reads.append((kind, key))

    def lookup_definition(self, symbol):
        body = self._scopes.lookup_definition(self._sid, symbol)
        if body is not None:
            self._record("definition", repr(symbol))
        return body

    def assumptions(self):
        asms = self._scopes.assumptions(self._sid)
        for a in asms:
            self._record("assumption", repr(a.proposition))
        return tuple(a.proposition for a in asms)

    def declarations(self):
        return self._scopes.declarations(self._sid)

    def decide(self, proposition):
        # The runtime service performs mathematical expansion.  The kernel only
        # records the scope reads that boundary will consume; it does not import
        # math or decide which definitions apply.
        for symbol in self._scopes.definition_map(self._sid):
            self.lookup_definition(symbol)
        self.assumptions()
        v = self._services.decide(proposition, self._sid)
        self._record("decide", repr(proposition))
        return v

    def read_set(self, dedupe=True):
        """The recorded read dependencies. dedupe=True gives Step granularity
        (each distinct item once); False gives read granularity, keeping every
        occurrence, which is what audit mode records.

        Deduplication is keyed on the whole `(kind, key)` pair. Keying on kind
        alone would collapse multiple reads of the same kind (two assumptions,
        two decisions) into one and lose read dependencies.
        """
        if dedupe:
            return ContextReadSet(tuple(sorted(set(self._reads))))
        return ContextReadSet(tuple(self._reads))
