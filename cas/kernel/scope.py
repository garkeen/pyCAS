"""Scope tree: persistent, parent-linked, immutable.

A scope is the authority for the *context*, not for computation; computation
does not go through it. It only answers how a symbol binds here, which
assumptions are visible, and whether a local symbol can escape.

The structure is immutable throughout (`Scope` is a frozen dataclass) and
changes are expressed by new Scope objects. Two kinds of creation exist:

· `ScopeStore.extend` appends entries and returns a **new version** of the same
  scope: the new object gets its own id, so every id names one fixed context and
  a recorded conclusion is never re-interpreted by later extensions;
· `ScopeStore.child` (and `create` for the root) starts a **new lineage**: a
  branch forks from one fixed version of its parent and only ever sees that
  version and its ancestors.

`lineage_of` groups the versions that share a context history and `head_of`
resolves an id to the version where new entries land.
"""

from dataclasses import dataclass

from cas.errors import ScopeError

from cas.kernel.ids import ScopeId
from cas.kernel.model import Assumption, Declaration, Definition


@dataclass(frozen=True, slots=True)
class Scope:
    """One scope version: immutable, parent-linked, never mutated in place.

    `parent` links a version to the version it was extended from (or, for a
    branch, to the version it forked from). `lineage` is shared by all versions
    of one context history, so an extension is recognisable as "the same scope,
    one entry later" rather than as a replacement of the same id.
    """
    id: ScopeId
    parent: ScopeId | None
    lineage: ScopeId
    declarations: tuple[Declaration, ...] = ()
    definitions: tuple[Definition, ...] = ()
    assumptions: tuple[Assumption, ...] = ()


@dataclass(frozen=True, slots=True)
class Assumptions:
    """Immutable assumption set: a read-only projection of the assumptions
    along a scope chain.

    `extended` produces a new object rather than writing in place, so no clone
    and no rollback are needed. The authoritative source of assumptions is the
    Scope (persistent, parent-linked); this object is only the projection
    consumed by the decision layer and takes no part in bookkeeping. Undo is
    done by moving the revision pointer.
    """
    items: tuple = ()

    @classmethod
    def of(cls, store, scope_id):
        return cls(tuple(a.proposition for a in store.assumptions(scope_id)))

    def extended(self, *terms):
        return Assumptions(self.items + tuple(terms))

    def __iter__(self):
        return iter(self.items)

    def __len__(self):
        return len(self.items)

    def __bool__(self):
        return bool(self.items)


class ScopeStore:
    """Scope storage: issues ids, maintains the version tree and answers
    visibility queries.

    Ids are never reused and entries only ever append, so a query against an id
    answers for exactly the context that id names.
    """

    def __init__(self):
        self._scopes: dict[ScopeId, Scope] = {}
        self._heads: dict[ScopeId, ScopeId] = {}
        # symbol -> scopes introducing it as a local symbol, in creation order.
        # Maintained at the two creation sites so the escape check never scans
        # every scope; symbols are interned with identity hashing, so a lookup
        # keeps the identity semantics of the check.
        self._introducers: dict = {}
        self._next = 0

    # --- construction ---

    def create(self, parent=None, declarations=(), definitions=(),
               assumptions=()) -> Scope:
        """Create a root scope, or a fork under `parent` (a new lineage)."""
        if parent is not None and parent not in self._scopes:
            raise KeyError(f"parent scope does not exist: {parent}")
        sid = ScopeId(self._next)
        self._next += 1
        s = Scope(id=sid, parent=parent, lineage=sid,
                  declarations=tuple(declarations),
                  definitions=tuple(definitions),
                  assumptions=tuple(assumptions))
        self._scopes[sid] = s
        self._heads[sid] = sid
        self._index_entries(s)
        return s

    def child(self, parent: Scope, declarations=(), definitions=(),
              assumptions=()) -> Scope:
        """Fork a new lineage under one fixed version of `parent`."""
        return self.create(parent=parent.id, declarations=declarations,
                           definitions=definitions, assumptions=assumptions)

    def _index_entries(self, s: Scope) -> None:
        """Record the local symbols this scope introduces.

        A symbol is local to the scope whose declaration or definition
        introduces it; the escape check asks for exactly that set, and scanning
        every scope for it would cost O(ledger size) on every commit.
        """
        for entry in tuple(s.declarations) + tuple(s.definitions):
            self._introducers.setdefault(entry.symbol, []).append(s.id)

    def extend(self, scope: Scope, declarations=(), definitions=(),
               assumptions=()) -> Scope:
        """Record entries on top of `scope` and return a **new version** of it.

        The new version carries a new id, so the previous version stays
        addressable and its context stays frozen: a conclusion recorded there
        keeps resolving against exactly the entries that were present.

        Only the entries passed here are stored on the new version; the chain
        queries (`declarations`/`assumptions`/`definition_map`) accumulate them
        along the parent links, exactly as they do for a forked branch. Storing
        a cumulative copy instead would make every chain walk count the
        ancestors' entries again.

        Only the current version of a lineage can be extended; extending an
        older one would fork the version chain and leave the head ambiguous.
        """
        head = self._heads.get(scope.lineage)
        if head is None or head != scope.id:
            raise ScopeError(
                f"only the current version of a scope can be extended: {scope.id}")
        sid = ScopeId(self._next)
        self._next += 1
        s = Scope(id=sid, parent=scope.id, lineage=scope.lineage,
                  declarations=tuple(declarations),
                  definitions=tuple(definitions),
                  assumptions=tuple(assumptions))
        self._scopes[sid] = s
        self._heads[s.lineage] = sid
        self._index_entries(s)
        return s

    def get(self, sid: ScopeId) -> Scope:
        return self._scopes[sid]

    def lineage_of(self, sid: ScopeId) -> ScopeId:
        """The lineage `sid` belongs to: shared by all versions of one context
        history, distinct for sibling branches."""
        return self._scopes[sid].lineage

    def head_of(self, sid: ScopeId) -> ScopeId:
        """The current version of `sid`'s lineage: where new entries land."""
        return self._heads[self._scopes[sid].lineage]

    # --- visibility ---

    def chain(self, sid: ScopeId):
        """The scope chain from root down to this scope."""
        out = []
        cur = self._scopes[sid]
        while True:
            out.append(cur)
            if cur.parent is None:
                break
            cur = self._scopes[cur.parent]
        return tuple(reversed(out))

    def is_visible(self, ancestor: ScopeId, descendant: ScopeId) -> bool:
        """Whether `descendant` is inside `ancestor` (inclusive).

        A conclusion from a child scope may not be used in a parent scope, and
        sibling branches cannot see each other.
        """
        return any(s.id == ancestor for s in self.chain(descendant))

    # --- entry queries ---

    def declarations(self, sid: ScopeId) -> tuple[Declaration, ...]:
        out = []
        for s in self.chain(sid):
            out.extend(s.declarations)
        return tuple(out)

    def assumptions(self, sid: ScopeId) -> tuple[Assumption, ...]:
        out = []
        for s in self.chain(sid):
            out.extend(s.assumptions)
        return tuple(out)

    def definition_map(self, sid: ScopeId) -> dict:
        """Visible definition table; an inner scope shadows an outer one."""
        m = {}
        for s in self.chain(sid):
            for d in s.definitions:
                m[d.symbol] = d.body
        return m

    def lookup_definition(self, sid: ScopeId, symbol):
        return self.definition_map(sid).get(symbol)

    # --- hygiene checks ---

    def introducers(self, symbol) -> tuple:
        """Which scopes introduce this symbol as a local symbol (declaration or
        definition left-hand side), in creation order."""
        return tuple(self._introducers.get(symbol, ()))

    def escapes(self, sid: ScopeId, term) -> tuple:
        """Local symbols that escape from `term`; empty when none do.

        Criterion: a free symbol is introduced by a scope that is *not* on the
        ancestor chain of `sid`, and no scope on that chain introduces it. A
        symbol introduced in `sid` or an ancestor is visible and does not
        escape (if the same symbol is shadowed along the chain the outer
        binding wins, so appearing anywhere on the chain counts as visible).

        Why this matters: a local definition (`u := x^2`) and introduced helper
        symbols are only meaningful inside their scope; if one appears in a
        parent-scope conclusion, readers of the parent would reference an
        undefined symbol.
        """
        from cas.syntax.termpath import free_vars
        fv = free_vars(term)
        if not fv:
            return ()
        chain = {s.id for s in self.chain(sid)}
        bad = []
        for f in fv:
            owners = set(self.introducers(f))
            if owners and not (owners & chain):
                bad.append(f)
        return tuple(bad)
