"""Scope tree: persistent, parent-linked, immutable.

A scope is the authority for the *context*, not for computation; computation
does not go through it. It only answers how a symbol binds here, which
assumptions are visible, and whether a local symbol can escape.

The structure is immutable throughout (`Scope` is a frozen dataclass) and
changes are expressed by new Scope objects.
"""

from dataclasses import dataclass, replace

from cas.kernel.ids import ScopeId
from cas.kernel.model import Assumption, Declaration, Definition


@dataclass(frozen=True, slots=True)
class Scope:
    """A persistent scope: immutable, child scopes carry a parent pointer, and
    changes are expressed by new Scope objects."""
    id: ScopeId
    parent: ScopeId | None = None
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
    """Scope storage: issues ids, maintains the parent tree and answers
    visibility queries."""

    def __init__(self):
        self._scopes: dict[ScopeId, Scope] = {}
        self._next = 0

    # --- construction ---

    def create(self, parent=None, declarations=(), definitions=(),
               assumptions=()) -> Scope:
        if parent is not None and parent not in self._scopes:
            raise KeyError(f"parent scope does not exist: {parent}")
        sid = ScopeId(self._next)
        self._next += 1
        s = Scope(id=sid, parent=parent,
                  declarations=tuple(declarations),
                  definitions=tuple(definitions),
                  assumptions=tuple(assumptions))
        self._scopes[sid] = s
        return s

    def child(self, parent: Scope, declarations=(), definitions=(),
              assumptions=()) -> Scope:
        return self.create(parent=parent.id, declarations=declarations,
                           definitions=definitions, assumptions=assumptions)

    def extend(self, scope: Scope, declarations=(), definitions=(),
               assumptions=()) -> Scope:
        """Append entries on top of `scope` and return a **new** Scope; the
        original is never modified in place."""
        s = replace(scope,
                    declarations=scope.declarations + tuple(declarations),
                    definitions=scope.definitions + tuple(definitions),
                    assumptions=scope.assumptions + tuple(assumptions))
        self._scopes[s.id] = s
        return s

    def get(self, sid: ScopeId) -> Scope:
        return self._scopes[sid]

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

    def local_symbols(self, sid: ScopeId) -> tuple:
        """Symbols introduced by this scope itself (not its ancestors):
        declarations plus definition left-hand sides."""
        s = self._scopes[sid]
        return tuple([d.symbol for d in s.declarations]
                     + [d.symbol for d in s.definitions])

    def introducers(self, symbol) -> tuple:
        """Which scopes introduce this symbol as a local symbol (declaration or
        definition left-hand side)."""
        out = []
        for s in self._scopes.values():
            if any(d.symbol is symbol for d in s.declarations) \
                    or any(d.symbol is symbol for d in s.definitions):
                out.append(s.id)
        return tuple(out)

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
