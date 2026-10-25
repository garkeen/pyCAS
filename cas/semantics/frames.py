"""Worlds and frames: the immutable name and hypothesis environment.

A `World` fixes the language signature. A `Frame` is one immutable version of a
name environment: declarations, definitions and hypotheses, plus a link to the
parent version it was created from.

Visibility is ancestor-only. A descendant sees every ancestor; a sibling sees
nothing; a parent sees nothing from its children. There is no "current version"
pointer here: extending a frame creates a new frame, and an old one stays
exactly as it was.

Frames are created only through `FrameStore`, which checks freshness, binding,
definition acyclicity at use time, and that a hypothesis is meaningful in the
parent it extends. Symbol identity is a `SymbolId`; display names never decide
visibility or equality.
"""

from __future__ import annotations

from dataclasses import dataclass

from cas.foundation.ids import FrameId, IdIssuer, SymbolId, WorldId
from cas.language import sorts as S
from cas.language.propositions import MeaningKey, Proposition
from cas.language.signatures import LanguageSignature
from cas.syntax import binding as B
from cas.syntax import term as T


@dataclass(frozen=True, slots=True, eq=False)
class World:
    """An assembled semantic world: the language it speaks."""

    id: WorldId
    language: LanguageSignature


@dataclass(frozen=True, slots=True)
class Declaration:
    """`symbol : sort`."""

    symbol_id: SymbolId
    name: str
    sort: S.Sort

    def __post_init__(self) -> None:
        if not self.name:
            raise ValueError("a declaration needs a display name")
        if not isinstance(self.sort, S.Sort):
            raise TypeError("a declaration needs a sort")


@dataclass(frozen=True, slots=True)
class Definition:
    """`symbol := body`; a local alias, not an equation."""

    symbol_id: SymbolId
    name: str
    body: T.Term

    def __post_init__(self) -> None:
        if not self.name:
            raise ValueError("a definition needs a display name")
        if not isinstance(self.body, T.Term):
            raise TypeError("a definition body must be a term")


@dataclass(frozen=True, slots=True)
class Hypothesis:
    """A proposition assumed in a frame."""

    proposition: Proposition

    def __post_init__(self) -> None:
        if not isinstance(self.proposition, Proposition):
            raise TypeError("a hypothesis must be a proposition")


@dataclass(frozen=True, slots=True, eq=False)
class Frame:
    """One immutable version of a name environment."""

    id: FrameId
    world: WorldId
    parent: FrameId | None
    declarations: tuple[Declaration, ...] = ()
    definitions: tuple[Definition, ...] = ()
    hypotheses: tuple[Hypothesis, ...] = ()

    @property
    def meaning(self) -> MeaningKey:
        """The key under which formulas are read in this frame."""
        return MeaningKey(self.world, self.id)


class FrameStore:
    """Creates frames and answers visibility, sort and escape queries."""

    def __init__(self, world: World) -> None:
        self._world = world
        self._frames: dict[FrameId, Frame] = {}
        self._introducers: dict[SymbolId, set[FrameId]] = {}
        self._issuer = IdIssuer()
        self._root = self.create()

    @property
    def world(self) -> World:
        return self._world

    @property
    def root(self) -> Frame:
        return self._root

    def count(self) -> int:
        return self._issuer.issued

    def create(
        self,
        parent: FrameId | None = None,
        *,
        declarations: tuple[Declaration, ...] = (),
        definitions: tuple[Definition, ...] = (),
        hypotheses: tuple[Hypothesis, ...] = (),
    ) -> Frame:
        """Create a frame extending `parent`, or the root when it is None."""
        if parent is not None and parent not in self._frames:
            raise KeyError(f"parent frame does not exist: {parent}")
        self._validate(parent, declarations, definitions, hypotheses)
        frame = Frame(
            FrameId(self._issuer.issue()),
            self._world.id,
            parent,
            declarations,
            definitions,
            hypotheses,
        )
        self._frames[frame.id] = frame
        for declaration in declarations:
            self._introducers.setdefault(declaration.symbol_id, set()).add(frame.id)
        for definition in definitions:
            self._introducers.setdefault(definition.symbol_id, set()).add(frame.id)
        return frame

    def get(self, frame: FrameId) -> Frame:
        return self._frames[frame]

    def chain(self, frame: FrameId) -> tuple[Frame, ...]:
        """From the root down to `frame`."""
        out: list[Frame] = []
        current = self._frames[frame]
        while True:
            out.append(current)
            if current.parent is None:
                break
            current = self._frames[current.parent]
        return tuple(reversed(out))

    def is_visible(self, ancestor: FrameId, descendant: FrameId) -> bool:
        """Whether `ancestor` is on the chain of `descendant` (inclusive).

        A frame that was never created is not visible; callers can use this as
        a guard before comparing propositions that carry a meaning key.
        """
        try:
            chain = self.chain(descendant)
        except KeyError:
            return False
        return any(current.id == ancestor for current in chain)

    def sort_of(self, frame: FrameId, symbol_id: SymbolId) -> S.Sort | None:
        """The declared sort of a symbol, innermost declaration first.

        Definitions are aliases, not declarations: their sort is established by
        elaboration, not here.
        """
        for current in reversed(self.chain(frame)):
            for declaration in current.declarations:
                if declaration.symbol_id == symbol_id:
                    return declaration.sort
        return None

    def lookup_definition(
        self, frame: FrameId, symbol_id: SymbolId
    ) -> Definition | None:
        for current in reversed(self.chain(frame)):
            for definition in current.definitions:
                if definition.symbol_id == symbol_id:
                    return definition
        return None

    def assumptions(self, frame: FrameId) -> tuple[Proposition, ...]:
        """Hypotheses along the chain, outermost first."""
        return tuple(
            hypothesis.proposition
            for current in self.chain(frame)
            for hypothesis in current.hypotheses
        )

    def readable(self, proposition: Proposition, frame: FrameId) -> bool:
        """Whether `proposition` keeps its meaning when read in `frame`."""
        return (
            proposition.meaning.world == self._world.id
            and self.is_visible(proposition.meaning.frame, frame)
            and not self.escapes(frame, proposition.term)
        )

    def agree_in(
        self,
        frame: FrameId,
        left: Proposition,
        right: Proposition,
    ) -> bool:
        """Whether two propositions may be compared in `frame`.

        Symbols keep stable identities and a frame only extends its parent
        chain, so a proposition read in an ancestor keeps its meaning in a
        descendant. This method makes that weakening rule an explicit
        precondition; propositions from unrelated frames or worlds never agree.
        """
        return self.readable(left, frame) and self.readable(right, frame)

    def escapes(self, frame: FrameId, term: T.Term) -> tuple[SymbolId, ...]:
        """Local symbols of unrelated frames that appear free in `term`."""
        free = B.free_symbols(term)
        if not free:
            return ()
        chain = {current.id for current in self.chain(frame)}
        escaped = []
        for symbol_id in free:
            owners = self._introducers.get(symbol_id)
            # Every introducer must be on the query chain. Sharing an id with
            # a sibling frame makes the free occurrence ambiguous, so a merely
            # intersecting owner set is not enough.
            if owners and not owners <= chain:
                escaped.append(symbol_id)
        return tuple(sorted(escaped))

    # --- validation ---

    def _validate(
        self,
        parent: FrameId | None,
        declarations: tuple[Declaration, ...],
        definitions: tuple[Definition, ...],
        hypotheses: tuple[Hypothesis, ...],
    ) -> None:
        introduced: set[SymbolId] = set()
        for declaration in declarations:
            self._require_fresh(parent, declaration.symbol_id, introduced, declaration.name)
        for definition in definitions:
            self._require_fresh(parent, definition.symbol_id, introduced, definition.name)
            if not B.well_scoped(definition.body):
                raise ValueError(
                    f"definition body of {definition.name} is not well scoped"
                )
            if parent is not None and self.escapes(parent, definition.body):
                raise ValueError(
                    f"definition body of {definition.name} references a local "
                    "symbol of an unrelated frame"
                )
        for hypothesis in hypotheses:
            if parent is None:
                raise ValueError("the root frame cannot inherit a hypothesis")
            if not self.is_visible(hypothesis.proposition.meaning.frame, parent):
                raise ValueError(
                    "a hypothesis must be meaningful in the parent frame"
                )
            if self.escapes(parent, hypothesis.proposition.term):
                raise ValueError(
                    "a hypothesis references a local symbol of an "
                    "unrelated frame"
                )
        self._reject_alias_cycles(parent, definitions)

    def _reject_alias_cycles(
        self,
        parent: FrameId | None,
        definitions: tuple[Definition, ...],
    ) -> None:
        """A definition may use earlier aliases, never itself or a later one.

        This is what makes expansion terminate: every body refers only to
        aliases that were already available when it was declared.
        """
        available: set[SymbolId] = set()
        if parent is not None:
            for current in self.chain(parent):
                available.update(
                    definition.symbol_id for definition in current.definitions
                )
        in_frame = {definition.symbol_id for definition in definitions}
        for definition in definitions:
            for symbol_id in B.free_symbols(definition.body):
                if symbol_id in in_frame and symbol_id not in available:
                    raise ValueError(
                        f"definition {definition.name!r} references itself "
                        "or a later alias"
                    )
            available.add(definition.symbol_id)

    def _require_fresh(
        self,
        parent: FrameId | None,
        symbol_id: SymbolId,
        introduced: set[SymbolId],
        name: str,
    ) -> None:
        if symbol_id in introduced:
            raise ValueError(f"symbol introduced twice in one frame: {name}")
        language = self._world.language
        if language.head_of(symbol_id) is not None:
            raise ValueError(
                f"a structural head cannot be declared as a symbol: {name}"
            )
        if language.operator_of(symbol_id) is not None:
            raise ValueError(
                f"a language operator cannot be redeclared: {name}"
            )
        introduced.add(symbol_id)
        owners = self._introducers.get(symbol_id)
        if owners:
            raise ValueError(
                f"symbol {name!r} is already introduced in another frame"
            )


class FrameSorts:
    """The `SortEnvironment` view of one frame."""

    __slots__ = ("_frames", "_frame")

    def __init__(self, frames: FrameStore, frame: FrameId) -> None:
        self._frames = frames
        self._frame = frame

    def sort_of(self, symbol_id: SymbolId) -> S.Sort | None:
        return self._frames.sort_of(self._frame, symbol_id)

    def bound_sort(self, index: int) -> S.Sort | None:
        del index
        return None


__all__ = [
    "Declaration",
    "Definition",
    "Frame",
    "FrameSorts",
    "FrameStore",
    "Hypothesis",
    "World",
]
