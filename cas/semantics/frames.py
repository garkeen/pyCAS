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

import hashlib
from collections.abc import Iterator
from contextlib import contextmanager
from dataclasses import dataclass

from cas.foundation.ids import FrameId, IdIssuer, SymbolId, WorldId
from cas.language import sorts as S
from cas.language.meaning import MeaningKey
from cas.language.propositions import Proposition
from cas.language.signatures import LanguageSignature
from cas.syntax import binding as B
from cas.syntax import term as T

_CONTENT_VERSION = "pycas.content.v1"


def _content_digest(content: object) -> str:
    """A SHA-256 over the deterministic `repr` of one canonical value.

    Every value passed here is a tuple of strings, integers, booleans, `None`
    and nested tuples.  Python `hash()` and object ids are never involved, so
    the digest survives process boundaries when the content is the same.
    """
    return hashlib.sha256(repr(content).encode("utf-8")).hexdigest()


def _sort_key(sort: S.Sort) -> object:
    """Canonical structural form of one sort, independent of its display."""
    if isinstance(sort, S.ScalarSort):
        return ("scalar", sort.number_system.value)
    if isinstance(sort, S.VectorSort):
        return ("vector", _sort_key(sort.element), sort.length)
    if isinstance(sort, S.MatrixSort):
        return (
            "matrix",
            _sort_key(sort.element),
            sort.rows,
            sort.columns,
        )
    if isinstance(sort, S.FunctionSort):
        return (
            "function",
            tuple(_sort_key(argument) for argument in sort.arguments),
            _sort_key(sort.result),
        )
    if isinstance(sort, S.SetSort):
        return ("set", _sort_key(sort.element), sort.empty)
    if isinstance(sort, S.PropositionSort):
        return ("proposition",)
    if isinstance(sort, S.RegionSort):
        return ("region",)
    if isinstance(sort, S.SyntaxSort):
        return ("syntax",)
    raise TypeError(f"unknown sort: {type(sort).__name__}")


@dataclass(frozen=True, slots=True, eq=False)
class World:
    """An assembled semantic world: the language it speaks."""

    id: WorldId
    language: LanguageSignature

    @property
    def digest(self) -> str:
        """Stable content identity of the language signature.

        The serialization contains the structural head mapping, arities,
        binders and operator signatures with their `SymbolId`s, plus every sort
        in canonical structural form.  The process-local `WorldId` is not part
        of it, so two independently assembled worlds with the same signature
        agree.  `SymbolId`s remain part of the content because terms are
        compared and serialized by them; deterministic assembly gives equal
        signatures equal ids.
        """
        language = self.language
        heads = tuple(
            (int(symbol_id), head.value)
            for symbol_id, head in sorted(
                language.heads.items(), key=lambda item: int(item[0])
            )
        )
        arities = tuple(
            (head.value, arity.minimum, arity.maximum)
            for head, arity in sorted(
                language.arities.items(), key=lambda item: item[0].value
            )
        )
        binders = tuple(
            (
                name,
                signature.name,
                signature.arity,
                tuple(
                    _sort_key(sort) for sort in signature.parameter_sorts
                ),
                (
                    None
                    if signature.result is None
                    else _sort_key(signature.result)
                ),
            )
            for name, signature in sorted(language.binders.items())
        )
        operators = tuple(
            (
                int(symbol_id),
                tuple(_sort_key(sort) for sort in signature.arguments),
                _sort_key(signature.result),
            )
            for symbol_id, signature in sorted(
                language.operators.items(), key=lambda item: int(item[0])
            )
        )
        return _content_digest(
            (
                _CONTENT_VERSION,
                "world",
                heads,
                arities,
                binders,
                operators,
            )
        )


_WORLD_IDS = IdIssuer(start=1)


def new_world(language: LanguageSignature) -> World:
    """Create a world with an identity distinct from every other assembly.

    A world id is a trust-boundary identity, not a per-store counter that may
    restart at zero.  Two runtimes assembled in one process must not make each
    other's propositions readable merely because both start their frame ids at
    zero.  The issuer is process-local; persistence must replace it with the
    stable content identity described in §6.5/§28.3.
    """
    return World(WorldId(_WORLD_IDS.issue()), language)


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

    @property
    def digest(self) -> str:
        """Stable content identity of this declaration."""
        return _content_digest(
            (
                _CONTENT_VERSION,
                "declaration",
                int(self.symbol_id),
                self.name,
                _sort_key(self.sort),
            )
        )


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

    @property
    def digest(self) -> str:
        """Stable content identity of this definition.

        The body is serialized by `Term.structural_key`, so display names of
        free symbols do not enter it; the alias's own name is explicit content.
        """
        return _content_digest(
            (
                _CONTENT_VERSION,
                "definition",
                int(self.symbol_id),
                self.name,
                self.body.structural_key(),
            )
        )


@dataclass(frozen=True, slots=True)
class Hypothesis:
    """A proposition assumed in a frame."""

    proposition: Proposition

    def __post_init__(self) -> None:
        if not isinstance(self.proposition, Proposition):
            raise TypeError("a hypothesis must be a proposition")

    @property
    def digest(self) -> str:
        """Stable content identity of this hypothesis.

        Only the proposition term enters this record key.  The meaning world is
        not repeated as the process-local `WorldId`: it is part of the
        enclosing `FrameStore.digest` through `World.digest`, which is the only
        context in which a hypothesis is valid.  Repeating the numeric id here
        would make two independently assembled worlds with identical content
        disagree.
        """
        return _content_digest(
            (
                _CONTENT_VERSION,
                "hypothesis",
                self.proposition.term.structural_key(),
            )
        )


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
        """The number of frames currently published in this store."""
        return len(self._frames)

    def digest(self, frame: FrameId) -> str:
        """Stable content identity of one frame and its ancestor chain.

        The digest recursively includes the world digest, the parent frame
        digest, and the frame's declarations, definitions and hypotheses in
        their stored order.  Stored order is the order the caller assembled
        them; duplicate introductions are refused by `create`, and definition
        order is meaningful because an alias may only use earlier aliases.
        The world digest is also the meaning world of every hypothesis, so the
        hypothesis record key does not repeat the process-local `WorldId`.

        Process-local `FrameId`s do not enter the digest, so two stores with
        identical worlds and frame content agree even when their ids differ.
        Adding a child frame never changes an existing parent's digest.
        """
        current = self.get(frame)
        if current.world != self._world.id:
            raise ValueError("the frame belongs to another world")
        parent_digest = (
            None
            if current.parent is None
            else self.digest(current.parent)
        )
        return _content_digest(
            (
                _CONTENT_VERSION,
                "frame",
                self._world.digest,
                parent_digest,
                tuple(
                    declaration.digest
                    for declaration in current.declarations
                ),
                tuple(
                    definition.digest
                    for definition in current.definitions
                ),
                tuple(
                    hypothesis.digest
                    for hypothesis in current.hypotheses
                ),
            )
        )

    @contextmanager
    def transaction(self) -> Iterator[None]:
        """Restore the frame table if one synchronous action fails.

        A frame created by a failed action is unpublished: no judgment can
        refer to it, and the next action receives a fresh id.  Committed frames
        are immutable and are never removed by this context manager.
        """
        frames = dict(self._frames)
        introducers = {
            symbol: set(owners)
            for symbol, owners in self._introducers.items()
        }
        try:
            yield
        except BaseException:
            self._frames = frames
            self._introducers = introducers
            raise

    def discard(self, frame_id: FrameId) -> None:
        """Remove a just-created frame that no committed record refers to.

        This is only for the failure path of one synchronous action: the caller
        has just created the frame, no judgment was published, and the frame has
        no children.  It is not a general history rewrite.
        """
        frame = self._frames.get(frame_id)
        if frame is None:
            raise KeyError(frame_id)
        if any(
            other.parent == frame_id
            for other in self._frames.values()
            if other.id != frame_id
        ):
            raise ValueError("cannot discard a frame with children")
        del self._frames[frame_id]
        for owners in self._introducers.values():
            owners.discard(frame_id)

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

    def environment_unchanged(
        self, ancestor: FrameId, descendant: FrameId
    ) -> bool:
        """Whether `descendant` extends `ancestor` without new environment content.

        Declarations, definitions and hypotheses are the name environment a
        proposition is read in (§6.2/§13.6): adding any of them changes the
        meaning of a formula even when the formula's own term is unchanged.  An
        obligation issued in `ancestor` can therefore be reused in `descendant`
        only while every frame strictly between them introduces none of them.

        The test is by chain position and frame content, never by frame id or
        registration order.  `ancestor` must lie on the chain of `descendant`; a
        sibling that happens to have the same content is a different
        environment and answers False.  A frame is unchanged from itself, so
        `environment_unchanged(frame, frame)` is True.
        """
        try:
            chain = self.chain(descendant)
        except KeyError:
            return False
        position = next(
            (
                index
                for index, current in enumerate(chain)
                if current.id == ancestor
            ),
            None,
        )
        if position is None:
            return False
        return all(
            not current.declarations
            and not current.definitions
            and not current.hypotheses
            for current in chain[position + 1 :]
        )

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

    def escapes(
        self,
        frame: FrameId,
        term: T.Term,
        *,
        local: frozenset[SymbolId] = frozenset(),
    ) -> tuple[SymbolId, ...]:
        """Free symbols that are not visible from `frame`.

        Every non-language free symbol needs a declaration on the frame chain
        (§6.4).  A symbol introduced only in an unrelated frame is an escape;
        a symbol never introduced at all is also an escape, not an implicit
        global name.  `local` lists symbols introduced by the frame currently
        being validated, whose introducer records are not published yet.
        """
        free = B.free_symbols(term)
        if not free:
            return ()
        chain = {current.id for current in self.chain(frame)}
        language = self._world.language
        escaped = []
        for symbol_id in free:
            owners = self._introducers.get(symbol_id)
            # Every introducer must be on the query chain. Sharing an id with
            # a sibling frame makes the free occurrence ambiguous, so a merely
            # intersecting owner set is not enough.
            if owners is not None:
                if not owners <= chain:
                    escaped.append(symbol_id)
                continue
            if symbol_id in local:
                continue
            if (
                language.head_of(symbol_id) is None
                and language.operator_of(symbol_id) is None
            ):
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
        frame_symbols = frozenset(
            {declaration.symbol_id for declaration in declarations}
            | {definition.symbol_id for definition in definitions}
        )
        for definition in definitions:
            self._require_fresh(parent, definition.symbol_id, introduced, definition.name)
            if not B.well_scoped(definition.body):
                raise ValueError(
                    f"definition body of {definition.name} is not well scoped"
                )
            if parent is not None and self.escapes(
                parent, definition.body, local=frame_symbols
            ):
                raise ValueError(
                    f"definition body of {definition.name} references a local "
                    "symbol of an unrelated frame"
                )
        for hypothesis in hypotheses:
            if parent is None:
                raise ValueError("the root frame cannot inherit a hypothesis")
            if not self.readable(hypothesis.proposition, parent):
                if hypothesis.proposition.meaning.world != self._world.id:
                    raise ValueError(
                        "a hypothesis belongs to another meaning world"
                    )
                if not self.is_visible(
                    hypothesis.proposition.meaning.frame, parent
                ):
                    raise ValueError(
                        "a hypothesis must be meaningful in the parent frame"
                    )
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
    "new_world",
]
