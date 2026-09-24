"""Event: operation history.

The history graph and the proof graph are two different graphs: an Event
carries occurrence order (`parent_revision`) while a Step carries reasoning
dependencies (premises -> conclusions). Treating temporal order as a
mathematical dependency is forbidden, which is why the two cannot be merged
(the cardinality also differs: one interactive simplification can produce
hundreds of Artifacts and zero Steps).

`outputs` is the only cross-layer exit: it lists the object ids produced by the
operation and may contain kernel ids (`StepId` / `JudgmentId`). The kernel side
has no `event_id` field, so the reference direction can only be
workflow -> kernel. The provenance chain is therefore
`Judgment -> Step -> Event`, and the reverse query ("which operation produced
this conclusion") is answered by the inverted index in this module.

The log is append-only and the view is a branch pointer over it: `_events`
keeps every recorded operation, `_view` lists the indices currently in view (in
occurrence order), and `_future` holds the indices an undo moved out of the
view, most recent last, so a redo can put them back. `parent_revision` records
the revision in view when an operation was performed -- the point in history it
was applied to, not the raw event count. An operation performed after an undo
is therefore performed on the shortened view and discards the redo branch: the
undone events stay recorded, but they cannot be replayed past the new
operation.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import StrEnum

from cas.workflow.ids import EventId, RevisionId


class RefKind(StrEnum):
    ARTIFACT = "artifact"
    TASK = "task"
    CONSTRAINT = "constraint"
    BRANCH = "branch"
    SCOPE = "scope"
    STEP = "step"
    JUDGMENT = "judgment"


@dataclass(frozen=True, slots=True)
class Ref:
    """An output reference: a typed kind tag plus an id."""

    kind: RefKind
    id: int


@dataclass(frozen=True, slots=True)
class Event:
    id: EventId
    command: str
    inputs: tuple[int, ...] = ()
    outputs: tuple[Ref, ...] = ()
    parent_revision: RevisionId = RevisionId(0)


class EventLog:
    """Append-only operation history with a branch-aware view, a revision
    pointer and an artifact inverted index."""

    def __init__(self) -> None:
        self._events: list[Event] = []
        self._view: list[int] = []
        self._future: list[int] = []
        self._next = 0
        self._revision = RevisionId(0)
        self._producers: dict[Ref, list[EventId]] = {}

    def append(self, command: str, inputs: tuple[int, ...] = (),
               outputs: tuple[Ref, ...] = ()) -> Event:
        """Record one operation on top of the current view."""
        eid = EventId(self._next)
        self._next += 1
        ev = Event(id=eid, command=command, inputs=inputs, outputs=outputs,
                   parent_revision=self._revision)
        self._events.append(ev)
        self._view.append(len(self._events) - 1)
        self._future.clear()
        for ref in ev.outputs:
            self._producers.setdefault(ref, []).append(eid)
        self._revision = RevisionId(len(self._view))
        return ev

    def events(self) -> tuple[Event, ...]:
        """Every recorded event, in recording order."""
        return tuple(self._events)

    def visible(self) -> tuple[Event, ...]:
        """The events in view, in view order."""
        return tuple(self._events[i] for i in self._view)

    def current_revision(self) -> RevisionId:
        """The revision in view: how many operations the view holds."""
        return self._revision

    def producers_of(self, kind: RefKind | str, ident: int) -> tuple[EventId, ...]:
        """Return the events that produced an id in a typed id space."""
        return tuple(self._producers.get(Ref(RefKind(kind), ident), ()))

    def undo(self) -> RevisionId:
        """Move the most recent event in view out of the active view."""
        if self._view:
            self._future.append(self._view.pop())
        self._revision = RevisionId(len(self._view))
        return self._revision

    def redo(self) -> RevisionId:
        """Move the most recently undone event back into view."""
        if self._future:
            self._view.append(self._future.pop())
        self._revision = RevisionId(len(self._view))
        return self._revision

    def __len__(self) -> int:
        return len(self._events)
