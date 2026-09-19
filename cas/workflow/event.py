"""Event: operation history.

The history graph and the proof graph are two different graphs: an Event
carries occurrence order (`parent_revision`) while a Step carries reasoning
dependencies (premises -> conclusions). Treating temporal order as a
mathematical dependency is forbidden, which is why the two cannot be merged
(their cardinality also differs: one interactive simplification can produce
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

from dataclasses import dataclass

from cas.workflow.ids import EventId, RevisionId


@dataclass(frozen=True, slots=True)
class Ref:
    """An output reference: a `kind` tag plus an id.

    Why a tag is needed: a NewType is only an `int` at runtime, so
    `ArtifactId(1)`, `TaskId(1)` and `JudgmentId(1)` compare equal and the
    inverted index would collide. The tag makes the id space explicit.
    """
    kind: str
    id: int


@dataclass(frozen=True, slots=True)
class Event:
    id: EventId
    command: str
    inputs: tuple = ()
    outputs: tuple = ()                    # tuple[Ref, ...]
    parent_revision: RevisionId = RevisionId(0)


class EventLog:
    """Append-only operation history with a branch-aware view, a revision
    pointer and an artifact inverted index."""

    def __init__(self):
        self._events: list[Event] = []
        self._view: list[int] = []          # event indices in view, in order
        self._future: list[int] = []        # undone indices, most recent last
        self._next = 0
        self._revision = RevisionId(0)      # current revision = number of events in view
        self._producers: dict[object, list] = {}

    def append(self, command, inputs=(), outputs=()) -> Event:
        """Record one operation on top of the current view.

        `parent_revision` is the revision in view *before* this operation, so
        an operation performed after an undo is recorded as branching from the
        shortened history. Recording discards the redo branch: the undone
        events stay in `_events` but can no longer be put back.
        """
        eid = EventId(self._next)
        self._next += 1
        ev = Event(id=eid, command=command, inputs=tuple(inputs),
                   outputs=tuple(outputs), parent_revision=self._revision)
        self._events.append(ev)
        self._view.append(len(self._events) - 1)
        self._future.clear()
        for obj in ev.outputs:
            self._producers.setdefault(obj, []).append(eid)
        self._revision = RevisionId(len(self._view))
        return ev

    # --- queries ---

    def events(self):
        """Every recorded event, in recording order (the append-only history)."""
        return tuple(self._events)

    def visible(self):
        """The events in view, in view order.

        After an undo the later events stay recorded and are still listed by
        `events()`; they are simply not part of the current branch.
        """
        return tuple(self._events[i] for i in self._view)

    def current_revision(self) -> RevisionId:
        """The revision in view: how many operations the view holds."""
        return self._revision

    def producers_of(self, kind, ident) -> tuple:
        """Inverted index: which event(s) produced this id in the `kind` id
        space. The kernel takes no part. Every recorded event is indexed, not
        only the visible ones: the provenance query is about history.
        """
        return tuple(self._producers.get(Ref(kind, ident), ()))

    # --- undo / redo (view pointer only, no event deletion) ---

    def undo(self) -> RevisionId:
        """Move the most recent event in view out of it, for a redo to restore."""
        if self._view:
            self._future.append(self._view.pop())
        self._revision = RevisionId(len(self._view))
        return self._revision

    def redo(self) -> RevisionId:
        """Put the most recently undone event back into view, if any."""
        if self._future:
            self._view.append(self._future.pop())
        self._revision = RevisionId(len(self._view))
        return self._revision

    def __len__(self):
        return len(self._events)
