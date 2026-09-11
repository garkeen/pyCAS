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

undo/redo only moves the revision pointer; the event list is append-only and
never physically deletes.
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
    """Append-only operation history with a revision pointer and an artifact
    inverted index."""

    def __init__(self):
        self._events: list[Event] = []
        self._next = 0
        self._revision = RevisionId(0)      # current revision = number of events in view
        self._producers: dict[object, list] = {}

    def append(self, command, inputs=(), outputs=()) -> Event:
        eid = EventId(self._next)
        self._next += 1
        ev = Event(id=eid, command=command, inputs=tuple(inputs),
                   outputs=tuple(outputs), parent_revision=self._revision)
        self._events.append(ev)
        for obj in ev.outputs:
            self._producers.setdefault(obj, []).append(eid)
        self._revision = RevisionId(len(self._events))
        return ev

    # --- queries ---

    def events(self):
        return tuple(self._events)

    def visible(self):
        """Events visible at the current revision; after an undo, later events
        remain in the list but are not visible."""
        return tuple(self._events[: self._revision])

    def current_revision(self) -> RevisionId:
        return self._revision

    def producers_of(self, kind, ident) -> tuple:
        """Inverted index: which event(s) produced this id in the `kind` id
        space. The kernel takes no part."""
        return tuple(self._producers.get(Ref(kind, ident), ()))

    # --- undo / redo (pointer only, no event deletion) ---

    def undo(self) -> RevisionId:
        if self._revision > 0:
            self._revision = RevisionId(self._revision - 1)
        return self._revision

    def redo(self) -> RevisionId:
        if self._revision < len(self._events):
            self._revision = RevisionId(self._revision + 1)
        return self._revision

    def __len__(self):
        return len(self._events)
