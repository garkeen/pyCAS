"""Workflow identifier types.

Separate from the kernel ids: the kernel does not know workflow concepts, so
these types can only live on the workflow side.
"""

from typing import NewType

ArtifactId = NewType("ArtifactId", int)
TaskId = NewType("TaskId", int)
TaskCandidateId = NewType("TaskCandidateId", int)
EventId = NewType("EventId", int)
RevisionId = NewType("RevisionId", int)
