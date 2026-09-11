"""Kernel identifier types.

Each id is a distinct NewType so a ScopeId can never be passed where a
JudgmentId is expected. At runtime they are ints issued by an incrementing
counter in the store; an issued id is never reused because the store is
append-only and never physically deletes.

ArtifactId / TaskId / EventId / RevisionId belong to the workflow layer and are
deliberately not defined here: the kernel does not know workflow concepts.
"""

from typing import NewType

ScopeId = NewType("ScopeId", int)
RequirementId = NewType("RequirementId", int)
JudgmentId = NewType("JudgmentId", int)
StepId = NewType("StepId", int)
