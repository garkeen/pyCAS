# -*- coding: utf-8 -*-
"""工作流标识类型（v4 §8）。

与 kernel 的 id 分开：内核不认识工作流概念（v4 §四「kernel → workflow」禁止），
所以这些类型只能住在 workflow 侧。
"""

from typing import NewType

ArtifactId = NewType("ArtifactId", int)
TaskId = NewType("TaskId", int)
TaskCandidateId = NewType("TaskCandidateId", int)
EventId = NewType("EventId", int)
RevisionId = NewType("RevisionId", int)
