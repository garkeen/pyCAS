# -*- coding: utf-8 -*-
"""内核标识类型（v4 §6）。

各 id 是不同的 NewType，防止 ScopeId 与 JudgmentId 互串。运行期都是 int，
存储层用递增计数器发放；id 一经发放永不复用（store 追加式，不物理删除）。
"""

from typing import NewType

ScopeId = NewType("ScopeId", int)
RequirementId = NewType("RequirementId", int)
JudgmentId = NewType("JudgmentId", int)
StepId = NewType("StepId", int)

# 工作流侧（阶段4 落位；此处先给类型，避免后续反向定义）
ArtifactId = NewType("ArtifactId", int)
TaskId = NewType("TaskId", int)
EventId = NewType("EventId", int)
RevisionId = NewType("RevisionId", int)
