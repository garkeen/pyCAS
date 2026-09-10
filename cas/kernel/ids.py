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

# ArtifactId / TaskId / EventId / RevisionId 属 workflow（v4 §8），**不在此处**：
# 内核不认识工作流概念（§四「kernel → workflow」严格禁止）。它们随阶段4 在
# workflow 侧定义。
