# -*- coding: utf-8 -*-
"""Event：操作历史（v4 §8.9）。

历史图与证明图是**两张不同的图**（§8.5）：Event 带的是发生顺序
（`parent_revision`），Step 带的是推理依赖（premises → conclusions）。§8.1 明确
禁止把时间顺序当作数学依赖，所以两者不能合并（基数也不同：一条 interactive
化简可产几百个 Artifact 而零个 Step）。

**`outputs` 是跨层引用的唯一出口**（v4 §四）：它列出本次操作产出的对象 id，
可以含内核 id（`StepId` / `JudgmentId`）。内核侧没有 `event_id` 字段——方向只能
workflow → kernel。于是溯源链是 `Judgment → Step → Event`，反向查询（「这张结论
是哪个操作造的」）由本模块的倒排索引回答。

undo/redo 只移 revision 指针；事件列表追加式，不物理删除（§8.9 / §四.5）。
"""

from dataclasses import dataclass

from cas.workflow.ids import EventId, RevisionId


@dataclass(frozen=True, slots=True)
class Ref:
    """产出引用：`kind` 标签 + id。

    **为什么需要标签**：`NewType` 在运行期只是 `int`，`ArtifactId(1)`、`TaskId(1)`、
    `JudgmentId(1)` 彼此相等，倒排索引会互相碰撞。标签把「哪个 id 空间」显式带上。
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
    """追加式操作历史 + revision 指针 + 产物倒排索引。"""

    def __init__(self):
        self._events: list[Event] = []
        self._next = 0
        self._revision = RevisionId(0)      # 当前 revision = 已纳入视图的事件数
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

    # --- 查询 ---

    def events(self):
        return tuple(self._events)

    def visible(self):
        """当前 revision 下可见的事件（undo 之后其后的事件仍在列表里，只是不可见）。"""
        return tuple(self._events[: self._revision])

    def current_revision(self) -> RevisionId:
        return self._revision

    def producers_of(self, kind, ident) -> tuple:
        """倒排索引：哪个（些）事件产出了 `kind` 空间的这个 id。内核不参与。"""
        return tuple(self._producers.get(Ref(kind, ident), ()))

    # --- undo / redo（只移指针，不删事件）---

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
