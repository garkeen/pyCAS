# -*- coding: utf-8 -*-
"""checker 读取上下文的通道（v4 §6.11）。

v3 的可变 `Context`（`entries` 列表 + `marks`/`rollback` 位置指针撤销）已在
阶段5 删除，由 kernel 的持久化作用域树接管：

    假设的权威来源   kernel/scope.py: Scope（不可变、带父指针）+ ScopeStore
    判定层消费的投影 kernel/scope.py: Assumptions（不可变假设集）
    checker 的读通道  本模块: TrackedContext（把读写留下痕迹）

三者的分工是「谁有权威」与「谁消费」的分工，不是三套并行实现：

· `Scope`/`ScopeStore` 决定某个符号在此处如何绑定、哪些假设可见——**权威**。
· `Assumptions` 是判定层（decide/piecewise）消费的只读投影，`extended` 产生
  新对象而非就地写入，所以不需要克隆，也不需要撤销（撤销由 revision 指针
  完成，§8.9）。
· `TrackedContext` 让 checker 的每一次上下文读取都进入 `Step.reads`——否则会
  出现「某步实际依赖一条假设，而步骤记录里没有体现」。
"""

from cas.kernel.model import ContextReadSet


class TrackedContext:
    """checker 不直接读裸上下文，而读本对象——任何隐式使用都留下读依赖。

    读依赖按 `ContextReadSet` 累积，随 Step 落地；只有记录粒度随执行模式
    变化（kernel/mode.py），判定结果与读取内容不受模式影响（AGENTS.md §四.3）。
    """

    def __init__(self, scopes, services, scope_id, mode=None):
        from cas.kernel.mode import DEFAULT_MODE
        self._scopes = scopes
        self._services = services
        self._sid = scope_id
        self._mode = mode if mode is not None else DEFAULT_MODE
        self._reads = []

    def _record(self, kind, key):
        if self._mode.records_reads():
            self._reads.append((kind, key))

    def lookup_definition(self, symbol):
        body = self._scopes.lookup_definition(self._sid, symbol)
        if body is not None:
            self._record("definition", repr(symbol))
        return body

    def assumptions(self):
        asms = self._scopes.assumptions(self._sid)
        for a in asms:
            self._record("assumption", repr(a.proposition))
        return tuple(a.proposition for a in asms)

    def declarations(self):
        return self._scopes.declarations(self._sid)

    def decide(self, proposition):
        v = self._services.decide(proposition, self._sid)
        self._record("decide", repr(proposition))
        return v

    def read_set(self, dedupe=True):
        """读依赖记录。dedupe=True 为 Step 粒度（**每项**一次），False 为 read
        粒度（保留每次出现）——后者即 audit 模式。

        去重以 `(kind, key)` 整项为键：以 kind 为键会把同类的多次读取（如两条
        假设、两次判定）压成一条，读依赖就丢了。
        """
        if dedupe:
            return ContextReadSet(tuple(sorted(set(self._reads))))
        return ContextReadSet(tuple(self._reads))
