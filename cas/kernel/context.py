from dataclasses import dataclass

from cas.syntax import term as T


@dataclass
class Entry:
    fact: T.Term
    kind: str
    origin: object


@dataclass
class Branch:
    cond: T.Term
    ctx: "Context"
    status: str


class Context:
    """v3 遗留的可变上下文（阶段5 换持久化 Scope 树）。

    **本类只装数据、只做纯记账**：假设列表、标记/回滚、按来源删除。判定与
    分支构造**不在这里**——它们要调 cas.math.decide，而 v4 §四 严格禁止
    `kernel → 具体数学模块`。相应的自由函数见 `cas.math.decide.check_and_assume`
    与 `cas.math.decide.branch`（math → kernel 引用 Branch，方向合规）。
    """

    def __init__(self):
        self.entries = []
        self.marks = []

    def assume(self, fact, origin="user", kind="fact"):
        e = Entry(fact, kind, origin)
        self.entries.append(e)
        return e

    def clone(self):
        c = self.__class__()
        c.entries = list(self.entries)
        return c

    def mark(self):
        self.marks.append(len(self.entries))
        return len(self.marks) - 1

    def rollback(self, mi=None):
        if mi is None:
            if self.marks:
                self.entries = self.entries[: self.marks.pop()]
        else:
            while len(self.marks) > mi + 1:
                self.marks.pop()
            pos = self.marks[mi] if self.marks else 0
            self.entries = self.entries[:pos]

    def drop_origin(self, origin):
        self.entries = [e for e in self.entries if e.origin != origin]

    def facts(self):
        return [e.fact for e in self.entries]


# ---------------------------------------------------------------------------
# TrackedContext：checker 读取上下文的唯一通道（v4 §6.11）
# ---------------------------------------------------------------------------

class TrackedContext:
    """checker 不直接读裸上下文，而读本对象——任何隐式使用都留下读依赖。

    不这样做就会出现「某步实际依赖一条假设，但步骤记录里没有体现」。读依赖
    按 `ContextReadSet` 累积，随 Step 落地；只有记录粒度随执行模式变化，判定
    结果与读取内容不受模式影响（AGENTS.md §四.3）。
    """

    def __init__(self, scopes, services, scope_id,
                 mode=None):
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
        """读依赖记录。dedupe=True 为 Step 粒度（每项一次），False 为 read 粒度
        （保留每次出现）——后者即 audit 模式。"""
        from cas.kernel.model import ContextReadSet
        if dedupe:
            seen = {}
            for k, val in self._reads:
                seen[k] = val
            return ContextReadSet(tuple(sorted(seen.items())))
        return ContextReadSet(tuple(self._reads))