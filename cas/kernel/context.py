from dataclasses import dataclass

from cas.syntax import term as T
from cas.kernel.verdict import YES, NO


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
    """v3 可变上下文（v4 阶段5 将换持久化 Scope 树，此处为临时后端）。

    decide 依赖按方法内惰性导入：kernel 包不得在 import 期拉进整个
    math/decide（跨层反向边）；decide 侧亦有惰性回引（cas/math/decide.py
    环回边注释）。两向都惰性，任何模块作入口都无半初始化风险。
    """

    def __init__(self):
        self.entries = []
        self.marks = []

    def assume(self, fact, origin="user", kind="fact"):
        e = Entry(fact, kind, origin)
        self.entries.append(e)
        return e

    def check_and_assume(self, fact, origin="user", kind="fact"):
        from cas.math.decide import domain_ok as _domain_ok
        from cas.math.decide import contradicted as _contradicted
        if _domain_ok(fact, self) is NO:
            return NO, "domain"
        if _contradicted(fact, self):
            return NO, "contradiction"
        self.assume(fact, origin=origin, kind=kind)
        return YES, None

    def clone(self):
        c = self.__class__()
        c.entries = list(self.entries)
        return c

    def branch(self, *conds):
        out = []
        for c in conds:
            bctx = self.clone()
            st, why = bctx.check_and_assume(c, origin="branch", kind="branch")
            if st is NO:
                out.append(Branch(c, bctx, "empty"))
            else:
                out.append(Branch(c, bctx, "open"))
        return out

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

    def decide(self, fact):
        from cas.math.decide import decide as _decide
        return _decide(fact, self)

    def contradicted(self, fact):
        from cas.math.decide import contradicted as _contradicted
        return _contradicted(fact, self)


# ---------------------------------------------------------------------------
# TrackedContext：checker 读取上下文的唯一通道（v4 §6.11）
# ---------------------------------------------------------------------------

class TrackedContext:
    """checker 不直接读裸上下文，而读本对象——任何隐式使用都留下读依赖。

    不这样做就会出现「某步实际依赖一条假设，但步骤记录里没有体现」。读依赖
    按 `ContextReadSet` 累积，随 Step 落地；只有记录粒度随执行模式变化，判定
    结果与读取内容不受模式影响（AGENTS.md §四.3）。
    """

    def __init__(self, scopes, services, scope_id):
        self._scopes = scopes
        self._services = services
        self._sid = scope_id
        self._reads = []

    def _record(self, kind, key):
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

    def read_set(self):
        from cas.kernel.model import ContextReadSet
        seen = {}
        for k, val in self._reads:
            seen[k] = val
        return ContextReadSet(tuple(sorted(seen.items())))