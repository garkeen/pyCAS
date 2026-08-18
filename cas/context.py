from dataclasses import dataclass

from cas import term as T
from cas.decide import decide as _decide
from cas.decide import contradicted as _contradicted
from cas.decide import domain_ok as _domain_ok
from cas.decide import T3


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
    def __init__(self):
        self.entries = []
        self.marks = []

    def assume(self, fact, origin="user", kind="fact"):
        e = Entry(fact, kind, origin)
        self.entries.append(e)
        return e

    def check_and_assume(self, fact, origin="user", kind="fact"):
        if _domain_ok(fact, self) is T3.NO:
            return T3.NO, "domain"
        if _contradicted(fact, self):
            return T3.NO, "contradiction"
        self.assume(fact, origin=origin, kind=kind)
        return T3.YES, None

    def clone(self):
        c = self.__class__()
        c.entries = list(self.entries)
        return c

    def branch(self, *conds):
        out = []
        for c in conds:
            bctx = self.clone()
            st, why = bctx.check_and_assume(c, origin="branch", kind="branch")
            if st is T3.NO:
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
        return _decide(fact, self)

    def contradicted(self, fact):
        return _contradicted(fact, self)