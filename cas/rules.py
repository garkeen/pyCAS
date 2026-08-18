from dataclasses import dataclass, field

from cas import term as T
from cas.match import matches


@dataclass(frozen=True)
class Rule:
    id: str
    pattern: T.Term
    template: T.Term
    guard: object = None
    direction: str = None
    channels: tuple = ("manual", "suggest")
    auto: bool = False
    origin: str = "user"


@dataclass
class Step:
    sid: int
    rule_id: str
    path: tuple
    before: T.Term
    after: T.Term
    guard: str
    dcost: int


@dataclass
class ApplyResult:
    ok: bool
    guard: str
    term: T.Term = None
    subst: dict = None


def root_key(p):
    if isinstance(p, T.Expr):
        return p.head.name
    if isinstance(p, (T.PatVar, T.PatSeq)):
        return "*"
    return p.__class__.__name__ + ":" + repr(p)


class RuleSet:
    def __init__(self):
        self.rules = {}
        self.index = {}

    def add(self, rule):
        self.rules[rule.id] = rule
        self.index.setdefault(root_key(rule.pattern), []).append(rule)

    def remove(self, rid):
        r = self.rules.pop(rid, None)
        if r:
            lst = self.index.get(root_key(r.pattern), [])
            if r in lst:
                lst.remove(r)

    def for_term(self, t):
        seen = set()
        keys = ["*"]
        if isinstance(t, T.Expr):
            keys.append(t.head.name)
        else:
            keys.append(t.__class__.__name__ + ":" + repr(t))
        for k in keys:
            for r in self.index.get(k, ()):
                if r.id not in seen:
                    seen.add(r.id)
                    yield r

    def ids(self):
        return list(self.rules)


def apply_rule(rule, expr, path, guard_eval=None, budget=10000):
    sub_t = T.term_at(expr, path)
    for sub in matches(rule.pattern, sub_t, budget=budget):
        if rule.guard is None:
            g = "YES"
        else:
            g = guard_eval(rule.guard, sub) if guard_eval else "UNKNOWN"
        if g == "YES":
            inst = T.instantiate(rule.template, sub)
            after = T.replace_at(expr, path, inst)
            return ApplyResult(True, "YES", after, sub)
        if g == "NO":
            continue
        return ApplyResult(False, "UNKNOWN", expr, sub)
    return ApplyResult(False, "NOMATCH", expr, None)
