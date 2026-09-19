"""Rule engine: the single rewriting engine of the whole system.

Rules come only from run-time declarations, installed by bootstrap. Guard
decisions go through the decision pipeline (the Verdict ADT); there is no second
rule mechanism and no second guard vocabulary.

Consumers:
· `simplify.autosimplify` runs the auto rules to a fixed point (automatic
  channel);
· the REPL `apply` command applies one rule at a chosen location (interactive
  channel).
Both share `apply_rule`, and verification goes through the workflow's Rewrite
step.
"""

from dataclasses import dataclass

from cas.syntax import term as T
from cas.syntax import pattern as P
from cas.syntax.match import identity_element, matches
from cas.kernel.verdict import YES, NO, unknown

_DECLS = None


def bind_runtime(rt):
    """Inject the declaration query surface at assembly time.

    The dependency direction is runtime -> math and the reverse is forbidden, so
    a math module must not import runtime; declarations are injected during
    assembly instead.

    Querying before injection raises rather than returning None: a silent None
    would turn "forgot to assemble" into a hard-to-find wrong answer, whereas
    "no such name" is a different case that still returns None.
    """
    global _DECLS
    _DECLS = rt


def _R():
    if _DECLS is None:
        raise RuntimeError(
            "not assembled: call cas.runtime.bootstrap() first")
    return _DECLS



@dataclass(frozen=True)
class Rule:
    id: str
    pattern: object               # a Pattern; a pattern is not a term
    template: object              # a Pattern; instantiation yields a Term
    guard: object = None          # Pattern | None (a condition is also a pattern, with holes)
    auto: bool = False
    priority: int = 100           # try order among rules at the same position (lower first)


@dataclass
class ApplyResult:
    ok: bool
    guard: object                 # Verdict; only YES may land
    term: T.Term = None
    subst: dict = None
    rule_id: str = ""


def root_key(p):
    """Rule index key (pattern-level; holes map to '*')."""
    return P.root_key(p)


def _matches_any_root(p):
    """Whether a pattern can match a subterm whose root is any head.

    A hole matches anything; a call of a head with an identity element reaches
    through the OneIdentity channel even when the target's root is a different
    head. Only a literal and a call of an identity-free head are confined to
    their own root key.
    """
    if isinstance(p, T.Term):
        return False
    if p.__class__ is P.PatternCall:
        return identity_element(p.head.name) is not None
    return True


class RuleSet:
    """Rule storage plus a root-key index that narrows match candidates.

    `index` maps a pattern's root key to the rules whose pattern can only match
    at that root; `_universal` holds the rules whose pattern can match under any
    root. `candidates` returns the union in insertion order, so narrowing proves
    a rule cannot match instead of guessing, and the set and order of match
    attempts are unchanged.
    """

    def __init__(self):
        self.rules = {}
        self.index = {}
        self._universal = []
        self._seq = {}
        self._next_seq = 0

    def _detach(self, rule):
        if _matches_any_root(rule.pattern):
            if rule in self._universal:
                self._universal.remove(rule)
            return
        key = root_key(rule.pattern)
        lst = self.index.get(key)
        if lst and rule in lst:
            lst.remove(rule)
            if not lst:
                del self.index[key]

    def add(self, rule):
        old = self.rules.pop(rule.id, None)
        if old is not None:
            self._detach(old)
        self.rules[rule.id] = rule
        self._seq[rule.id] = self._next_seq
        self._next_seq += 1
        if _matches_any_root(rule.pattern):
            self._universal.append(rule)
        else:
            self.index.setdefault(root_key(rule.pattern), []).append(rule)

    def remove(self, rid):
        r = self.rules.pop(rid, None)
        if r is not None:
            self._detach(r)
            self._seq.pop(rid, None)

    def ids(self):
        return list(self.rules)

    def candidates(self, tgt):
        """The rules whose pattern can match `tgt` at a root position, in
        insertion order.

        Soundness: a match at a root position requires the pattern's root key
        to equal the target's (a literal matches only an identical term, an
        identity-free call only an Expr with the same interned head), or the
        pattern to be a hole or an identity-element call, which matches every
        term. Everything else is left out, and no matchable rule is lost.
        """
        bucket = self.index.get(root_key(tgt), ())
        if not self._universal:
            return tuple(bucket)
        if not bucket:
            return tuple(self._universal)
        merged = list(bucket) + list(self._universal)
        merged.sort(key=lambda r: self._seq[r.id])
        return tuple(merged)


def apply_rule(rule, expr, path, guard_eval=None, budget=10000):
    """Try to apply a rule at `path` in `expr`.

    guard_eval: (guard_term, subst) -> Verdict. The default (no guard) counts as
    YES; a guarded rule with no evaluator counts as UNKNOWN and honestly does not
    land.
    """
    sub_t = T.term_at(expr, path)
    for sub in matches(rule.pattern, sub_t, budget=budget):
        if rule.guard is None:
            g = YES
        else:
            g = guard_eval(rule.guard, sub) if guard_eval else unknown()
        if g is YES:
            inst = P.instantiate(rule.template, sub)
            after = T.replace_at(expr, path, inst)
            return ApplyResult(True, YES, after, sub, rule.id)
        if g is NO:
            continue
        return ApplyResult(False, g, expr, sub, rule.id)
    return ApplyResult(False, None, expr, None, rule.id)


_LIB_RULESETS = {}


def declared_ruleset() -> RuleSet:
    """Build the rule set from run-time declarations, cached per runtime.

    The cache is keyed by the identity of the assembled runtime, so a re-assembly
    that changes the rule text (a second bootstrap with different declarations)
    reparses rather than serving a stale ruleset. The declarations carry rule-line
    strings as pure data and DSL parsing happens at this consumption point, so a
    math module never imports this module back. A corrupt rule line is a
    declaration defect: the parse error propagates and is never swallowed.
    """
    rt = _R()
    rs = _LIB_RULESETS.get(id(rt))
    if rs is None:
        # Deferred import: this is the back edge of the
        # cas.math.rules <-> cas.math.loader cycle. loader imports Rule at its
        # top, so importing loader at the top here would have both sides hit a
        # half-initialized module. The cycle exists because the parsed product of
        # the rule-line DSL is a Rule and the assembly point is this module.
        from cas.math.loader import parse_rule_line
        rs = RuleSet()
        for line in rt.rules:
            rs.add(parse_rule_line(line))
        _LIB_RULESETS[id(rt)] = rs
    return rs
