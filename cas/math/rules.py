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

from __future__ import annotations

from dataclasses import dataclass
from types import MappingProxyType
from typing import TYPE_CHECKING, Callable, Mapping, TypeAlias

from cas.syntax import pattern as P
from cas.syntax import term as T
from cas.syntax.match import identity_element, matches
from cas.syntax.termpath import replace_at, term_at

if TYPE_CHECKING:
    from cas.math.context import MathContext
from cas.kernel.verdict import YES, No, Refutation, Verdict, unknown

PatternLike: TypeAlias = T.Term | P.Pattern
SubstitutionValue: TypeAlias = T.Term | tuple[T.Term, ...]
Substitution: TypeAlias = Mapping[str, SubstitutionValue]


@dataclass(frozen=True, slots=True)
class AutoRule:
    """A rule admitted to the automatic channel; it cannot carry a guard."""

    id: str
    pattern: PatternLike
    template: PatternLike
    priority: int = 100

    @property
    def auto(self) -> bool:
        return True

    @property
    def guard(self) -> None:
        return None



@dataclass(frozen=True, slots=True)
class ManualRule:
    """An unconditional rule reserved for the explicit interactive channel."""

    id: str
    pattern: PatternLike
    template: PatternLike
    priority: int = 100

    @property
    def auto(self) -> bool:
        return False

    @property
    def guard(self) -> None:
        return None


@dataclass(frozen=True, slots=True)
class GuardedRule:
    """An interactive rule with one mandatory condition pattern."""

    id: str
    pattern: PatternLike
    template: PatternLike
    condition: PatternLike
    priority: int = 100

    @property
    def auto(self) -> bool:
        return False

    @property
    def guard(self) -> PatternLike:
        return self.condition


Rule: TypeAlias = AutoRule | ManualRule | GuardedRule


class ApplyResult:
    """Closed result base; callers inspect variants, not arbitrary fields."""

    __slots__ = ()

    @property
    def ok(self) -> bool:
        return isinstance(self, Applied)


@dataclass(frozen=True, slots=True)
class Applied(ApplyResult):
    term: T.Term
    substitution: Substitution
    guard: Verdict
    rule_id: str

    @property
    def subst(self) -> Substitution:
        return self.substitution


@dataclass(frozen=True, slots=True)
class ApplyFailed(ApplyResult):
    term: T.Term
    substitution: Substitution | None
    guard: Verdict
    rule_id: str
    refutations: tuple[Refutation, ...] = ()

    @property
    def subst(self) -> Substitution | None:
        return self.substitution

def root_key(p: PatternLike) -> str:
    """Rule index key (pattern-level; holes map to '*')."""
    return P.root_key(p)


def _matches_any_root(p: PatternLike) -> bool:
    """Whether a pattern can match a subterm rooted at any head."""
    if isinstance(p, T.Term):
        return False
    if p.__class__ is P.PatternCall:
        return identity_element(p.head.name) is not None
    return True


class RuleSet:
    """Rule storage plus a root-key index that narrows match candidates."""

    def __init__(self) -> None:
        self.rules: dict[str, Rule] = {}
        self.index: dict[str, list[Rule]] = {}
        self._universal: list[Rule] = []
        self._seq: dict[str, int] = {}
        self._next_seq = 0

    def _detach(self, rule: Rule) -> None:
        if _matches_any_root(rule.pattern):
            if rule in self._universal:
                self._universal.remove(rule)
            return
        key = root_key(rule.pattern)
        bucket = self.index.get(key)
        if bucket and rule in bucket:
            bucket.remove(rule)
            if not bucket:
                del self.index[key]

    def add(self, rule: Rule) -> None:
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


    def remove(self, rid: str) -> None:
        rule = self.rules.pop(rid, None)
        if rule is not None:
            self._detach(rule)
            self._seq.pop(rid, None)

    def ids(self) -> list[str]:
        return list(self.rules)

    def candidates(self, tgt: PatternLike) -> tuple[Rule, ...]:
        """Return rules that can match `tgt` at its root, in insertion order."""
        bucket = self.index.get(root_key(tgt), ())
        if not self._universal:
            return tuple(bucket)
        if not bucket:
            return tuple(self._universal)
        merged = list(bucket) + list(self._universal)
        merged.sort(key=lambda rule: self._seq[rule.id])
        return tuple(merged)


@dataclass(frozen=True, slots=True)
class RuleCatalog:
    """Immutable rule lookup and root index owned by one MathContext."""

    rules: Mapping[str, Rule]
    _index: Mapping[str, tuple[Rule, ...]]
    _universal: tuple[Rule, ...]
    _sequence: Mapping[str, int]

    @classmethod
    def from_set(cls, source: RuleSet) -> RuleCatalog:
        return cls(
            rules=MappingProxyType(dict(source.rules)),
            _index=MappingProxyType({
                key: tuple(bucket) for key, bucket in source.index.items()
            }),
            _universal=tuple(source._universal),
            _sequence=MappingProxyType(dict(source._seq)),
        )

    def ids(self) -> tuple[str, ...]:
        return tuple(self.rules)

    def candidates(self, target: PatternLike) -> tuple[Rule, ...]:
        bucket = self._index.get(root_key(target), ())
        if not self._universal:
            return bucket
        if not bucket:
            return self._universal
        merged = [*bucket, *self._universal]
        merged.sort(key=lambda rule: self._sequence[rule.id])
        return tuple(merged)


def apply_rule(
    rule: Rule,
    expr: T.Term,
    path: tuple[int, ...],
    guard_eval: Callable[[PatternLike, Substitution], Verdict] | None = None,
    budget: int = 10000,
) -> ApplyResult:
    """Try to apply a rule at `path` in `expr`.

    `guard_eval` has shape `(condition, substitution) -> Verdict`. An automatic
    rule is always evaluated as YES; a guarded rule without an evaluator is
    honestly UNKNOWN and cannot land.
    """
    sub_t = term_at(expr, path)
    refutations: list[Refutation] = []
    for substitution in matches(rule.pattern, sub_t, budget=budget):
        verdict: Verdict
        if rule.auto or rule.guard is None:
            verdict = YES
        else:
            verdict = guard_eval(rule.guard, substitution) if guard_eval else unknown()
        if verdict is YES:
            instance = P.instantiate(rule.template, substitution)
            after = replace_at(expr, path, instance)
            return Applied(after, substitution, verdict, rule.id)
        if isinstance(verdict, No):
            refutations.append(verdict.evidence)
            continue
        return ApplyFailed(
            expr,
            substitution,
            verdict,
            rule.id,
            tuple(refutations),
        )
    return ApplyFailed(
        expr,
        None,
        unknown(),
        rule.id,
        tuple(refutations),
    )


def declared_ruleset(ctx: MathContext) -> RuleCatalog:
    """Return the immutable rule catalog carried by ``ctx``."""
    return ctx.rule_catalog
