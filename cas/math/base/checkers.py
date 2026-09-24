"""Checkers for the base module.

These checkers used to live in the workflow as wrappers around the old
verifiers and were moved to the mathematical side, because they verify
mathematics and living in the workflow would create a reverse dependency from
the workflow onto the math layer.

Checker protocol: `check(proposal, context, services) -> CheckResult`. The math
context is injected through `__init__` and kept as `self.ctx` (the kernel knows
no math context; a checker is registered as a factory `(math_context) -> checker`).
Two
invariant rules:

· the *instance* of the conclusion must be re-checked, never trust what the
  caller reports. Premise propositions are resolved by commit and back-filled
  into `proposal.premise_propositions`.
· the guard is determined and reported by the checker
  (`Accepted.direct_requirements`); the kernel builds Requirements from it and
  attempts discharge. A checker never decides itself whether a condition holds.

The shared helpers here are also reused by the calculus and equation checkers.
"""

from __future__ import annotations

from collections.abc import Sequence
from typing import TYPE_CHECKING, TypeGuard, TypeVar

from cas.kernel.commit import ResolvedProposal
from cas.kernel.context import TrackedContext
from cas.kernel.evidence import (
    Accepted,
    CheckResult,
    RefutationRejected,
    Rejected,
    UnknownResult,
)
from cas.kernel.services import KernelServices
from cas.kernel.verdict import No, Reason, Unknown, Verdict
from cas.math.base.equality import identity_verdict, normal_form
from cas.math.builder import CheckerRegistration, MathBuilder
from cas.math.decls import LiftPolicy
from cas.math.domcond import dom_condition
from cas.syntax import pattern as P
from cas.syntax import term as T
from cas.syntax.match import matches
from cas.syntax.pattern import PatternSubstitution
from cas.syntax.term import Expr, S, Sym, Term
from cas.syntax.termpath import free_vars, replace_at, subst, term_at
from cas.workflow.command import (
    BothSidesPayload,
    ClaimPayload,
    Command,
    Direction,
    MergePayload,
    RewritePayload,
    SplitPayload,
    SubstPayload,
    TransPayload,
    UsePayload,
    ValuationPayload,
)

if TYPE_CHECKING:
    from cas.math.context import MathContext
    from cas.math.rules import Rule

PayloadT = TypeVar("PayloadT")

# ---------------------------------------------------------------------------
# Shared helpers
# ---------------------------------------------------------------------------

def _is_piecewise(term: Term) -> TypeGuard[Expr]:
    from cas.math.piecewise import is_piecewise

    return is_piecewise(term)


def _ok(
    ctx: MathContext,
    proposal: ResolvedProposal,
    context: TrackedContext,
    extra: Sequence[Term] = (),
) -> Accepted:
    """Accept with de-duplicated direct requirements and tracked reads."""
    content = proposal.conclusions[0]
    requirements: list[Term] = []
    for requirement in tuple(dom_condition(ctx, content)) + tuple(extra):
        if requirement not in requirements:
            requirements.append(requirement)
    return Accepted(
        direct_requirements=tuple(requirements),
        reads=context.read_set(),
    )


def _is_equation(term: Term) -> TypeGuard[Expr]:
    return (
        isinstance(term, Expr)
        and isinstance(term.head, Sym)
        and term.head.name == "Eq"
    )


def _one_conclusion(proposal: ResolvedProposal) -> Term | Rejected:
    if len(proposal.conclusions) != 1:
        return Rejected(
            Reason.FRAGMENT,
            "checker accepts single-conclusion proposals only",
        )
    return proposal.conclusions[0]



def _command(proposal: ResolvedProposal) -> Command | None:
    """Decode the command envelope at a checker boundary."""
    raw = proposal.evidence.payload
    return raw if isinstance(raw, Command) else None


def _payload(
    proposal: ResolvedProposal,
    payload_type: type[PayloadT],
) -> PayloadT | None:
    """Decode one closed command payload, rejecting malformed evidence."""
    command = _command(proposal)
    if command is None:
        return None
    payload = command.payload
    return payload if isinstance(payload, payload_type) else None

def _premise(proposal: ResolvedProposal) -> Term | None:
    if not proposal.premise_propositions:
        return None
    return proposal.premise_propositions[0]


def _expand(context: TrackedContext, term: Term) -> Term:
    """Expand visible definitions before comparing terms."""
    from cas.math.definitions import expand

    return expand(context.lookup_definition, term)


def _defined(context: TrackedContext | None, symbol: Term) -> bool:
    """Whether a symbol is defined in the visible scope."""
    return (
        context is not None
        and context.lookup_definition(symbol) is not None
    )


def _identity(
    ctx: MathContext,
    content: Term,
    expected: Term,
    mismatch: str,
) -> CheckResult | None:
    """Return a typed refutation/unknown when a candidate is not the expected identity."""
    verdict = identity_verdict(ctx, content, expected)
    if verdict.is_yes():
        return None
    if isinstance(verdict, No):
        return RefutationRejected(verdict.evidence)
    if not isinstance(verdict, Unknown):
        raise TypeError("identity channel returned an unsupported verdict")
    return UnknownResult(
        verdict.reason,
        f"{mismatch} (identity undecided)",
    )


def _same_subst(
    first: PatternSubstitution,
    second: PatternSubstitution,
) -> bool:
    """Compare pattern substitutions by variable and interned term identity."""
    if set(first) != set(second):
        return False
    for name, first_value in first.items():
        second_value = second[name]
        if isinstance(first_value, tuple) or isinstance(second_value, tuple):
            if not (
                isinstance(first_value, tuple)
                and isinstance(second_value, tuple)
            ):
                return False
            if len(first_value) != len(second_value) or any(
                left is not right
                for left, right in zip(first_value, second_value)
            ):
                return False
        elif first_value is not second_value:
            return False
    return True


def _rule_conditions(
    rule: Rule,
    substitution: PatternSubstitution,
) -> tuple[Term, ...]:
    """Instantiate a rule guard into concrete direct requirements."""
    if rule.guard is None:
        return ()
    return (P.instantiate(rule.guard, substitution),)


# ---------------------------------------------------------------------------
# Checkers
# ---------------------------------------------------------------------------

class ClaimChecker:
    """Assert into the ledger: the command declares `registers_assumption`, so
    the workflow registers the proposition as a scope assumption once this commit
    succeeds.

    The checker verifies the claim from the command payload (the only legitimate
    route to the assumption.entry checker is a claim command), not from the
    scope: registration now happens after a successful commit, so a refused or
    undecided claim never pollutes the scope's assumptions. It reports the
    expression's own definedness conditions, so asserting `x/x` carries `x != 0`
    and later rewrites inherit it through the kernel.
    """
    id = "assumption.entry"

    def __init__(self, ctx: MathContext) -> None:
        self.ctx = ctx

    def check(
        self,
        proposal: ResolvedProposal,
        context: TrackedContext,
        services: KernelServices,
    ) -> CheckResult:
        content = _one_conclusion(proposal)
        if isinstance(content, Rejected):
            return content
        cmd = _command(proposal)
        if (cmd is None or not isinstance(cmd.payload, ClaimPayload)
                or not cmd.registers_assumption):
            return Rejected(Reason.FRAGMENT,
                            "assumption.entry requires a claim command")
        return _ok(self.ctx, proposal, context)


class BothSidesChecker:
    """Apply the same operation to both sides of an equation. mul/div need the
    operand to be nonzero, reported as a direct condition for the kernel to
    decide and discharge; the checker declares the condition rather than
    deciding it."""
    id = "both_sides.operate"

    def __init__(self, ctx: MathContext) -> None:
        self.ctx = ctx

    def check(
        self,
        proposal: ResolvedProposal,
        context: TrackedContext,
        services: KernelServices,
    ) -> CheckResult:
        content = _one_conclusion(proposal)
        if isinstance(content, Rejected):
            return content
        pred = _premise(proposal)
        if pred is None:
            return Rejected(Reason.FRAGMENT, "predecessor is not an equation")
        payload = _payload(proposal, BothSidesPayload)
        if payload is None:
            return Rejected(
                Reason.FRAGMENT,
                "both_sides requires a both-sides payload",
            )
        d = payload
        expanded_pred = _expand(context, pred)
        if not _is_equation(expanded_pred):
            return Rejected(Reason.FRAGMENT, "predecessor is not an equation")
        pred = expanded_pred
        content = _expand(context, content)
        lhs, rhs = pred.args
        op = d.op
        if op == "add":
            exp = T.eq(T.plus(lhs, d.operand), T.plus(rhs, d.operand))
        elif op == "sub":
            exp = T.eq(T.plus(lhs, T.neg(d.operand)),
                       T.plus(rhs, T.neg(d.operand)))
        elif op == "mul":
            exp = T.eq(T.times(lhs, d.operand), T.times(rhs, d.operand))
        elif op == "div":
            exp = T.eq(T.times(lhs, T.pw(d.operand, T.N(-1))),
                       T.times(rhs, T.pw(d.operand, T.N(-1))))
        else:
            return Rejected(Reason.FRAGMENT, f"unknown operation: {op}")
        bad = _identity(self.ctx, content, exp,
                        "content does not match the operation on the predecessor")
        if bad is not None:
            return bad
        extra: tuple[T.Term, ...] = ()
        if op in ("mul", "div"):
            extra = (T.mk(S("Ne"), (d.operand, T.ZERO)),)
        return _ok(self.ctx, proposal, context, extra)


class NormalizeChecker:
    """Rewrite to the domain normal form: the content equals the predecessor's
    domain normal form, with no rule search involved."""
    id = "equality.normalize"

    def __init__(self, ctx: MathContext) -> None:
        self.ctx = ctx

    def check(
        self,
        proposal: ResolvedProposal,
        context: TrackedContext,
        services: KernelServices,
    ) -> CheckResult:
        content = _one_conclusion(proposal)
        if isinstance(content, Rejected):
            return content
        pred = _premise(proposal)
        if pred is None:
            return Rejected(Reason.FRAGMENT, "missing predecessor")
        if _payload(proposal, RewritePayload) is None:
            return Rejected(Reason.FRAGMENT, "equality.normalize requires a rewrite payload")
        bad = _identity(self.ctx, _expand(context, content),
                        normal_form(self.ctx, _expand(context, pred)),
                        "content is not the domain normal form of the predecessor")
        if bad is not None:
            return bad
        return _ok(self.ctx, proposal, context)


class RuleInstanceChecker:
    """Declare one instance of a declared rule at (path, substitution).

    Only the given instance is verified, in four steps:
      1. look the rule up: a rule is data, not a search;
      2. the given substitution really is a match at that position, checked with
         the syntax-layer matcher, which is different from the proposer's
         *search* over paths and rules;
      3. the result really is the instantiation of that template under that
         substitution;
      4. the rest of the predecessor is preserved unchanged (only the path is
         rewritten).

    The checker imports no searcher such as `apply_rule` and traverses no paths.
    """
    id = "rule.instance"

    def __init__(self, ctx: MathContext) -> None:
        self.ctx = ctx

    def check(
        self,
        proposal: ResolvedProposal,
        context: TrackedContext,
        services: KernelServices,
    ) -> CheckResult:
        content = _one_conclusion(proposal)
        if isinstance(content, Rejected):
            return content
        pred = _premise(proposal)
        if pred is None:
            return Rejected(Reason.FRAGMENT, "missing predecessor")
        d = _payload(proposal, RewritePayload)
        if d is None:
            return Rejected(Reason.FRAGMENT, "rule.instance requires a rewrite payload")
        from cas.math.rules import declared_ruleset
        rule = declared_ruleset(self.ctx).rules.get(d.rule)
        if rule is None:
            return Rejected(Reason.FRAGMENT, f"unknown rule: {d.rule}")
        if d.substitution is None:
            return Rejected(Reason.FRAGMENT, "rule instance is missing a substitution")
        path = tuple(d.path)
        # Both sides are expanded consistently, so aliases are transparent to the
        # pointer comparison that pins the rewritten instance.
        pred = _expand(context, pred)
        content = _expand(context, content)
        try:
            sub_t = term_at(pred, path)
        except IndexError:
            return Rejected(Reason.FRAGMENT, f"path out of range: {path}")
        if not any(_same_subst(s, d.substitution)
                   for s in matches(rule.pattern, sub_t)):
            return Rejected(Reason.FRAGMENT, "the given substitution is not a match at that position")
        inst = _expand(context, P.instantiate(rule.template, d.substitution))
        if replace_at(pred, path, inst) is not content:
            return Rejected(Reason.FRAGMENT, "content is not the result of that instance")
        return _ok(self.ctx, proposal, context, _rule_conditions(rule, d.substitution))


class SubstChecker:
    """Substitution: replace a variable in the predecessor with a value, a purely
    syntactic operation."""
    id = "substitute"

    def __init__(self, ctx: MathContext) -> None:
        self.ctx = ctx

    def check(
        self,
        proposal: ResolvedProposal,
        context: TrackedContext,
        services: KernelServices,
    ) -> CheckResult:
        content = _one_conclusion(proposal)
        if isinstance(content, Rejected):
            return content
        pred = _premise(proposal)
        if pred is None:
            return Rejected(Reason.FRAGMENT, "missing predecessor")
        pred = _expand(context, pred)
        content = _expand(context, content)
        d = _payload(proposal, SubstPayload)
        if d is None:
            return Rejected(Reason.FRAGMENT, "substitute requires a substitution payload")
        # The key and the occurrence are part of what the step claims: a compound
        # key is not a variable, and substituting a variable that does not occur
        # would commit a step whose name says something that did not happen.
        if not isinstance(d.var, T.Sym):
            return Rejected(Reason.FRAGMENT,
                            "the substitution key must be a single variable")
        if d.var not in free_vars(pred):
            return Rejected(Reason.FRAGMENT,
                            f"the substituted variable does not occur in the predecessor: {d.var}")
        substituted = subst(pred, {d.var: d.value})
        last: Verdict | None = None
        for expected in (substituted, normal_form(self.ctx, substituted)):
            verdict = identity_verdict(self.ctx, content, expected)
            if verdict.is_yes():
                return _ok(self.ctx, proposal, context)
            last = verdict
        if last is None:
            return UnknownResult(Reason.FRAGMENT, "substitution identity unavailable")
        if isinstance(last, No):
            return RefutationRejected(last.evidence)
        if not isinstance(last, Unknown):
            raise TypeError("substitution identity returned an unsupported verdict")
        return UnknownResult(last.reason, "substitution identity undecided")


class SplitChecker:
    """Conditional branch split: content is equivalent to
    predecessor and (not) condition."""
    id = "branch.split"

    def __init__(self, ctx: MathContext) -> None:
        self.ctx = ctx

    def check(
        self,
        proposal: ResolvedProposal,
        context: TrackedContext,
        services: KernelServices,
    ) -> CheckResult:
        content = _one_conclusion(proposal)
        if isinstance(content, Rejected):
            return content
        pred = _premise(proposal)
        if pred is None:
            return Rejected(Reason.FRAGMENT, "missing predecessor")
        d = _payload(proposal, SplitPayload)
        if d is None:
            return Rejected(Reason.FRAGMENT, "branch.split requires a split payload")
        cond = d.condition
        branch = T.not_(cond) if d.negate else cond
        expected = T.mk(S("And"), (_expand(context, pred), branch))
        if content is expected:
            return _ok(self.ctx, proposal, context)
        verdict = identity_verdict(ctx=self.ctx, left=_expand(context, content), right=expected)
        if verdict.is_yes():
            return _ok(self.ctx, proposal, context)
        if isinstance(verdict, No):
            return RefutationRejected(verdict.evidence)
        if not isinstance(verdict, Unknown):
            raise TypeError("identity channel returned an unsupported verdict")
        return UnknownResult(verdict.reason, "branch equivalence undecided")


def _is_tautology(term: Term) -> bool:
    """Syntactic tautology: a disjunction containing a complementary pair
    (`c` and `not c`), or the constant true.

    The test lives on the verification side and does not rely on
    construction-time collapse, keeping verification independent of
    construction. Only the law of excluded middle is recognized; any other
    coverage needs a real proof.
    """
    if isinstance(term, T.BVal):
        return term.val
    if not (isinstance(term, T.Expr) and term.head.name == "Or"):
        return False
    disjuncts = {argument._h for argument in term.args}
    return any(
        isinstance(argument, T.Expr)
        and argument.head.name == "Not"
        and argument.args[0]._h in disjuncts
        for argument in term.args
    )


class BranchCoverageChecker:
    """Branch coverage: whether the disjunction of the branch conditions covers
    the parent problem.

    Only a syntactic tautology is recognized, namely the law of excluded middle
    `c or not c`. The decision is made here independently and does not rely on
    the constructor collapsing complementary pairs to true. Non-complementary
    coverage needs a real coverage proof, so this honestly returns undecided
    rather than pretending.
    """
    id = "branch.coverage"

    def __init__(self, ctx: MathContext) -> None:
        self.ctx = ctx

    def check(
        self,
        proposal: ResolvedProposal,
        context: TrackedContext,
        services: KernelServices,
    ) -> CheckResult:
        content = _one_conclusion(proposal)
        if isinstance(content, Rejected):
            return content
        if _is_tautology(content):
            return Accepted()
        return UnknownResult(Reason.FRAGMENT, "coverage is not a syntactic tautology; a real coverage proof is needed")


class BranchMergeChecker:
    """Branch merge: reason by cases.

    Each branch concludes the same proposition P in its own scope and the
    disjunction of the branch conditions covers the parent problem, so P holds in
    the parent scope; each branch's open guards are promoted to `C_i => G_i`.

    **Boundary that must be known**: a branch conclusion cannot be a premise of
    the parent scope, because commit's second step forbids using a child-scope
    conclusion upward, so the only premise here is the coverage conclusion in the
    parent. The "each branch really answered P" loop is therefore checked by the
    workflow against the kernel record (`Judgment.scope` and
    `Judgment.proposition`) rather than recomputed independently by this checker;
    what this checker re-checks is that premise, payload and conclusion agree,
    namely that the coverage proposition equals the disjunction of the payload's
    branch conditions (so the payload is pinned by the committed coverage
    conclusion), that the number of answers equals the number of branches, and
    that every answer is exactly the conclusion P.

    Making that loop independently re-checked by the kernel would need commit to
    support implication introduction, from Gamma plus C proving P to Gamma
    proving C implies P, which is a new kernel rule and a design decision not yet
    taken.
    """
    id = "branch.merge"

    def __init__(self, ctx: MathContext) -> None:
        self.ctx = ctx

    def check(
        self,
        proposal: ResolvedProposal,
        context: TrackedContext,
        services: KernelServices,
    ) -> CheckResult:
        content = _one_conclusion(proposal)
        if isinstance(content, Rejected):
            return content
        d = _payload(proposal, MergePayload)
        if d is None:
            return Rejected(Reason.FRAGMENT, "branch.merge requires a merge payload")
        coverage = T.or_(*d.conditions)
        if not any(p is coverage for p in proposal.premise_propositions):
            return Rejected(Reason.FRAGMENT, "the premise does not contain this branch group's coverage proposition")
        if len(d.answers) != len(d.conditions):
            return Rejected(Reason.FRAGMENT,
                            f"branch answer count {len(d.answers)} does not match "
                            f"branch count {len(d.conditions)}")
        if any(a is not content for a in d.answers):
            return Rejected(Reason.FRAGMENT, "not every branch answered the same proposition")
        promoted = tuple(T.implies(c, g)
                         for c, gs in zip(d.conditions, d.guards) for g in gs)
        return Accepted(direct_requirements=tuple(dom_condition(self.ctx, content)) + promoted,
                        reads=context.read_set())


class ConstraintSatisfiedChecker:
    """Constraint satisfaction.

    The payload is a (constraint, valuation) pair. The checker re-checks two
    things:

      1. the conclusion really is that constraint's instance under that
         valuation, by syntactic identity, without trusting the caller's report;
      2. that instance vanishes in the current context, using independent
         facilities (domain normal form, identity decision, domain analysis) and
         never re-running the solver.

    Finding the valuation is the solver's job on the untrusted side and may be
    wrong; what may be claimed is decided here. When vanishing is outside the
    projection this honestly returns undecided.
    """
    id = "constraint.satisfied"

    def __init__(self, ctx: MathContext) -> None:
        self.ctx = ctx

    def check(
        self,
        proposal: ResolvedProposal,
        context: TrackedContext,
        services: KernelServices,
    ) -> CheckResult:
        content = _one_conclusion(proposal)
        if isinstance(content, Rejected):
            return content
        d = _payload(proposal, ValuationPayload)
        if d is None:
            return Rejected(Reason.FRAGMENT, "constraint.satisfied requires a valuation payload")
        rel = _expand(context, d.constraint.relation)
        inst = subst(rel, dict(d.valuation))
        if _expand(context, content) is not _expand(context, inst):
            return Rejected(Reason.FRAGMENT, "content is not this constraint's instance under that valuation")
        # The instance is re-checked as an **identity** in the free symbols that
        # remain after the valuation: a construction constraint must vanish as a
        # function, so a demonstrably nonzero difference is evidence of a wrong
        # valuation, while an uncovered (non-identity) shape stays undecided.
        if _is_equation(inst):
            bad = _identity(
                self.ctx,
                inst.args[0],
                inst.args[1],
                "the constraint does not hold under this valuation",
            )
            if bad is not None:
                return bad
            return _ok(self.ctx, proposal, context)
        verdict = context.decide(inst)
        if verdict.is_yes():
            return _ok(self.ctx, proposal, context)
        if isinstance(verdict, No):
            return RefutationRejected(verdict.evidence)
        if not isinstance(verdict, Unknown):
            raise TypeError("decision service returned an unsupported verdict")
        return UnknownResult(
            verdict.reason,
            "constraint instance vanishing undecided",
        )


class TransChecker:
    """Compose two equality premises in the registered equality module."""

    id = "equality.trans"

    def __init__(self, ctx: MathContext) -> None:
        self.ctx = ctx

    def check(
        self,
        proposal: ResolvedProposal,
        context: TrackedContext,
        services: KernelServices,
    ) -> CheckResult:
        content = _one_conclusion(proposal)
        if isinstance(content, Rejected):
            return content
        if len(proposal.premise_propositions) != 2:
            return Rejected(Reason.FRAGMENT, "transitivity needs exactly two premises")
        first, second = (_expand(context, proposition) for proposition in proposal.premise_propositions)
        if not _is_equation(first) or not _is_equation(second):
            return Rejected(Reason.FRAGMENT, "transitivity premises must be equalities")
        if first.args[1] is not second.args[0]:
            return Rejected(Reason.FRAGMENT, "the middle equality terms do not match")
        expected = T.eq(first.args[0], second.args[1])
        d = _payload(proposal, TransPayload)
        if d is None:
            return Rejected(Reason.FRAGMENT, "equality.trans requires a trans payload")
        if d.value != (first.args[0], first.args[1], second.args[1]):
            return Rejected(Reason.FRAGMENT,
                            "transitivity evidence payload does not match the premises")
        if _expand(context, content) is not expected:
            return Rejected(Reason.FRAGMENT, "conclusion is not the transitive equality")
        return _ok(self.ctx, proposal, context)


def _path_requirements(target: Term, path: tuple[int, ...]) -> tuple[Term, ...]:
    """Return branch conditions for a replacement inside a Piecewise value."""
    current = target
    requirements: list[Term] = []
    for index in path:
        if _is_piecewise(current) and index % 2 == 0:
            requirements.append(current.args[index + 1])
        current = term_at(current, (index,))
    return tuple(requirements)


class CongruenceLiftChecker:
    """Verify one explicitly located equality replacement."""

    id = "congruence.lift"

    def __init__(self, ctx: MathContext) -> None:
        self.ctx = ctx

    def check(
        self,
        proposal: ResolvedProposal,
        context: TrackedContext,
        services: KernelServices,
    ) -> CheckResult:
        content = _one_conclusion(proposal)
        if isinstance(content, Rejected):
            return content
        if len(proposal.premise_propositions) != 2:
            return Rejected(Reason.FRAGMENT, "use needs an equality and a target premise")
        source, target = (
            _expand(context, proposition)
            for proposition in proposal.premise_propositions
        )
        if not _is_equation(source):
            return Rejected(Reason.FRAGMENT, "use source is not an equality")
        d = _payload(proposal, UsePayload)
        if d is None:
            return Rejected(Reason.FRAGMENT, "congruence.lift requires a use payload")
        if d.direction is Direction.RIGHT:
            before, after = source.args
        elif d.direction is Direction.LEFT:
            before, after = source.args[1], source.args[0]
        else:
            return Rejected(Reason.FRAGMENT, "use direction must be -> or <-")
        try:
            subterm = term_at(target, tuple(d.path))
        except (IndexError, TypeError):
            return Rejected(Reason.FRAGMENT, "use path is outside the target")
        bad = _identity(self.ctx, subterm, before,
                        "the target subterm is not the selected side of the equality")
        if bad is not None:
            return bad
        if not d.path:
            return Rejected(Reason.FRAGMENT, "an empty path cannot select a replacement site")
        try:
            parent = term_at(target, tuple(d.path[:-1]))
        except (IndexError, TypeError):
            return Rejected(Reason.FRAGMENT, "use path is outside the target")
        extra: list[Term] = []
        policy: LiftPolicy
        if isinstance(parent, T.Expr):
            head = parent.head.name
            if head in ("Derivative", "Quote"):
                return Rejected(
                    Reason.FRAGMENT,
                    f"{head} does not admit equality lifting",
                )
            if head == "Power":
                if d.path[-1] != 0 or not isinstance(parent.args[1], T.Int):
                    return Rejected(
                        Reason.FRAGMENT,
                        "only an integer exponent permits base lifting",
                    )
            if head in ("Integrate", "DefIntegrate"):
                extra.append(source)
            if head in ("Plus", "Times", "Eq"):
                policy = LiftPolicy.CONGRUENT
            elif head in ("Power", "Piecewise", "Integrate", "DefIntegrate"):
                policy = LiftPolicy.CONDITIONAL
            else:
                policy = self.ctx.lift_policy(head)
        else:
            policy = (
                LiftPolicy.CONGRUENT
                if isinstance(parent, T.Bound)
                else LiftPolicy.FORBIDDEN
            )
        extra.extend(_path_requirements(target, tuple(d.path)))
        if policy is LiftPolicy.FORBIDDEN:
            detail = (
                f"no lifting policy is declared for {parent.head.name}"
                if isinstance(parent, T.Expr)
                else "only expression subterms are liftable"
            )
            return Rejected(Reason.FRAGMENT, detail)
        expected = replace_at(target, tuple(d.path), after)
        bad = _identity(self.ctx, content, expected,
                        "content is not the selected replacement")
        if bad is not None:
            return bad
        return _ok(self.ctx, proposal, context, tuple(extra))


CHECKERS = (ClaimChecker, BothSidesChecker, NormalizeChecker,
            RuleInstanceChecker, SubstChecker, SplitChecker,
            BranchCoverageChecker, BranchMergeChecker,
            ConstraintSatisfiedChecker, TransChecker, CongruenceLiftChecker)


def register(builder: MathBuilder) -> None:
    """Register this module's checker factories during explicit assembly."""
    for checker in CHECKERS:
        builder.register_checker(CheckerRegistration(checker.id, checker))
