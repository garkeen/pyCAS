"""Checkers for the base module.

These checkers used to live in the workflow as wrappers around the old
verifiers and were moved to the mathematical side, because they verify
mathematics and living in the workflow would create a reverse dependency from
the workflow onto the math layer.

Checker protocol: `check(proposal, context, services) -> CheckResult`. Two
invariant rules:

· the *instance* of the conclusion must be re-checked, never trust what the
  caller reports. Premise propositions are resolved by commit and back-filled
  into `proposal.premise_propositions`.
· the guard is determined and reported by the checker
  (`Accepted.direct_requirements`); the kernel builds Requirements from it and
  attempts discharge. A checker never decides itself whether a condition holds.

The shared helpers here are also reused by the calculus and equation checkers.
"""

from cas.syntax import term as T
from cas.syntax import pattern as P
from cas.syntax.term import S
from cas.syntax.match import matches
from cas.kernel.evidence import Accepted, Rejected, UnknownResult
from cas.kernel.verdict import Reason
from cas.math.domcond import dom_condition
from cas.math.base.equality import equal, normal_form


# ---------------------------------------------------------------------------
# Shared helpers
# ---------------------------------------------------------------------------

def _is_piecewise(t) -> bool:
    from cas.math.piecewise import is_piecewise
    return is_piecewise(t)


def _ok(proposal, context, extra=()):
    """Accept, reporting the direct conditions: the content's definedness
    constraints plus any type-specific conditions."""
    content = proposal.conclusions[0]
    reqs = tuple(dom_condition(content)) + tuple(extra)
    return Accepted(direct_requirements=reqs, reads=context.read_set())


def _one_conclusion(proposal):
    if len(proposal.conclusions) != 1:
        return None, Rejected(Reason.FRAGMENT, "checker accepts single-conclusion proposals only")
    return proposal.conclusions[0], None


def _premise(proposal):
    if not proposal.premise_propositions:
        return None
    return proposal.premise_propositions[0]


def _same_subst(a, b):
    """Whether two substitutions agree hole by hole (terms by pointer, sequences
    element-wise by pointer)."""
    if set(a) != set(b):
        return False
    for k, va in a.items():
        vb = b[k]
        if isinstance(va, tuple) or isinstance(vb, tuple):
            if not (isinstance(va, tuple) and isinstance(vb, tuple)):
                return False
            if len(va) != len(vb) or any(x is not y for x, y in zip(va, vb)):
                return False
        elif va is not vb:
            return False
    return True


def _rule_conditions(rule, subst):
    """Instantiate the rule guard into concrete conditions. The checker reports
    conditions; deciding and discharging them belongs to the kernel."""
    if rule.guard is None:
        return ()
    return (P.instantiate(rule.guard, subst),)


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

    def check(self, proposal, context, services):
        content, bad = _one_conclusion(proposal)
        if bad is not None:
            return bad
        cmd = proposal.evidence.payload
        if not getattr(cmd, "registers_assumption", False):
            return Rejected(Reason.FRAGMENT,
                            "assumption.entry requires a claim command")
        return _ok(proposal, context)


class BothSidesChecker:
    """Apply the same operation to both sides of an equation. mul/div need the
    operand to be nonzero, reported as a direct condition for the kernel to
    decide and discharge; the checker declares the condition rather than
    deciding it."""
    id = "both_sides.operate"

    def check(self, proposal, context, services):
        content, bad = _one_conclusion(proposal)
        if bad is not None:
            return bad
        pred = _premise(proposal)
        if pred is None or not T.is_eq(pred):
            return Rejected(Reason.FRAGMENT, "predecessor is not an equation")
        d = proposal.evidence.payload
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
        if not equal(content, exp):
            return Rejected(Reason.FRAGMENT, "content does not match the operation on the predecessor")
        extra = ()
        if op in ("mul", "div"):
            extra = (T.mk(S("Ne"), (d.operand, T.ZERO)),)
        return _ok(proposal, context, extra)


class NormalizeChecker:
    """Rewrite to the domain normal form: the content equals the predecessor's
    domain normal form, with no rule search involved."""
    id = "equality.normalize"

    def check(self, proposal, context, services):
        content, bad = _one_conclusion(proposal)
        if bad is not None:
            return bad
        pred = _premise(proposal)
        if pred is None:
            return Rejected(Reason.FRAGMENT, "missing predecessor")
        if equal(content, normal_form(pred)):
            return _ok(proposal, context)
        return Rejected(Reason.FRAGMENT, "content is not the domain normal form of the predecessor")


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

    def check(self, proposal, context, services):
        content, bad = _one_conclusion(proposal)
        if bad is not None:
            return bad
        pred = _premise(proposal)
        if pred is None:
            return Rejected(Reason.FRAGMENT, "missing predecessor")
        d = proposal.evidence.payload
        from cas.math.rules import declared_ruleset
        rule = declared_ruleset().rules.get(d.rule)
        if rule is None:
            return Rejected(Reason.FRAGMENT, f"unknown rule: {d.rule}")
        if d.substitution is None:
            return Rejected(Reason.FRAGMENT, "rule instance is missing a substitution")
        path = tuple(d.path)
        try:
            sub_t = T.term_at(pred, path)
        except IndexError:
            return Rejected(Reason.FRAGMENT, f"path out of range: {path}")
        if not any(_same_subst(s, d.substitution)
                   for s in matches(rule.pattern, sub_t)):
            return Rejected(Reason.FRAGMENT, "the given substitution is not a match at that position")
        inst = P.instantiate(rule.template, d.substitution)
        if T.replace_at(pred, path, inst) is not content:
            return Rejected(Reason.FRAGMENT, "content is not the result of that instance")
        return _ok(proposal, context, _rule_conditions(rule, d.substitution))


class SubstChecker:
    """Substitution: replace a variable in the predecessor with a value, a purely
    syntactic operation."""
    id = "substitute"

    def check(self, proposal, context, services):
        content, bad = _one_conclusion(proposal)
        if bad is not None:
            return bad
        pred = _premise(proposal)
        if pred is None:
            return Rejected(Reason.FRAGMENT, "missing predecessor")
        d = proposal.evidence.payload
        substituted = T.subst(pred, {d.var: d.value})
        if equal(content, substituted) or equal(content, normal_form(substituted)):
            return _ok(proposal, context)
        return Rejected(Reason.FRAGMENT, "content does not match the substitution result")


class SplitChecker:
    """Conditional branch split: content is equivalent to
    predecessor and (not) condition."""
    id = "branch.split"

    def check(self, proposal, context, services):
        content, bad = _one_conclusion(proposal)
        if bad is not None:
            return bad
        pred = _premise(proposal)
        if pred is None:
            return Rejected(Reason.FRAGMENT, "missing predecessor")
        d = proposal.evidence.payload
        cond = d.condition
        branch = T.not_(cond) if d.negate else cond
        expected = T.mk(S("And"), (pred, branch))
        if content is expected:
            return _ok(proposal, context)
        v = context.decide(T.mk(S("Eq"), (content, expected)))
        if v.is_yes():
            return _ok(proposal, context)
        if v.is_no():
            return Rejected(Reason.FRAGMENT, "content is not the conjunction of the predecessor and the branch condition")
        return UnknownResult(v.reason, "branch equivalence undecided")


def _is_tautology(t) -> bool:
    """Syntactic tautology: a disjunction containing a complementary pair
    (`c` and `not c`), or the constant true.

    The test lives on the verification side and does not rely on
    construction-time collapse, keeping verification independent of
    construction. Only the law of excluded middle is recognized; any other
    coverage needs a real proof.
    """
    if isinstance(t, T.BVal):
        return t.val
    if not (isinstance(t, T.Expr) and t.head.name == "Or"):
        return False
    disjuncts = {a._h for a in t.args}
    return any(isinstance(a, T.Expr) and a.head.name == "Not"
               and a.args[0]._h in disjuncts for a in t.args)


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

    def check(self, proposal, context, services):
        content, bad = _one_conclusion(proposal)
        if bad is not None:
            return bad
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

    def check(self, proposal, context, services):
        content, bad = _one_conclusion(proposal)
        if bad is not None:
            return bad
        d = proposal.evidence.payload
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
        return Accepted(direct_requirements=tuple(dom_condition(content)) + promoted,
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

    def check(self, proposal, context, services):
        content, bad = _one_conclusion(proposal)
        if bad is not None:
            return bad
        d = proposal.evidence.payload
        rel = d.constraint.relation
        inst = T.subst(rel, dict(d.valuation))
        if content is not inst:
            return Rejected(Reason.FRAGMENT, "content is not this constraint's instance under that valuation")
        v = context.decide(inst)
        if v.is_yes():
            return _ok(proposal, context)
        if v.is_no():
            return Rejected(Reason.FRAGMENT, "the constraint does not hold under this valuation")
        return UnknownResult(v.reason, "constraint instance vanishing undecided")


CHECKERS = (ClaimChecker, BothSidesChecker, NormalizeChecker,
            RuleInstanceChecker, SubstChecker, SplitChecker,
            BranchCoverageChecker, BranchMergeChecker,
            ConstraintSatisfiedChecker)


def register(builder) -> None:
    """Register this module's checkers with the assembly builder. Called from
    `base.install` during bootstrap; import never mutates global state."""
    for cls in CHECKERS:
        builder.register_checker(cls.id, cls())
