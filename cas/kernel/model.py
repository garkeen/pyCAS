"""Kernel data model.

The kernel's basic object is not a transformed expression but a conditional,
scope-qualified proposition:

    Gamma |- P [Delta]

· Gamma = Scope (declarations / definitions / assumptions)
· P     = Judgment.proposition
· Delta = Judgment.requirements (open conditions)

Conclusions and decision results are expressed as a closed variant hierarchy
(`Applicability`) so illegal states cannot be represented; value objects are
frozen with slots. `Step` has no subclasses: what a step did is described by
its conclusion propositions and its evidence.

The kernel knows no mathematical head: this module depends on syntax only and
imports no concrete mathematical module.
"""

from dataclasses import dataclass, field
from enum import Enum

from cas.syntax import term as T
from cas.kernel.ids import JudgmentId, RequirementId, ScopeId, StepId


# ---------------------------------------------------------------------------
# Scope entries
# ---------------------------------------------------------------------------

@dataclass(frozen=True, slots=True)
class Declaration:
    """A declaration: `x : Real`, `n : Integer`, `c : Parameter independent of
    x`, `y : Function(Real, Real)`."""
    symbol: T.Term
    sort: T.Term


@dataclass(frozen=True, slots=True)
class Definition:
    """A definition: `u := x^2`. A local alias, not an equation the user must
    prove."""
    symbol: T.Term
    body: T.Term


@dataclass(frozen=True, slots=True)
class Assumption:
    """An assumption: `x > 0`, `a != 0`, `continuous(f, I)`. A condition the
    user or a branch explicitly accepts.

    An open guard must never be written into assumptions automatically; that is
    what Requirement is for.
    """
    proposition: T.Term


# ---------------------------------------------------------------------------
# Requirement: an open condition
# ---------------------------------------------------------------------------

class RequirementReason(Enum):
    """Why the condition was introduced. Distinct from verdict.Reason, which
    says why a decision failed."""
    DEFINEDNESS = "definedness"
    RULE_GUARD = "rule_guard"
    ALGORITHM_PRECONDITION = "algorithm_precondition"
    BRANCH_COVERAGE = "branch_coverage"
    DOMAIN_MEMBERSHIP = "domain_membership"


@dataclass(frozen=True, slots=True)
class Requirement:
    id: RequirementId
    scope: ScopeId
    proposition: T.Term
    introduced_by: StepId
    reason: RequirementReason


# ---------------------------------------------------------------------------
# Judgment / Step
# ---------------------------------------------------------------------------

@dataclass(frozen=True, slots=True)
class Judgment:
    """A dependable mathematical conclusion: Gamma |- proposition
    [requirements].

    `producer` is the Step that produced it. A Judgment can only be created by
    `kernel.commit`.
    """
    id: JudgmentId
    scope: ScopeId
    proposition: T.Term
    requirements: tuple[RequirementId, ...]
    producer: StepId


@dataclass(frozen=True, slots=True)
class ContextReadSet:
    """Context facts read by a step.

    Every implicit use must leave a read dependency, otherwise "this step
    depends on an assumption not recorded in the step" happens silently.
    """
    entries: tuple[tuple[str, str], ...] = ()

    def merge(self, other):
        """Union with per-item deduplication: a read dependency is a set, so
        reading the same item twice counts once.

        The key is the whole `(kind, key)` pair; merging on kind alone would
        collapse multiple reads of the same kind into one.
        """
        return ContextReadSet(tuple(sorted(set(self.entries)
                                              | set(other.entries))))

    def __bool__(self):
        return bool(self.entries)


@dataclass(frozen=True, slots=True)
class Step:
    """A mathematical dependency edge. No subclasses; dispatch goes through the
    checker registry.

    `premises` / `conclusions` are Judgment ids. An Artifact can never be a
    premise.
    """
    id: StepId
    scope: ScopeId
    premises: tuple[JudgmentId, ...]
    conclusions: tuple[JudgmentId, ...]
    evidence: object                    # kernel.evidence.Evidence
    reads: ContextReadSet = field(default_factory=ContextReadSet)


# ---------------------------------------------------------------------------
# Discharge and applicability
# ---------------------------------------------------------------------------

@dataclass(frozen=True, slots=True)
class Discharge:
    """A discharge: `requirement` is proved by `by_judgment` in `scope`.

    Discharge never modifies the original Judgment. The conditional conclusion
    still holds; a query in this scope simply reports it as directly
    applicable.
    """
    requirement: RequirementId
    by_judgment: JudgmentId
    scope: ScopeId


class Applicability:
    """Closed hierarchy of applicability.

    When a condition is refuted the original conclusion is not destroyed, it is
    marked Inapplicable: as a conditional proposition it remains correct, and
    it is not cascade-deleted along dependency edges.
    """
    __slots__ = ()

    def is_applicable(self):
        return self.__class__ is Applicable

    def is_conditional(self):
        return self.__class__ is Conditional

    def is_inapplicable(self):
        return self.__class__ is Inapplicable


@dataclass(frozen=True, slots=True)
class Applicable(Applicability):
    """Directly applicable: every condition has been discharged."""


@dataclass(frozen=True, slots=True)
class Conditional(Applicability):
    """Conditional: some requirement is still undischarged."""
    requirements: tuple[RequirementId, ...] = ()


@dataclass(frozen=True, slots=True)
class Inapplicable(Applicability):
    """Not applicable in this scope: a condition was refuted. The original
    conclusion is not deleted."""
    refutations: tuple[JudgmentId, ...] = ()
