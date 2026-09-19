"""Kernel ledger: writes of committed facts, discharge, and layered history.

Append-only, never physically deleting: the Judgment store only grows, and an
original conclusion never disappears because a condition was refuted. A
conclusion whose guard is refuted becomes `Inapplicable`; it is not destroyed
and nothing cascades along dependency edges.

The store holds **committed** facts only. Intermediate computation products are
Artifacts and never enter here, so the ledger size depends on the number of
commits, not on the number of rewrites.
"""
from cas.syntax import term as T

from cas.kernel.evidence import CheckerRegistry
from cas.kernel.ids import JudgmentId, RequirementId, StepId
from cas.kernel.model import (
    Applicable, Conditional, Discharge, Inapplicable, Judgment, Requirement, Step,
)
from cas.kernel.scope import ScopeStore


def negation_arg(p):
    """The operand of a syntactic negation `Not(p)`, or None when `p` is not a
    negation call. Syntactic only: no semantic guessing about other shapes."""
    if isinstance(p, T.Expr) and p.head.name == "Not":
        return p.args[0]
    return None


class KernelStore:
    """Append-only ledger: scopes, requirements, judgments, steps, discharges."""

    def __init__(self, scopes=None, checkers=None):
        self.scopes = scopes if scopes is not None else ScopeStore()
        self.checkers = checkers if checkers is not None else CheckerRegistry()
        self._requirements: dict[RequirementId, Requirement] = {}
        self._judgments: dict[JudgmentId, Judgment] = {}
        self._steps: dict[StepId, Step] = {}
        self._discharges: dict[RequirementId, list] = {}
        self._refutations: dict[RequirementId, list] = {}
        # Reverse index over requirement propositions, maintained at the single
        # requirement write site: proposition -> ids, and the operand of a
        # syntactic negation -> ids. Each bucket is in insertion order, so a
        # refutation query sees the candidates in the order a full scan did.
        self._req_by_prop: dict = {}
        self._req_by_negation: dict = {}
        self._next_req = 0
        self._next_jud = 0
        self._next_step = 0

    # --- id issuing ---

    def new_requirement_id(self) -> RequirementId:
        rid = RequirementId(self._next_req)
        self._next_req += 1
        return rid

    def new_judgment_id(self) -> JudgmentId:
        jid = JudgmentId(self._next_jud)
        self._next_jud += 1
        return jid

    def new_step_id(self) -> StepId:
        sid = StepId(self._next_step)
        self._next_step += 1
        return sid

    # --- writes (only commit calls these) ---

    def put_requirement(self, req: Requirement) -> Requirement:
        """The single requirement write site; it also maintains the reverse
        index over propositions."""
        self._requirements[req.id] = req
        self._req_by_prop.setdefault(req.proposition, []).append(req.id)
        neg = negation_arg(req.proposition)
        if neg is not None:
            self._req_by_negation.setdefault(neg, []).append(req.id)
        return req

    def put_judgment(self, j: Judgment) -> Judgment:
        self._judgments[j.id] = j
        return j

    def put_step(self, s: Step) -> Step:
        self._steps[s.id] = s
        return s

    def add_discharge(self, d: Discharge) -> None:
        self._discharges.setdefault(d.requirement, []).append(d)

    def add_refutation(self, requirement: RequirementId, by: JudgmentId) -> None:
        """Record that a condition was refuted: the original conclusion is kept
        and its applicability becomes Inapplicable."""
        self._refutations.setdefault(requirement, []).append(by)

    # --- queries ---

    def get_requirement(self, rid: RequirementId) -> Requirement:
        return self._requirements[rid]

    def get_judgment(self, jid: JudgmentId) -> Judgment:
        return self._judgments[jid]

    def get_step(self, sid: StepId) -> Step:
        return self._steps[sid]

    def all_steps(self) -> tuple:
        return tuple(self._steps[i] for i in range(self._next_step))

    def all_judgments(self) -> tuple:
        return tuple(self._judgments[i] for i in range(self._next_jud))

    def requirements_of(self, jid: JudgmentId) -> tuple:
        return self._judgments[jid].requirements

    def all_requirements(self) -> tuple:
        return tuple(self._requirements.values())

    def requirements_refuted_by(self, proposition) -> tuple:
        """Requirement ids that `proposition` syntactically refutes, in
        insertion order.

        A requirement is refuted when its proposition is the operand of the
        conclusion's syntactic negation, or when the requirement's own
        syntactic negation is the conclusion; both sides compare by term
        identity, exactly as the full scan did. The two buckets are disjoint
        (a requirement whose proposition were both the operand and the
        negation itself would have to contain itself as a strict subterm), so
        no deduplication is needed.
        """
        out = []
        neg = negation_arg(proposition)
        if neg is not None:
            out.extend(self._req_by_prop.get(neg, ()))
        out.extend(self._req_by_negation.get(proposition, ()))
        return tuple(out)

    def discharges_of(self, rid: RequirementId) -> tuple:
        return tuple(self._discharges.get(rid, ()))

    def refutations_of(self, rid: RequirementId) -> tuple:
        return tuple(self._refutations.get(rid, ()))

    def is_discharged(self, rid: RequirementId, scope) -> bool:
        """Whether the requirement is discharged in `scope`: a discharge
        performed in the scope or any ancestor is visible."""
        for d in self._discharges.get(rid, ()):
            if self.scopes.is_visible(d.scope, scope):
                return True
        return False

    def is_refuted(self, rid: RequirementId, scope) -> bool:
        for r in self._refutations.get(rid, ()):
            j = self._judgments[r]
            if self.scopes.is_visible(j.scope, scope):
                return True
        return False

    # --- applicability ---

    def applicability(self, jid: JudgmentId, scope):
        """Applicability of a conclusion in `scope`.

        Refutation takes precedence over discharge: if any condition is refuted
        within the visible range of `scope`, the result is Inapplicable even if
        another condition was discharged. The original conclusion is neither
        deleted nor cascaded.
        """
        reqs = self.requirements_of(jid)
        refuted = tuple(r for r in reqs if self.is_refuted(r, scope))
        if refuted:
            return Inapplicable(refutations=tuple(refuted))
        pending = tuple(r for r in reqs if not self.is_discharged(r, scope))
        if pending:
            return Conditional(requirements=pending)
        return Applicable()

    # --- size (ledger size tracks commits, not rewrites) ---

    def stats(self):
        return {
            "requirements": len(self._requirements),
            "judgments": len(self._judgments),
            "steps": len(self._steps),
            "scopes": self._next_scope_count(),
        }

    def _next_scope_count(self):
        return getattr(self.scopes, "_next", 0)
