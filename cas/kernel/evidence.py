"""Checker protocol and the closed set of check outcomes.

A checker receives exactly what the kernel resolved — the submission frame, the
requested conclusions, the premise propositions — plus the certificate. It must
return the specifications it actually verified. The kernel compares them with
the request; a checker may not verify one thing while the caller claims another.

`InvalidEvidence` marks a malformed certificate, which is not a refutation.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass
from types import MappingProxyType
from typing import Mapping, Protocol, TypeAlias

from cas.foundation.ids import (
    FrameId,
    JudgmentId,
    ObligationId,
    SymbolId,
    WorldId,
)
from cas.kernel.model import Judgment, ObligationReason
from cas.kernel.trust import AxiomRef, BasisRef, CertificateSchema
from cas.language.decisions import Reason
from cas.language.execution import BudgetTicket, ExecutionBudget
from cas.language.problems import (
    Exactness,
    InterpretationRequirement,
    ProblemSpec,
    ValueDomain,
    VariableRoles,
)
from cas.language.propositions import Proposition
from cas.language.roles import CandidateRole
from cas.language.signatures import LanguageSignature
from cas.language.typing import SortEnvironment, TypedExpr
from cas.semantics import conditions
from cas.semantics.frames import FrameSorts, FrameStore
from cas.semantics.request import AlgebraRequest
from cas.syntax import term as T


@dataclass(frozen=True, slots=True)
class DecisionService:
    """The context's decision interface for the current condition fragment.

    Every method delegates exactly to `cas.semantics.conditions` with this
    service's language signature and optional sort environment.  It proves only
    the restricted condition logic (linear intervals plus exact square
    nonnegativity and monotonicity); an undecidable implication stays `None`
    and is never treated as true.  Equality/disequality square facts require
    the environment to prove the base's free symbols ordered.
    """

    signature: LanguageSignature
    environment: SortEnvironment | None = None

    def __post_init__(self) -> None:
        if not isinstance(self.signature, LanguageSignature):
            raise TypeError("a decision service needs a LanguageSignature")

    def implies(self, assumption: T.Term, goal: T.Term) -> bool | None:
        """Whether the assumption entails the goal in the condition fragment."""
        return conditions.implies(
            assumption, goal, self.signature, self.environment
        )

    def equivalent(self, left: T.Term, right: T.Term) -> bool | None:
        """Whether two conditions are equivalent in the condition fragment."""
        return conditions.equivalent(
            left, right, self.signature, self.environment
        )

    def is_subregion(
        self, subregion: T.Term, region: T.Term
    ) -> bool | None:
        """Whether the subregion is provably contained in the region."""
        return conditions.is_subregion(
            subregion, region, self.signature, self.environment
        )

    def is_empty(self, term: T.Term) -> bool:
        """Whether the condition fragment proves the region empty."""
        return conditions.is_empty_condition(
            term, self.signature, self.environment
        )


@dataclass(frozen=True, slots=True)
class SupportsService:
    """Read-only judgment access for one verification context.

    The kernel constructs it from live `KernelStore` queries; it holds the
    callables, never a second ledger.  A checker reads branch judgments and
    discharge state through this service instead of reaching into a store.
    """

    judgment_of: Callable[[JudgmentId], Judgment]
    visible_in: Callable[[FrameId], tuple[Judgment, ...]]
    discharged_in: Callable[[ObligationId, FrameId], bool]

    def __post_init__(self) -> None:
        for label, value in (
            ("judgment lookup", self.judgment_of),
            ("visible-judgment lookup", self.visible_in),
            ("discharge lookup", self.discharged_in),
        ):
            if not callable(value):
                raise TypeError(
                    f"a supports service needs a callable {label}"
                )

    def judgment(self, judgment_id: JudgmentId) -> Judgment:
        """The issued judgment, or `KeyError` when it does not exist."""
        return self.judgment_of(judgment_id)

    def visible(self, frame: FrameId) -> tuple[Judgment, ...]:
        """Every issued judgment visible from `frame`."""
        return self.visible_in(frame)

    def is_discharged(
        self, obligation_id: ObligationId, frame: FrameId
    ) -> bool:
        """Whether the obligation is discharged visibly from `frame`."""
        return self.discharged_in(obligation_id, frame)


@dataclass(frozen=True, slots=True)
class BudgetService:
    """The execution budget fixed for one verification request.

    `budget` is the proposal's explicit budget, and `ticket` is the immutable
    snapshot the kernel starts from that budget (including its consumption
    counters).  `None` in either field means no such value was fixed; the
    checker's certificate schema still supplies its own limit.  The service is
    a read-only view; it adds no spending state, so reusing a context cannot
    change the answer.
    """

    budget: ExecutionBudget | None = None
    ticket: BudgetTicket | None = None

    def __post_init__(self) -> None:
        if self.budget is not None and not isinstance(
            self.budget, ExecutionBudget
        ):
            raise TypeError(
                "a budget service needs an ExecutionBudget or None"
            )
        if self.ticket is not None and not isinstance(
            self.ticket, BudgetTicket
        ):
            raise TypeError("a budget service ticket must be a BudgetTicket")


@dataclass(frozen=True, slots=True)
class AlgebraService:
    """The fixed algebra request a mathematical checker may rely on.

    The kernel constructs it from `CommitProposal.algebra`; the service holds
    the operation's already-selected request, not a second role registry.  A
    checker that receives it must verify that the request is the one it was
    built for, so a caller cannot verify a claim under another coefficient
    structure, target or parameter mode.
    """

    request: AlgebraRequest

    def __post_init__(self) -> None:
        if not isinstance(self.request, AlgebraRequest):
            raise TypeError("an algebra service needs an AlgebraRequest")


@dataclass(frozen=True, slots=True)
class DefinednessService:
    """Region containment checks scoped to one verification context.

    The kernel constructs the service from the same `DecisionService` and
    `FrameStore` as the rest of the context.  `frame` is the verification frame
    the kernel fixed; a service built directly by a test may leave it `None`,
    in which case both propositions must share one meaning frame.  A region
    inclusion is only meaningful when both propositions keep their meaning in
    the comparison frame: `covers` returns `False` for a proposition from
    another world, from a frame outside the verification frame's ancestor
    chain, or from a frame the store does not contain.  An inclusion the
    restricted condition fragment cannot decide stays `None`; it is never read
    as true.
    """

    decision: DecisionService
    frames: FrameStore
    frame: FrameId | None = None

    def __post_init__(self) -> None:
        if not isinstance(self.decision, DecisionService):
            raise TypeError(
                "a definedness service needs a DecisionService"
            )
        if not isinstance(self.frames, FrameStore):
            raise TypeError("a definedness service needs a FrameStore")
        if self.frame is not None and (
            isinstance(self.frame, bool) or not isinstance(self.frame, int)
        ):
            raise TypeError(
                "a definedness service frame must be a FrameId or None"
            )

    def _readable(self, proposition: Proposition, frame: FrameId) -> bool:
        """Whether `proposition` keeps its meaning when read in `frame`."""
        if proposition.meaning.world != self.frames.world.id:
            return False
        if not self.frames.is_visible(proposition.meaning.frame, frame):
            return False
        return self.frames.readable(proposition, frame)

    def covers(
        self, region: Proposition, domain: Proposition
    ) -> bool | None:
        """Whether `region` is provably contained in `domain`.

        Both propositions must be readable in the service's verification frame
        (or, without one, in their common meaning frame).  An unreadable
        proposition is not contained: the conservative result is `False`, never
        a vacuous `True` and never an undecided `None`.

        Definedness premises are part of each proposition's meaning.  The
        region's own premises must follow from the region condition, and the
        domain's premises must follow from the region condition; an open
        premise is not read as true.
        """
        if not isinstance(region, Proposition) or not isinstance(
            domain, Proposition
        ):
            raise TypeError(
                "a definedness service compares propositions"
            )
        frame = self.frame
        if frame is None:
            if region.meaning.frame != domain.meaning.frame:
                return False
            frame = region.meaning.frame
        if not self._readable(region, frame) or not self._readable(
            domain, frame
        ):
            return False
        environment = FrameSorts(self.frames, frame)
        own = conditions.premises_proved(
            region.term,
            tuple(premise.term for premise in region.definedness),
            self.decision.signature,
            environment,
        )
        if own is not True:
            return own
        goal = conditions.premises_proved(
            region.term,
            tuple(premise.term for premise in domain.definedness),
            self.decision.signature,
            environment,
        )
        if goal is not True:
            return goal
        return self.decision.is_subregion(region.term, domain.term)


@dataclass(frozen=True, slots=True)
class VerificationContext:
    """The trusted scope in which a mathematical checker reads a problem.

    The kernel constructs the context from the submission frame; a checker may
    not substitute another world or frame.  It fixes the meaning world, the
    verification frame, the frame store, the condition decision service, the
    definedness service, the read-only support queries, the execution budget
    ticket, the admitted trusted dependencies and the fixed algebra request.
    The algebra service is present only when the proposal carried an algebra
    request; direct checker tests and manual rechecks may leave it absent.
    """

    world: WorldId
    frame: FrameId
    frames: FrameStore
    decision: DecisionService | None = None
    supports: SupportsService | None = None
    budget: BudgetService | None = None
    axioms: tuple[AxiomRef, ...] = ()
    algebra: AlgebraService | None = None
    definedness: DefinednessService | None = None

    def __post_init__(self) -> None:
        if isinstance(self.world, bool) or not isinstance(self.world, int):
            raise TypeError("a verification context needs a WorldId")
        if isinstance(self.frame, bool) or not isinstance(self.frame, int):
            raise TypeError("a verification context needs a FrameId")
        if not isinstance(self.frames, FrameStore):
            raise TypeError("a verification context needs a FrameStore")
        if self.decision is not None and not isinstance(
            self.decision, DecisionService
        ):
            raise TypeError(
                "a verification context decision must be a DecisionService "
                "or None"
            )
        if self.supports is not None and not isinstance(
            self.supports, SupportsService
        ):
            raise TypeError(
                "a verification context supports must be a SupportsService "
                "or None"
            )
        if self.budget is not None and not isinstance(
            self.budget, BudgetService
        ):
            raise TypeError(
                "a verification context budget must be a BudgetService or "
                "None"
            )
        axioms = tuple(self.axioms)
        if any(not isinstance(axiom, AxiomRef) for axiom in axioms):
            raise TypeError(
                "a verification context axioms must be AxiomRef values"
            )
        if any(axiom.world != self.world for axiom in axioms):
            raise ValueError(
                "a verification context axiom belongs to another world"
            )
        if self.algebra is not None and not isinstance(
            self.algebra, AlgebraService
        ):
            raise TypeError(
                "a verification context algebra must be an AlgebraService "
                "or None"
            )
        if self.definedness is not None and not isinstance(
            self.definedness, DefinednessService
        ):
            raise TypeError(
                "a verification context definedness must be a "
                "DefinednessService or None"
            )
        object.__setattr__(self, "axioms", axioms)

    def readable(self, proposition: Proposition | TypedExpr) -> bool:
        """Whether a proposition or typed input may be read in this context.

        Both carry a `MeaningKey`; the context requires the same meaning world
        and a frame on the verification frame's ancestor chain.  A proposition
        from a colliding frame id in another runtime's world is never readable.
        """
        return (
            proposition.meaning.world == self.world
            and self.frames.is_visible(
                proposition.meaning.frame, self.frame
            )
        )


@dataclass(frozen=True, slots=True)
class CheckRequest:
    """What a checker is asked to verify.

    `problem` is the fixed original problem.  The kernel requires it for every
    mathematical checker; core logic rules have no `ProblemSpec` and leave it
    `None`.  A checker that receives a problem must verify that its certificate
    still names the same inputs and target, and that every problem input is
    readable in `context`.

    `candidate` is the actual mathematical value the workflow will publish.  It
    is not a certificate field and not a trusted proposition: a mathematical
    checker compares it with the term its certificate or specification names,
    so the workflow cannot record a different result than the one that was
    verified.  `candidate_role` declares which part of the claim that value is;
    a mathematical checker selects the expected term from it and never from the
    operation name.  Core logic rules leave both fields `None`.

    `context` is the kernel-built verification scope.  A mathematical checker
    must receive it; a core logic rule leaves it `None`.
    """

    frame: FrameId
    conclusions: tuple[Proposition, ...]
    premises: tuple[Proposition, ...]
    certificate: object
    problem: ProblemSpec | None = None
    candidate: T.Term | None = None
    candidate_role: CandidateRole | None = None
    context: VerificationContext | None = None
    structured: tuple[tuple[str, T.Term], ...] | None = None

    def __post_init__(self) -> None:
        for proposition in self.premises + self.conclusions:
            if not isinstance(proposition, Proposition):
                raise TypeError("a check request carries propositions")
        if self.structured is not None:
            names = [name for name, _ in self.structured]
            if any(not name for name in names):
                raise ValueError(
                    "a structured check payload needs a component name"
                )
            if len(set(names)) != len(names):
                raise ValueError(
                    "a structured check payload repeats a component name"
                )
            if any(
                not isinstance(term, T.Term) for _, term in self.structured
            ):
                raise TypeError(
                    "a structured check payload holds terms"
                )
        if self.problem is not None and not isinstance(
            self.problem, ProblemSpec
        ):
            raise TypeError("a check request problem must be a ProblemSpec")
        if self.candidate is not None and not isinstance(
            self.candidate, T.Term
        ):
            raise TypeError("a check request candidate must be a term")
        if self.candidate_role is not None and not isinstance(
            self.candidate_role, CandidateRole
        ):
            raise TypeError(
                "a check request candidate role must be a CandidateRole "
                "or None"
            )
        if self.context is not None and not isinstance(
            self.context, VerificationContext
        ):
            raise TypeError(
                "a check request context must be a VerificationContext "
                "or None"
            )


def context_algebra_mismatch(
    context: VerificationContext | None,
    request: AlgebraRequest,
) -> str | None:
    """Why a fixed-request checker may not use the context's algebra view.

    Every mathematical checker that was built for one pre-assembled
    `AlgebraRequest` must consume exactly that request through the kernel-built
    `VerificationContext`.  A bare context (a direct test or a manual caller) has
    no algebra view, and a function problem must never pretend to have one.

    The comparison is by object identity, not structural equality.  The request
    is a frozen object assembled once by the operation's problem builder and
    handed to both the checker and the proposal; a structurally equal copy would
    still carry different parent/parameter/differential objects.  Identity keeps
    the request that selected the bridge and the request the checker verifies
    against one authority instead of accepting a second reconstructed value.
    """
    if context is None:
        return "the check request has no trusted verification context"
    if context.algebra is None:
        return "the check request has no fixed algebra request"
    if context.algebra.request is not request:
        return "the context algebra request does not match the checker request"
    return None


def problem_mismatch(
    request: CheckRequest,
    *,
    operations: tuple[str, ...] | None = None,
    target: SymbolId | None = None,
    inputs: tuple[T.Term, ...] | None = None,
    input_set: tuple[T.Term, ...] | None = None,
    region: T.Term | None = None,
    roles: VariableRoles | None = None,
    interpretation_requirement: InterpretationRequirement | None = None,
    exactness: Exactness | None = None,
    coefficient_domain: ValueDomain | None = None,
    value_domain: ValueDomain | None = None,
) -> str | None:
    """Why a checker's certificate does not match the original problem.

    `None` means either the request has no problem (a core logic rule) or every
    supplied check passed.  Mathematical checkers are required to receive both
    the problem and the kernel-built verification context; every problem input
    must belong to that context's meaning world and be visible from its frame.

    `inputs` compares the problem's input sequence exactly.  `input_set` is the
    set-reading of the same comparison for a specification whose operands are
    finite sets of terms (for example the generator set of a Groebner claim):
    repeated problem inputs fold, because a set names its members without order
    or multiplicity.  The two modes are mutually exclusive.  This is not a
    second problem comparator; it is one comparison with an ordered reading and
    a set reading.

    When `region` is supplied, the problem's own region must be covered by that
    specification region.  A problem without a region is read as `TRUE`, so it
    is covered only by a specification that is itself valid everywhere.  An
    inclusion the restricted condition logic cannot prove is reported as a
    mismatch rather than assumed.  The helper keeps their local checks uniform.

    When `roles`, `interpretation_requirement`, `exactness`,
    `coefficient_domain` or `value_domain` are supplied, the problem must carry
    exactly that fixed value.  Role equality covers the target, parameters,
    parameter mode, world and the target/parameter binding sorts, so a checker
    cannot accept a problem resolved under another request binding.  A missing
    interpretation or domain requirement on the problem is a mismatch when the
    checker requires one.  The domain fields are checked independently: a
    function checker supplies `coefficient_domain=None` because a function
    problem has no coefficient structure, and supplies the real value domain.
    """
    if inputs is not None and input_set is not None:
        raise ValueError(
            "problem_mismatch takes one input comparison mode, not both"
        )
    problem = request.problem
    if problem is None:
        return None
    context = request.context
    if context is None:
        return "the check request has no trusted verification context"
    for item in problem.inputs:
        if not context.readable(item):
            if item.meaning.world != context.world:
                return "a problem input belongs to another meaning world"
            return (
                "a problem input belongs to a frame outside the "
                "verification context"
            )
    if roles is not None and problem.roles != roles:
        return "the problem roles do not match the specification"
    if (
        interpretation_requirement is not None
        and problem.interpretation_requirement != interpretation_requirement
    ):
        return (
            "the problem interpretation requirement does not match the "
            "specification"
        )
    if exactness is not None and problem.exactness != exactness:
        return "the problem exactness does not match the specification"
    if coefficient_domain is not None or value_domain is not None:
        requirement = problem.domain_requirement
        if requirement is None:
            return "the problem does not fix a domain requirement"
        if (
            coefficient_domain is not None
            and requirement.coefficient != coefficient_domain
        ):
            return (
                "the problem coefficient domain does not match the "
                "specification"
            )
        if value_domain is not None and requirement.values != value_domain:
            return (
                "the problem value domain does not match the specification"
            )
    if operations is not None and problem.operation not in operations:
        return "the problem kind does not match the specification"
    if target is not None and problem.target != target:
        return "the problem target does not match the specification"
    if inputs is not None and tuple(
        item.term for item in problem.inputs
    ) != inputs:
        return "the problem inputs do not match the specification"
    if input_set is not None and frozenset(
        item.term for item in problem.inputs
    ) != frozenset(input_set):
        return (
            "the problem inputs do not match the specification generator set"
        )
    if region is not None:
        if problem.region is not None and not context.readable(
            problem.region
        ):
            if problem.region.meaning.world != context.world:
                return (
                    "the problem region belongs to another meaning world"
                )
            return (
                "the problem region belongs to a frame outside the "
                "verification context"
            )
        problem_region = (
            T.TRUE if problem.region is None else problem.region.term
        )
        if context.decision is not None:
            covered = context.decision.is_subregion(problem_region, region)
        else:
            covered = conditions.is_subregion(
                problem_region,
                region,
                context.frames.world.language,
                FrameSorts(context.frames, context.frame),
            )
        if covered is not True:
            return (
                "the problem region is not covered by the specification "
                "region"
            )
    return None


@dataclass(frozen=True, slots=True)
class ObligationReport:
    """A condition the checker declares; the reason is explanation only."""

    proposition: Proposition
    reason: ObligationReason

    def __post_init__(self) -> None:
        if not isinstance(self.proposition, Proposition):
            raise TypeError("an obligation report carries a proposition")
        if not isinstance(self.reason, ObligationReason):
            raise TypeError("an obligation report needs a reason")


@dataclass(frozen=True, slots=True)
class Verified:
    """The checker verified `checked`, which must equal the request.

    `used_premises` are indices into the request's premises that the checker
    actually used. The kernel records only those; a premise the caller supplied
    but the checker ignored does not become claimed support.
    """

    checked: tuple[Proposition, ...]
    obligations: tuple[ObligationReport, ...] = ()
    reads: tuple[tuple[str, str], ...] = ()
    used_premises: tuple[int, ...] = ()

    def __post_init__(self) -> None:
        if any(not isinstance(item, Proposition) for item in self.checked):
            raise TypeError("a verified outcome carries propositions")
        if any(
            not isinstance(item, ObligationReport)
            for item in self.obligations
        ):
            raise TypeError("a verified outcome carries obligation reports")
        if any(
            not isinstance(index, int) or isinstance(index, bool)
            for index in self.used_premises
        ):
            raise TypeError("used premise indices must be integers")


@dataclass(frozen=True, slots=True)
class Refuted:
    """The requested specification is false, with witnesses."""

    proposition: Proposition
    witnesses: tuple[T.Term, ...]
    detail: str

    def __post_init__(self) -> None:
        if not isinstance(self.proposition, Proposition):
            raise TypeError("a refutation carries a proposition")
        if not self.witnesses:
            raise ValueError("a refutation needs at least one witness")
        if any(not isinstance(item, T.Term) for item in self.witnesses):
            raise TypeError("refutation witnesses must be terms")
        if not self.detail:
            raise ValueError("a refutation needs an explanation")


@dataclass(frozen=True, slots=True)
class Unverified:
    """The checker could not decide; this is not a refutation.

    `missing` names the capabilities the checker lacked and `conditions` are
    the obligations it could not discharge.  Both are carried to the commit
    boundary instead of being flattened into `detail`.
    """

    reason: Reason
    detail: str
    missing: frozenset[str] = frozenset()
    conditions: tuple[Proposition, ...] = ()

    def __post_init__(self) -> None:
        if not isinstance(self.reason, Reason):
            raise TypeError("an unverified outcome needs a Reason")
        if not isinstance(self.detail, str):
            raise TypeError("an unverified outcome detail must be a string")
        if not self.detail:
            raise ValueError("an unverified outcome needs a detail")
        missing = frozenset(self.missing)
        if any(not isinstance(item, str) or not item for item in missing):
            raise TypeError(
                "unverified-outcome capabilities must be non-empty strings"
            )
        conditions = tuple(self.conditions)
        if any(not isinstance(item, Proposition) for item in conditions):
            raise TypeError(
                "unverified-outcome conditions must be propositions"
            )
        object.__setattr__(self, "missing", missing)
        object.__setattr__(self, "conditions", conditions)


@dataclass(frozen=True, slots=True)
class InvalidEvidence:
    """The certificate is malformed or belongs to another request."""

    detail: str


CheckOutcome: TypeAlias = Verified | Refuted | Unverified | InvalidEvidence


class Checker(Protocol):
    """A registered verification procedure."""

    @property
    def id(self) -> str: ...

    @property
    def version(self) -> str: ...

    def check(self, request: CheckRequest) -> CheckOutcome:
        """Re-verify the request and report exactly what was verified."""


@dataclass(frozen=True, slots=True)
class CheckerSpec:
    """Everything the kernel admits about one checker.

    The certificate schema, accepted kinds and trusted dependencies belong to
    the registration, not to a proposal. A proposal names a checker and a kind;
    it cannot supply its own trust metadata.
    """

    checker: Checker
    certificate_schema: CertificateSchema
    accepted_problem_kinds: frozenset[str]
    accepted_specification_kinds: frozenset[str]
    world: WorldId
    trusted_dependencies: tuple[BasisRef, ...] = ()
    requires_problem: bool = False

    @property
    def accepts_cross_frame_premises(self) -> bool:
        """Whether this checker may receive premises from non-visible frames.

        Only a case-analysis rule needs this: its branch judgments live in
        child frames.  The checker must then validate each premise's branch
        relation and prove that its obligations are closed in the frame where
        the premise was issued.  The capability is declared by the checker and
        exposed through the admitted registration, never inferred from an
        operation or checker name.
        """
        return bool(
            getattr(self.checker, "accepts_cross_frame_premises", False)
        )

    def __post_init__(self) -> None:
        if not self.checker.id:
            raise ValueError("a checker specification needs a checker id")
        if not self.checker.version:
            raise ValueError(
                f"checker {self.checker.id!r} has no version"
            )
        if not isinstance(self.requires_problem, bool):
            raise TypeError(
                f"checker {self.checker.id!r} requires_problem must be bool"
            )
        for label, kinds in (
            ("problem", self.accepted_problem_kinds),
            ("specification", self.accepted_specification_kinds),
        ):
            if not isinstance(kinds, frozenset) or any(
                not isinstance(kind, str) or not kind for kind in kinds
            ):
                raise TypeError(
                    f"checker {self.checker.id!r} needs string {label} kinds"
                )
            if not kinds:
                raise ValueError(
                    f"checker {self.checker.id!r} accepts no {label} kind"
                )
        if not isinstance(self.trusted_dependencies, tuple):
            raise TypeError(
                f"checker {self.checker.id!r} trusted dependencies "
                "must be a tuple"
            )
        if any(
            not isinstance(basis, BasisRef)
            for basis in self.trusted_dependencies
        ):
            raise TypeError(
                f"checker {self.checker.id!r} has a non-basis dependency"
            )
        keys = [
            (basis.name, basis.kind, basis.version, basis.digest, basis.world)
            for basis in self.trusted_dependencies
        ]
        if len(set(keys)) != len(keys):
            raise ValueError(
                f"checker {self.checker.id!r} repeats a trusted dependency"
            )
        for basis in self.trusted_dependencies:
            if basis.world != self.world:
                raise ValueError(
                    f"checker {self.checker.id!r} trusts a basis from "
                    "another world"
                )


class CheckerRegistry:
    """A frozen checker table built during assembly."""

    __slots__ = ("_specs",)

    def __init__(self, specs: Mapping[str, CheckerSpec]) -> None:
        table = dict(specs)
        for key, spec in table.items():
            if not isinstance(spec, CheckerSpec):
                raise TypeError(
                    "a checker registry holds CheckerSpec values, "
                    f"got {type(spec).__name__}"
                )
            if spec.checker.id != key:
                raise ValueError(
                    f"checker registered as {key!r} reports id "
                    f"{spec.checker.id!r}"
                )
        self._specs = MappingProxyType(table)

    def get(self, checker_id: str) -> Checker | None:
        spec = self._specs.get(checker_id)
        return None if spec is None else spec.checker

    def spec(self, checker_id: str) -> CheckerSpec | None:
        return self._specs.get(checker_id)

    def __len__(self) -> int:
        return len(self._specs)


__all__ = [
    "AlgebraService",
    "BudgetService",
    "CheckOutcome",
    "CheckRequest",
    "Checker",
    "CheckerRegistry",
    "CheckerSpec",
    "DecisionService",
    "DefinednessService",
    "InvalidEvidence",
    "ObligationReport",
    "Refuted",
    "SupportsService",
    "Unverified",
    "VerificationContext",
    "Verified",
    "context_algebra_mismatch",
    "problem_mismatch",
]
