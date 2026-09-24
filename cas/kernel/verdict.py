"""Three-valued decision results with explicit refutation evidence.

``Yes`` and ``Unknown`` are truth-state values. ``No`` is different: every
refutation names the exact proposition being refuted, the channel that produced
it, and the terms or child refutations that witness the result. There is
deliberately no global ``NO`` singleton.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum, StrEnum

from cas.syntax.term import Term


class Reason(Enum):
    """Why a decision remains undecided."""

    FRAGMENT = "fragment"
    GUARDED = "guarded"
    UNDECIDABLE = "undecidable"
    BUDGET = "budget"


class RefutationChannel(StrEnum):
    """Mathematical channel that established a negative answer."""

    EXACT_COMPARISON = "exact-comparison"
    NORMAL_FORM = "normal-form"
    ASSUMPTION_FACT = "assumption-fact"
    ORDER = "order"
    DERIVATION = "derivation"
    DOMAIN = "domain"
    BRANCH = "branch"
    RULE = "rule"
    LOGICAL = "logical"
    COMPOSITION = "composition"


@dataclass(frozen=True, slots=True)
class Refutation:
    """Structured evidence attached to every :class:`No`.

    ``proposition`` is always the exact proposition being refuted. A
    proposition alone is not evidence: either at least one inspected term is in
    ``witnesses`` or at least one child refutation is retained in ``causes``.
    Logical composition uses ``causes`` so that the outer proposition never
    hides the evidence produced by its children.
    """

    channel: RefutationChannel
    proposition: Term
    witnesses: tuple[Term, ...]
    causes: tuple[Refutation, ...]
    detail: str

    def __post_init__(self) -> None:
        if not isinstance(self.proposition, Term):
            raise ValueError("a refutation requires an exact proposition")
        if not self.witnesses and not self.causes:
            raise ValueError("a refutation requires witnesses or child causes")
        if not self.detail:
            raise ValueError("a refutation requires a non-empty explanation")


class Verdict:
    """Closed three-valued decision hierarchy."""

    __slots__ = ()

    def is_yes(self) -> bool:
        return self is YES

    def is_no(self) -> bool:
        return isinstance(self, No)

    def is_unknown(self) -> bool:
        return isinstance(self, Unknown)


class Yes(Verdict):
    """A successful decision."""

    __slots__ = ()

    def __repr__(self) -> str:
        return "YES"


@dataclass(frozen=True, slots=True)
class No(Verdict):
    """A refutation carrying the evidence that justifies it."""

    evidence: Refutation

    def __repr__(self) -> str:
        return f"NO[{self.evidence.channel.value}]"


@dataclass(frozen=True, slots=True)
class Unknown(Verdict):
    """A decision that cannot currently be established."""

    reason: Reason

    def __repr__(self) -> str:
        return f"UNKNOWN[{self.reason.value}]"


YES = Yes()
_UNKNOWN_CACHE: dict[Reason, Unknown] = {}


def unknown(reason: Reason = Reason.FRAGMENT) -> Unknown:
    """Return the interned unknown value for ``reason``."""

    cached = _UNKNOWN_CACHE.get(reason)
    if cached is None:
        cached = Unknown(reason)
        _UNKNOWN_CACHE[reason] = cached
    return cached


def refute(
    channel: RefutationChannel,
    proposition: Term,
    *witnesses: Term,
    detail: str,
    causes: tuple[Refutation, ...] = (),
) -> No:
    """Construct a validated negative verdict."""

    return No(Refutation(channel, proposition, tuple(witnesses), causes, detail))


def _first_unknown(*verdicts: Verdict) -> Unknown:
    for verdict in verdicts:
        if isinstance(verdict, Unknown):
            return verdict
    return unknown()


def _compose_refutation(
    channel: RefutationChannel,
    proposition: Term,
    causes: tuple[Refutation, ...],
    detail: str,
) -> No:
    """Wrap child evidence while retaining the complete outer proposition."""

    return No(Refutation(channel, proposition, (), causes, detail))


def _direct_causes(child: No, proposition: Term) -> tuple[Refutation, ...]:
    """Avoid hiding direct disjuncts behind an intermediate composition."""

    evidence = child.evidence
    if (
        evidence.channel is RefutationChannel.COMPOSITION
        and evidence.proposition is proposition
        and evidence.causes
    ):
        return evidence.causes
    return (evidence,)


def contextualize(
    verdict: Verdict,
    proposition: Term,
    detail: str = "the verdict was propagated to an outer proposition",
) -> Verdict:
    """Attach an outer proposition to a single child without losing its cause."""

    if isinstance(verdict, No):
        return _compose_refutation(
            RefutationChannel.LOGICAL,
            proposition,
            (verdict.evidence,),
            detail,
        )
    return verdict


def and3(left: Verdict, right: Verdict, proposition: Term) -> Verdict:
    """Three-valued conjunction with an exact outer proposition.

    A refuted conjunct makes the conjunction refuted. The returned refutation
    names ``proposition`` and retains the child evidence, including when the
    first child is already ``No``.
    """

    children = tuple(child for child in (left, right) if isinstance(child, No))
    if children:
        return _compose_refutation(
            RefutationChannel.LOGICAL,
            proposition,
            tuple(child.evidence for child in children),
            "a conjunct was refuted",
        )
    if left is YES and right is YES:
        return YES
    return _first_unknown(left, right)


def or3(left: Verdict, right: Verdict, proposition: Term) -> Verdict:
    """Three-valued disjunction with an exact outer proposition."""

    if left is YES or right is YES:
        return YES
    if isinstance(left, No) and isinstance(right, No):
        return _compose_refutation(
            RefutationChannel.COMPOSITION,
            proposition,
            _direct_causes(left, proposition) + _direct_causes(right, proposition),
            "both disjuncts were refuted",
        )
    return _first_unknown(left, right)


def not3(verdict: Verdict, proposition: Term) -> Verdict:
    """Three-valued negation with an explicit proposition for positive evidence."""

    if verdict is YES:
        return refute(
            RefutationChannel.LOGICAL,
            proposition,
            proposition,
            detail="the proposition being negated was proved",
        )
    if isinstance(verdict, No):
        return YES
    return verdict
