"""Propositions: a formula that has been typed and tied to a meaning frame.

A `Proposition` is not "any term with a label". It exists only through
`check`, which requires that the term

- is well scoped (no bound index escapes its binder),
- has proposition sort under the language signature,
- carries the identity of the world and frame it was read in.

A proposition also records its structural definedness premises: the conditions
under which its term is defined.  They are not additional assumptions that make
the proposition true.  This slice collects the nonzero-base condition of every
integer power with exponent `<= 0`, recurses through sums, products,
comparisons and the boolean connectives, and deliberately leaves declared
function domains, `Guarded`/`Piecewise` branch-local semantics and binder-aware
premises open.  Declared-predicate laws remain elaboration work; this layer
refuses a formula it cannot type, and never guesses.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import TypeAlias

from cas.language import sorts as S
from cas.language import typing as Ty
from cas.language.meaning import MeaningKey
from cas.language.signatures import LanguageSignature, StructuralHead
from cas.syntax import term as T

_SEAL = object()
_PROPOSITION_FIELDS = frozenset({"term", "meaning", "definedness"})


def _require_proposition_seal(value: object) -> None:
    """Refuse a proposition whose factory did not set the module seal."""
    try:
        seal = object.__getattribute__(value, "_seal")
    except AttributeError:
        seal = None
    if seal is not _SEAL:
        raise ValueError(
            "a proposition is issued only by propositions.check"
        )


@dataclass(frozen=True, slots=True)
class Proposition:
    """A typed formula with an explicit meaning environment.

    `definedness` holds the conditions under which `term` is defined, not
    assumptions that make it true.  Each premise is itself a proposition read
    in the same meaning environment, so its own premises are recorded
    recursively.  Premises are deduplicated by structural equality and may not
    be the proposition itself.

    Construction requires the module seal; use `check`.  `dataclasses.replace`
    cannot reproduce a proposition, because the replacement is built through
    `__init__` without the seal and is refused by `__post_init__`.
    """

    term: T.Term
    meaning: MeaningKey
    definedness: tuple[Proposition, ...] = ()
    _seal: object | None = field(
        init=False, default=None, repr=False, compare=False
    )

    def __post_init__(self) -> None:
        if self._seal is not _SEAL:
            raise ValueError(
                "a proposition is issued only by propositions.check"
            )
        if not isinstance(self.term, T.Term):
            raise TypeError("a proposition needs a term")
        if not isinstance(self.meaning, MeaningKey):
            raise TypeError("a proposition needs a meaning key")
        if not isinstance(self.definedness, tuple):
            raise TypeError(
                "a proposition definedness must be a tuple of propositions"
            )
        if any(
            not isinstance(premise, Proposition)
            for premise in self.definedness
        ):
            raise TypeError(
                "a proposition definedness holds propositions"
            )
        for premise in self.definedness:
            if premise.meaning != self.meaning:
                raise ValueError(
                    "a definedness premise must share the proposition's "
                    "meaning environment"
                )
            if premise.term == self.term and premise.meaning == self.meaning:
                raise ValueError(
                    "a proposition cannot be its own definedness premise"
                )
        if len(set(self.definedness)) != len(self.definedness):
            raise ValueError(
                "a proposition cannot repeat a definedness premise"
            )

    def __getattribute__(self, name: str) -> object:
        if name in _PROPOSITION_FIELDS:
            _require_proposition_seal(self)
        return object.__getattribute__(self, name)


def _issue_proposition(
    term: T.Term,
    meaning: MeaningKey,
    definedness: tuple[Proposition, ...] = (),
) -> Proposition:
    """Construct one proposition after setting the module seal."""
    value = object.__new__(Proposition)
    object.__setattr__(value, "term", term)
    object.__setattr__(value, "meaning", meaning)
    object.__setattr__(value, "definedness", definedness)
    object.__setattr__(value, "_seal", _SEAL)
    value.__post_init__()
    return value


PropositionOutcome: TypeAlias = Proposition | Ty.TypedExprFailure


def _structural_premises(
    term: T.Term,
    signature: LanguageSignature,
) -> tuple[T.Term, ...] | Ty.Unsupported:
    """Collect structural definedness premises from a typed proposition term.

    The walker is deliberately partial.  It records the nonzero-base condition
    of every integer power with exponent `<= 0`: the source expression
    `Power(base, n)` is undefined at a zero base for both `n = 0` and `n < 0`.
    It recurses through the operands of sums, products, comparisons and the
    boolean connectives.

    It does not inspect `Quote`/`Set` payloads: quoted syntax and set members
    are held data, not evaluated mathematics in this proposition.  A declared
    function application is walked only in its arguments; its own domain is not
    invented here.  A `Binder` body and its annotations are left uninspected in
    this batch because their bound indices need binder-aware premises.
    `Guarded`/`Piecewise` are walked structurally, not with branch-local
    evaluation; this is a conservative over-approximation, not a full partial
    function semantics.

    Premises are deduplicated by structural term in first-occurrence order.  A
    language without an `Ne` head cannot state `base != 0`, so the walker
    returns `Ty.Unsupported` rather than silently dropping the premise.
    """

    premises: list[T.Term] = []
    seen: set[T.Term] = set()

    def add(premise: T.Term) -> None:
        if premise not in seen:
            seen.add(premise)
            premises.append(premise)

    def walk(current: T.Term) -> Ty.Unsupported | None:
        if isinstance(current, T.Apply):
            if not isinstance(current.operator, T.SymbolRef):
                # Typing refuses a non-symbol operator before this walk; a
                # nested application in operator position cannot carry a
                # structural power premise this layer knows how to scope.
                return None
            head = signature.head_of(current.operator.symbol_id)
            if head is None:
                # A declared function application: its domain is not known
                # here, so only its evaluated arguments are walked.
                for argument in current.arguments:
                    failure = walk(argument)
                    if failure is not None:
                        return failure
                return None
            if head in (StructuralHead.QUOTE, StructuralHead.SET):
                # Quoted syntax and set members are held data, not evaluated
                # mathematics in this proposition.
                return None
            if head is StructuralHead.POWER and len(current.arguments) == 2:
                base, exponent = current.arguments
                if isinstance(exponent, T.IntLit) and exponent.value <= 0:
                    ne_symbol = signature.symbol_of(StructuralHead.NE)
                    if ne_symbol is None:
                        return Ty.Unsupported(
                            "the language has no inequality head for a "
                            "nonpositive integer power's nonzero-base "
                            "definedness premise"
                        )
                    add(
                        T.app(
                            T.symbol(ne_symbol, StructuralHead.NE.value),
                            base,
                            T.number(0),
                        )
                    )
                failure = walk(base)
                if failure is not None:
                    return failure
                return walk(exponent)
            # Every other structural head (Plus, Times, comparisons,
            # And/Or/Not/Implies, Guarded, Piecewise) is strict at this
            # structural level: walk every operand.  Branch-local
            # Guarded/Piecewise semantics are not modelled here.
            for argument in current.arguments:
                failure = walk(argument)
                if failure is not None:
                    return failure
            return None
        if isinstance(current, T.Binder):
            # Bound indices need binder-aware premises; the body and its
            # annotations are left uninspected rather than issuing an
            # unscoped premise.
            return None
        # Literals, symbols and quoted syntax carry no structural premise.
        return None

    failure = walk(term)
    if failure is not None:
        return failure
    return tuple(premises)


def check(
    term: T.Term,
    signature: LanguageSignature,
    environment: Ty.SortEnvironment,
    meaning: MeaningKey,
) -> PropositionOutcome:
    """Issue a `Proposition`, or explain why the term is not one.

    A wrong sort is reported as `IllTyped`: calling `x + 1` a proposition is a
    type error, not a false statement.

    After typing, the structural definedness premises of the typed term are
    collected and issued as propositions in the same signature, environment and
    meaning.  Each premise recursively records its own premises, so a nested
    nonpositive power keeps its full chain of nonzero-base conditions.  A
    premise that cannot be issued is returned unchanged; it is never dropped.
    """
    typed = Ty.typed(term, signature, environment, meaning)
    if not isinstance(typed, Ty.TypedExpr):
        return typed
    if typed.sort != S.PROPOSITION:
        return Ty.IllTyped(
            f"a proposition needs proposition sort, got {typed.sort!r}"
        )
    raw_premises = _structural_premises(typed.term, signature)
    if isinstance(raw_premises, Ty.Unsupported):
        return raw_premises
    premises: list[Proposition] = []
    for premise_term in raw_premises:
        if premise_term == typed.term:
            return Ty.Unsupported(
                "a definedness premise cannot be the proposition itself"
            )
        premise = check(premise_term, signature, environment, meaning)
        if not isinstance(premise, Proposition):
            return premise
        premises.append(premise)
    return _issue_proposition(typed.term, meaning, tuple(premises))


def negates(
    outer: T.Term,
    inner: T.Term,
    signature: LanguageSignature,
) -> bool:
    """Whether `outer` is exactly `not inner` in this language."""
    not_symbol = signature.symbol_of(StructuralHead.NOT)
    if not_symbol is None:
        return False
    head = T.symbol(not_symbol, StructuralHead.NOT.value)
    return (
        isinstance(outer, T.Apply)
        and outer.operator == head
        and len(outer.arguments) == 1
        and outer.arguments[0] == inner
    )


__all__ = [
    "Proposition",
    "PropositionOutcome",
    "check",
    "negates",
]
