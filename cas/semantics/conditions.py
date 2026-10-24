"""Exact ground evaluation, condition normalization and guarded implication.

Conditions are propositions over exact arithmetic, comparisons and boolean
connectives. This module evaluates the ground fragment, normalizes conjunctions
of one-atom comparisons into bounds, and decides a restricted implication
relation by interval reasoning. All decisions are conservative: an unknown atom
is never assumed true, and unrelated atoms never exchange information.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from fractions import Fraction

from cas.language.signatures import LanguageSignature, StructuralHead
from cas.syntax import term as T

_COMPARISONS = frozenset(
    {
        StructuralHead.EQ,
        StructuralHead.NE,
        StructuralHead.LT,
        StructuralHead.LE,
        StructuralHead.GT,
        StructuralHead.GE,
    }
)

_DUAL = {
    StructuralHead.EQ: StructuralHead.NE,
    StructuralHead.NE: StructuralHead.EQ,
    StructuralHead.LT: StructuralHead.GE,
    StructuralHead.LE: StructuralHead.GT,
    StructuralHead.GT: StructuralHead.LE,
    StructuralHead.GE: StructuralHead.LT,
}

_FLIP = {
    StructuralHead.EQ: StructuralHead.EQ,
    StructuralHead.NE: StructuralHead.NE,
    StructuralHead.LT: StructuralHead.GT,
    StructuralHead.LE: StructuralHead.GE,
    StructuralHead.GT: StructuralHead.LT,
    StructuralHead.GE: StructuralHead.LE,
}


def ground_value(
    term: T.Term,
    signature: LanguageSignature,
) -> Fraction | bool | None:
    """Evaluate a ground term exactly; None means the fragment cannot decide it."""
    if isinstance(term, T.IntLit):
        return Fraction(term.value)
    if isinstance(term, T.RatLit):
        return term.value
    if isinstance(term, T.BoolLit):
        return term.value
    if not isinstance(term, T.Apply) or not isinstance(
        term.operator, T.SymbolRef
    ):
        return None
    head = signature.head_of(term.operator.symbol_id)
    if head is None:
        return None
    if head in (StructuralHead.PLUS, StructuralHead.TIMES):
        return _arithmetic(head, term.arguments, signature)
    if head is StructuralHead.POWER:
        return _power(term.arguments, signature)
    if head in _COMPARISONS:
        return _comparison(head, term.arguments, signature)
    if head in (StructuralHead.AND, StructuralHead.OR):
        return _junction(head, term.arguments, signature)
    if head is StructuralHead.NOT:
        value = ground_value(term.arguments[0], signature)
        return None if not isinstance(value, bool) else not value
    if head is StructuralHead.IMPLIES:
        left = ground_value(term.arguments[0], signature)
        right = ground_value(term.arguments[1], signature)
        return _implies_truth(left, right)
    return None


def condition_truth(
    term: T.Term,
    signature: LanguageSignature,
) -> bool | None:
    value = ground_value(term, signature)
    return value if isinstance(value, bool) else None


def simplify(
    term: T.Term,
    signature: LanguageSignature,
) -> T.Term:
    truth = condition_truth(term, signature)
    if truth is True:
        return T.TRUE
    if truth is False:
        return T.FALSE
    return term


def and_all(
    signature: LanguageSignature,
    *conditions: T.Term | None,
) -> T.Term:
    """A conjunction with exact folding, bound normalization and de-duplication."""
    flattened: list[T.Term] = []
    for condition in conditions:
        if condition is None:
            continue
        normalized = _normalize_not(condition, signature)
        if isinstance(normalized, T.Apply) and isinstance(
            normalized.operator, T.SymbolRef
        ) and signature.head_of(
            normalized.operator.symbol_id
        ) is StructuralHead.AND:
            flattened.extend(normalized.arguments)
        else:
            flattened.append(normalized)

    order: list[tuple[str, object]] = []
    intervals: dict[T.Term, _Interval] = {}
    opaque: dict[T.Term, None] = {}
    for condition in flattened:
        truth = condition_truth(condition, signature)
        if truth is False:
            return T.FALSE
        if truth is True:
            continue
        comparison = _normalize_comparison(condition, signature)
        if comparison is None:
            if condition not in opaque:
                opaque[condition] = None
                order.append(("opaque", condition))
            continue
        interval = intervals.get(comparison.atom)
        if interval is None:
            interval = _Interval()
            intervals[comparison.atom] = interval
            order.append(("atom", comparison.atom))
        interval.add(comparison)

    kept: list[T.Term] = []
    for kind, value in order:
        if kind == "opaque":
            assert isinstance(value, T.Term)
            kept.append(value)
            continue
        assert isinstance(value, T.Term)
        terms = _interval_terms(value, intervals[value], signature)
        if terms is None:
            return T.FALSE
        kept.extend(terms)
    if not kept:
        return T.TRUE
    if len(kept) == 1:
        return kept[0]
    return T.app(_head(signature, StructuralHead.AND), *kept)


def implies(
    assumption: T.Term,
    goal: T.Term,
    signature: LanguageSignature,
) -> bool | None:
    """Whether `assumption` entails `goal` in the restricted condition logic."""
    return _implies(_normalize_not(assumption, signature), _normalize_not(goal, signature), signature)


def equivalent(
    left: T.Term,
    right: T.Term,
    signature: LanguageSignature,
) -> bool | None:
    forward = implies(left, right, signature)
    backward = implies(right, left, signature)
    if forward is False or backward is False:
        return False
    if forward is True and backward is True:
        return True
    return None


@dataclass(frozen=True, slots=True)
class _Comparison:
    atom: T.Term
    relation: StructuralHead
    bound: Fraction


def _normalize_comparison(
    term: T.Term,
    signature: LanguageSignature,
) -> _Comparison | None:
    if not isinstance(term, T.Apply) or not isinstance(
        term.operator, T.SymbolRef
    ):
        return None
    head = signature.head_of(term.operator.symbol_id)
    if head not in _COMPARISONS or len(term.arguments) != 2:
        return None
    left, right = term.arguments
    left_form = _linear(left, signature)
    right_form = _linear(right, signature)
    if left_form is None or right_form is None:
        return None
    left_atoms, left_constant = left_form
    right_atoms, right_constant = right_form
    atoms = dict(left_atoms)
    for atom, coefficient in right_atoms.items():
        atoms[atom] = atoms.get(atom, Fraction(0)) - coefficient
    atoms = {
        atom: coefficient
        for atom, coefficient in atoms.items()
        if coefficient != 0
    }
    constant = left_constant - right_constant
    if len(atoms) != 1:
        return None
    (atom, coefficient), = atoms.items()
    bound = -constant / coefficient
    relation = head if coefficient > 0 else _FLIP[head]
    return _Comparison(atom, relation, bound)


def _linear(
    term: T.Term,
    signature: LanguageSignature,
) -> tuple[dict[T.Term, Fraction], Fraction] | None:
    value = ground_value(term, signature)
    if isinstance(value, Fraction):
        return {}, value
    if not isinstance(term, T.Apply) or not isinstance(
        term.operator, T.SymbolRef
    ):
        return {term: Fraction(1)}, Fraction(0)
    head = signature.head_of(term.operator.symbol_id)
    if head is StructuralHead.PLUS:
        atoms: dict[T.Term, Fraction] = {}
        constant = Fraction(0)
        for argument in term.arguments:
            part_form = _linear(argument, signature)
            if part_form is None:
                return None
            part_atoms, part_constant = part_form
            for atom, coefficient in part_atoms.items():
                atoms[atom] = atoms.get(atom, Fraction(0)) + coefficient
            constant += part_constant
        return atoms, constant
    if head is StructuralHead.TIMES:
        form: tuple[dict[T.Term, Fraction], Fraction] = (
            {},
            Fraction(1),
        )
        for factor in term.arguments:
            part = _linear(factor, signature)
            if part is None:
                return None
            next_form = _multiply_linear(form, part)
            if next_form is None:
                return {term: Fraction(1)}, Fraction(0)
            form = next_form
        return form
    return {term: Fraction(1)}, Fraction(0)


def _multiply_linear(
    left: tuple[dict[T.Term, Fraction], Fraction],
    right: tuple[dict[T.Term, Fraction], Fraction],
) -> tuple[dict[T.Term, Fraction], Fraction] | None:
    left_atoms, left_constant = left
    right_atoms, right_constant = right
    if left_atoms and right_atoms:
        return None
    if not left_atoms:
        return (
            {
                atom: coefficient * left_constant
                for atom, coefficient in right_atoms.items()
            },
            left_constant * right_constant,
        )
    return (
        {
            atom: coefficient * right_constant
            for atom, coefficient in left_atoms.items()
        },
        left_constant * right_constant,
    )


def _normalize_not(
    term: T.Term,
    signature: LanguageSignature,
) -> T.Term:
    if not isinstance(term, T.Apply) or not isinstance(
        term.operator, T.SymbolRef
    ):
        return term
    head = signature.head_of(term.operator.symbol_id)
    if head is StructuralHead.NOT and len(term.arguments) == 1:
        operand = _normalize_not(term.arguments[0], signature)
        if isinstance(operand, T.BoolLit):
            return T.FALSE if operand.value else T.TRUE
        if isinstance(operand, T.Apply) and isinstance(
            operand.operator, T.SymbolRef
        ):
            inner = signature.head_of(operand.operator.symbol_id)
            if inner in _COMPARISONS:
                return T.app(
                    _head(signature, _DUAL[inner]),
                    *operand.arguments,
                )
            if inner is StructuralHead.NOT and len(operand.arguments) == 1:
                return operand.arguments[0]
        return T.app(_head(signature, StructuralHead.NOT), operand)
    if head in (StructuralHead.AND, StructuralHead.OR):
        arguments = tuple(
            _normalize_not(argument, signature)
            for argument in term.arguments
        )
        if all(
            new is old for new, old in zip(arguments, term.arguments)
        ):
            return term
        return T.app(_head(signature, head), *arguments)
    return term


@dataclass(slots=True)
class _Interval:
    lower: tuple[Fraction, bool] | None = None
    upper: tuple[Fraction, bool] | None = None
    equality: Fraction | None = None
    disequalities: list[Fraction] = field(default_factory=list)
    contradiction: bool = False

    def add(self, comparison: _Comparison) -> None:
        relation = comparison.relation
        value = comparison.bound
        if relation is StructuralHead.EQ:
            if self.equality is not None and self.equality != value:
                self.contradiction = True
            else:
                self.equality = value
        elif relation is StructuralHead.NE:
            self.disequalities.append(value)
        elif relation in (StructuralHead.GT, StructuralHead.GE):
            strict = relation is StructuralHead.GT
            if self.lower is None:
                self.lower = (value, strict)
            elif value > self.lower[0]:
                self.lower = (value, strict)
            elif value == self.lower[0] and strict:
                self.lower = (value, True)
        else:
            strict = relation is StructuralHead.LT
            if self.upper is None:
                self.upper = (value, strict)
            elif value < self.upper[0]:
                self.upper = (value, strict)
            elif value == self.upper[0] and strict:
                self.upper = (value, True)

    def is_contradictory(self) -> bool:
        if self.contradiction:
            return True
        if self.equality is not None:
            if self.equality in self.disequalities:
                return True
            if self.lower is not None and (
                self.lower[0] > self.equality
                or (
                    self.lower[0] == self.equality
                    and self.lower[1]
                )
            ):
                return True
            if self.upper is not None and (
                self.upper[0] < self.equality
                or (
                    self.upper[0] == self.equality
                    and self.upper[1]
                )
            ):
                return True
            return False
        if self.lower is not None and self.upper is not None:
            if self.lower[0] > self.upper[0]:
                return True
            if self.lower[0] == self.upper[0] and (
                self.lower[1] or self.upper[1]
            ):
                return True
            if (
                self.lower[0] == self.upper[0]
                and not self.lower[1]
                and not self.upper[1]
                and self.lower[0] in self.disequalities
            ):
                return True
        return False


def _interval_terms(
    atom: T.Term,
    interval: _Interval,
    signature: LanguageSignature,
) -> list[T.Term] | None:
    if interval.is_contradictory():
        return None
    equality = interval.equality
    if equality is not None:
        lower_problem = interval.lower is not None and (
            interval.lower[0] > equality
            or (
                interval.lower[0] == equality
                and interval.lower[1]
            )
        )
        upper_problem = interval.upper is not None and (
            interval.upper[0] < equality
            or (
                interval.upper[0] == equality
                and interval.upper[1]
            )
        )
        if lower_problem or upper_problem or equality in interval.disequalities:
            return None
        return [_comparison_term(atom, StructuralHead.EQ, equality, signature)]

    lower = interval.lower
    upper = interval.upper
    if lower is not None and upper is not None:
        if lower[0] > upper[0]:
            return None
        if lower[0] == upper[0] and (lower[1] or upper[1]):
            return None
    terms: list[T.Term] = []
    if (
        lower is not None
        and upper is not None
        and lower[0] == upper[0]
        and not lower[1]
        and not upper[1]
    ):
        terms.append(
            _comparison_term(atom, StructuralHead.EQ, lower[0], signature)
        )
    else:
        if lower is not None:
            terms.append(
                _comparison_term(
                    atom,
                    StructuralHead.GT if lower[1] else StructuralHead.GE,
                    lower[0],
                    signature,
                )
            )
        if upper is not None:
            terms.append(
                _comparison_term(
                    atom,
                    StructuralHead.LT if upper[1] else StructuralHead.LE,
                    upper[0],
                    signature,
                )
            )
    for value in interval.disequalities:
        if not _interval_excludes(interval, value):
            terms.append(
                _comparison_term(atom, StructuralHead.NE, value, signature)
            )
    return terms


def _interval_excludes(interval: _Interval, value: Fraction) -> bool:
    if interval.equality is not None:
        return interval.equality != value
    if (
        interval.lower is not None
        and interval.upper is not None
        and interval.lower[0] == interval.upper[0]
        and not interval.lower[1]
        and not interval.upper[1]
    ):
        return value != interval.lower[0]
    if interval.lower is not None:
        lower, strict = interval.lower
        if lower > value or (lower == value and strict):
            return True
    if interval.upper is not None:
        upper, strict = interval.upper
        if upper < value or (upper == value and strict):
            return True
    return False


def _comparison_term(
    atom: T.Term,
    relation: StructuralHead,
    bound: Fraction,
    signature: LanguageSignature,
) -> T.Term:
    return T.app(
        _head(signature, relation), atom, T.number(bound)
    )


def _implies(
    assumption: T.Term,
    goal: T.Term,
    signature: LanguageSignature,
) -> bool | None:
    if assumption == goal:
        return True
    assumption_truth = condition_truth(assumption, signature)
    if assumption_truth is False:
        return True
    if assumption_truth is True:
        return _goal_only(goal, signature)
    goal_truth = condition_truth(goal, signature)
    if goal_truth is True:
        return True

    if _is_head(goal, StructuralHead.OR, signature):
        assert isinstance(goal, T.Apply)
        results = [
            _implies(assumption, argument, signature)
            for argument in goal.arguments
        ]
        if any(result is True for result in results):
            return True
        if all(result is False for result in results):
            return False
        return None

    if _is_head(goal, StructuralHead.AND, signature):
        assert isinstance(goal, T.Apply)
        results = [
            _implies(assumption, argument, signature)
            for argument in goal.arguments
        ]
        if any(result is False for result in results):
            return False
        if all(result is True for result in results):
            return True
        return None

    if _is_head(assumption, StructuralHead.OR, signature):
        assert isinstance(assumption, T.Apply)
        results = [
            _implies(argument, goal, signature)
            for argument in assumption.arguments
        ]
        if any(result is False for result in results):
            return False
        if all(result is True for result in results):
            return True
        return None

    conjuncts = _conjuncts(assumption, signature)
    intervals: dict[T.Term, _Interval] = {}
    opaque: set[T.Term] = set()
    for conjunct in conjuncts:
        comparison = _normalize_comparison(conjunct, signature)
        if comparison is None:
            opaque.add(conjunct)
        else:
            known = intervals.setdefault(comparison.atom, _Interval())
            known.add(comparison)
    if any(interval.is_contradictory() for interval in intervals.values()):
        return True
    if goal_truth is False:
        return False

    target = _normalize_comparison(goal, signature)
    if target is None:
        return True if goal in opaque else None
    interval = intervals.get(target.atom)
    if interval is None:
        return None
    return _interval_implies(interval, target)


def _goal_only(
    goal: T.Term,
    signature: LanguageSignature,
) -> bool | None:
    truth = condition_truth(goal, signature)
    if truth is True:
        return True
    if truth is False:
        return False
    return None


def _conjuncts(
    term: T.Term,
    signature: LanguageSignature,
) -> tuple[T.Term, ...]:
    if isinstance(term, T.Apply) and _is_head(
        term, StructuralHead.AND, signature
    ):
        out: list[T.Term] = []
        for argument in term.arguments:
            out.extend(_conjuncts(argument, signature))
        return tuple(out)
    return (term,)


def _interval_implies(
    interval: _Interval,
    goal: _Comparison,
) -> bool | None:
    if interval.is_contradictory():
        return True
    relation = goal.relation
    bound = goal.bound
    if interval.equality is not None:
        value = interval.equality
        return _holds(value, relation, bound)
    if relation is StructuralHead.EQ:
        if _interval_is_point(interval, bound):
            return True
        if _interval_excludes(interval, bound):
            return False
        return None
    if relation is StructuralHead.NE:
        if _interval_excludes(interval, bound):
            return True
        if _interval_is_point(interval, bound):
            return False
        return None
    if relation is StructuralHead.GT:
        if interval.lower is not None and (
            interval.lower[0] > bound
            or (interval.lower[0] == bound and interval.lower[1])
        ):
            return True
        if interval.upper is not None and interval.upper[0] <= bound:
            return False
        return None
    if relation is StructuralHead.GE:
        if interval.lower is not None and interval.lower[0] >= bound:
            return True
        if interval.upper is not None and interval.upper[0] < bound:
            return False
        return None
    if relation is StructuralHead.LT:
        if interval.upper is not None and (
            interval.upper[0] < bound
            or (interval.upper[0] == bound and interval.upper[1])
        ):
            return True
        if interval.lower is not None and interval.lower[0] >= bound:
            return False
        return None
    if interval.upper is not None and interval.upper[0] <= bound:
        return True
    if interval.lower is not None and interval.lower[0] > bound:
        return False
    return None


def _interval_is_point(interval: _Interval, value: Fraction) -> bool:
    if interval.equality is not None:
        return interval.equality == value
    return (
        interval.lower is not None
        and interval.upper is not None
        and interval.lower[0] == value
        and interval.upper[0] == value
        and not interval.lower[1]
        and not interval.upper[1]
    )


def _holds(
    value: Fraction,
    relation: StructuralHead,
    bound: Fraction,
) -> bool:
    if relation is StructuralHead.EQ:
        return value == bound
    if relation is StructuralHead.NE:
        return value != bound
    if relation is StructuralHead.LT:
        return value < bound
    if relation is StructuralHead.LE:
        return value <= bound
    if relation is StructuralHead.GT:
        return value > bound
    return value >= bound


def _is_head(
    term: T.Term,
    head: StructuralHead,
    signature: LanguageSignature,
) -> bool:
    return (
        isinstance(term, T.Apply)
        and isinstance(term.operator, T.SymbolRef)
        and signature.head_of(term.operator.symbol_id) is head
    )


def _head(signature: LanguageSignature, head: StructuralHead) -> T.SymbolRef:
    symbol_id = signature.symbol_of(head)
    if symbol_id is None:
        raise ValueError(f"the language has no symbol for {head.value}")
    return T.symbol(symbol_id, head.value)


def _arithmetic(
    head: StructuralHead,
    arguments: tuple[T.Term, ...],
    signature: LanguageSignature,
) -> Fraction | None:
    values: list[Fraction] = []
    for argument in arguments:
        value = ground_value(argument, signature)
        if not isinstance(value, Fraction):
            return None
        values.append(value)
    if not values:
        return None
    if head is StructuralHead.PLUS:
        return sum(values, Fraction(0))
    product = Fraction(1)
    for value in values:
        product *= value
    return product


def _power(
    arguments: tuple[T.Term, ...],
    signature: LanguageSignature,
) -> Fraction | None:
    if len(arguments) != 2:
        return None
    base = ground_value(arguments[0], signature)
    exponent = arguments[1]
    if not isinstance(base, Fraction) or not isinstance(exponent, T.IntLit):
        return None
    if exponent.value < 0 and base == 0:
        return None
    return base**exponent.value


def _comparison(
    head: StructuralHead,
    arguments: tuple[T.Term, ...],
    signature: LanguageSignature,
) -> bool | None:
    if len(arguments) != 2:
        return None
    left = ground_value(arguments[0], signature)
    right = ground_value(arguments[1], signature)
    if not isinstance(left, Fraction) or not isinstance(right, Fraction):
        return None
    return _holds(left, head, right)


def _junction(
    head: StructuralHead,
    arguments: tuple[T.Term, ...],
    signature: LanguageSignature,
) -> bool | None:
    unknown = False
    for argument in arguments:
        value = ground_value(argument, signature)
        if not isinstance(value, bool):
            unknown = True
            continue
        if head is StructuralHead.AND and not value:
            return False
        if head is StructuralHead.OR and value:
            return True
    if unknown:
        return None
    return head is StructuralHead.AND


def _implies_truth(
    left: Fraction | bool | None,
    right: Fraction | bool | None,
) -> bool | None:
    if left is False or right is True:
        return True
    if left is True and right is False:
        return False
    return None


__all__ = [
    "and_all",
    "condition_truth",
    "equivalent",
    "ground_value",
    "implies",
    "simplify",
]
