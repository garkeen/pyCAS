"""Pattern metalanguage: a pattern is not a term.

PatternVar / PatternSeq are not Term subclasses, so they can never appear in a
user expression, a domain projection or a mathematical equality test. The term
layer holds mathematical objects only.

A literal is used directly as a pattern: pointer equality of interned terms is
literal matching, so no wrapper type is needed and a pattern argument has type
``PatternLike``.

Rule declarations (DSL) are parsed through the pattern channel by the loader,
producing Pattern objects; template instantiation produces Terms. Pattern
variables therefore occur in exactly two places: matching and instantiation.
"""

from __future__ import annotations

from collections.abc import Iterable, Mapping
from dataclasses import dataclass
from typing import TypeAlias

from cas.errors import BudgetExceeded, ParseError
from cas.syntax import term as T


@dataclass(frozen=True, order=True, slots=True)
class PatternSortKey:
    """Comparable key shared by literals, holes and pattern calls."""

    kind: int
    text: str
    term: T.SortKey
    children: tuple[PatternSortKey, ...]


_hp = 0


def _next_hp() -> int:
    global _hp
    _hp += 1
    return _hp


class Pattern:
    """Base of the closed pattern hierarchy with interned pointer semantics."""

    __slots__ = ("_h",)

    _h: int

    def __hash__(self) -> int:
        return self._h

    def __eq__(self, other: object) -> bool:
        return self is other

    def __ne__(self, other: object) -> bool:
        return self is not other

    def __lt__(self, other: Pattern) -> bool:
        if not isinstance(other, Pattern):
            return NotImplemented
        return sort_key(self) < sort_key(other)


class PatternVar(Pattern):
    __slots__ = ("name", "pred")

    name: str
    pred: str | None

    def __init__(self, name: str, pred: str | None = None) -> None:
        self.name = name
        self.pred = pred
        self._h = _next_hp()

    def __repr__(self) -> str:
        return f"?{self.name}" + (f"::{self.pred}" if self.pred else "")


class PatternSeq(Pattern):
    __slots__ = ("name",)

    name: str

    def __init__(self, name: str) -> None:
        self.name = name
        self._h = _next_hp()

    def __repr__(self) -> str:
        return f"??{self.name}"


class PatternCall(Pattern):
    __slots__ = ("head", "args")

    head: T.Sym
    args: tuple[PatternLike, ...]

    def __init__(self, head: T.Sym, args: tuple[PatternLike, ...], h: int) -> None:
        self.head = head
        self.args = args
        self._h = h

    def __repr__(self) -> str:
        return f"{self.head.name}{tuple(repr(argument) for argument in self.args)}"

PatternLike: TypeAlias = T.Term | Pattern
PatternSubstitutionValue: TypeAlias = T.Term | tuple[T.Term, ...]
PatternSubstitution: TypeAlias = Mapping[str, PatternSubstitutionValue]


_VARS: dict[tuple[str, str | None], PatternVar] = {}
_SEQS: dict[str, PatternSeq] = {}
_CALLS: dict[tuple[int, tuple[int, ...]], PatternCall] = {}

# Pattern interning is bounded like every other cache: rule declarations are a
# finite set, but the pattern channel also parses user input, so an unbounded
# table would grow with the session. Reaching the cap drops the whole table; the
# entries are cheap to rebuild and no consumer compares patterns by pointer.
_PATTERN_INTERN_CAP = 1 << 14


def PV(name: str, pred: str | None = None) -> PatternVar:
    key = (name, pred)
    pattern = _VARS.get(key)
    if pattern is None:
        pattern = PatternVar(name, pred)
        if len(_VARS) >= _PATTERN_INTERN_CAP:
            _VARS.clear()
        _VARS[key] = pattern
    return pattern


def PS(name: str) -> PatternSeq:
    pattern = _SEQS.get(name)
    if pattern is None:
        pattern = PatternSeq(name)
        if len(_SEQS) >= _PATTERN_INTERN_CAP:
            _SEQS.clear()
        _SEQS[name] = pattern
    return pattern


def _flatten_ac(head: T.Sym, args: Iterable[PatternLike]) -> list[PatternLike]:
    """Flatten and deterministically sort same-head AC pattern arguments."""
    flat: list[PatternLike] = []
    for argument in args:
        if isinstance(argument, PatternCall) and argument.head is head:
            flat.extend(argument.args)
        else:
            flat.append(argument)
    flat.sort(key=sort_key)
    return flat


def pcall(head: T.Sym, args: Iterable[PatternLike]) -> PatternCall:
    """Intern a pattern call, applying the term layer's AC shape."""
    arguments = list(args)
    if head.name in T.AC:
        arguments = _flatten_ac(head, arguments)
    key = (head._h, tuple(argument._h for argument in arguments))
    pattern = _CALLS.get(key)
    if pattern is None:
        pattern = PatternCall(head, tuple(arguments), _next_hp())
        if len(_CALLS) >= _PATTERN_INTERN_CAP:
            _CALLS.clear()
        _CALLS[key] = pattern
    return pattern


def sort_key(pattern: PatternLike) -> PatternSortKey:
    """Return a total order shared by term literals and pattern nodes."""
    if isinstance(pattern, T.Term):
        return PatternSortKey(10, "", T.sort_key(pattern), ())
    if isinstance(pattern, PatternVar):
        return PatternSortKey(0, pattern.name, T.SortKey(0), ())
    if isinstance(pattern, PatternSeq):
        return PatternSortKey(1, pattern.name, T.SortKey(0), ())
    if not isinstance(pattern, PatternCall):
        raise ParseError(f"unsupported pattern node: {pattern!r}")
    return PatternSortKey(
        11,
        "",
        T.sort_key(pattern.head),
        tuple(sort_key(argument) for argument in pattern.args),
    )


def has_holes(pattern: PatternLike) -> bool:
    """Return whether a pattern contains a hole."""
    if isinstance(pattern, T.Term):
        return False
    if isinstance(pattern, PatternCall):
        return any(has_holes(argument) for argument in pattern.args)
    return True


def root_key(pattern: PatternLike) -> str:
    """Return the rule-index root key for a pattern."""
    if isinstance(pattern, T.Expr):
        return pattern.head.name
    if isinstance(pattern, T.Term):
        return pattern.__class__.__name__ + ":" + repr(pattern)
    if isinstance(pattern, PatternCall):
        return pattern.head.name
    return "*"


def instantiate(
    pattern: PatternLike,
    substitution: PatternSubstitution,
) -> T.Term:
    """Instantiate a template pattern into the term language."""
    if isinstance(pattern, T.Term):
        return pattern
    if isinstance(pattern, PatternVar):
        value = substitution.get(pattern.name)
        if not isinstance(value, T.Term):
            raise ParseError(
                f"unbound pattern variable ?{pattern.name} in rule template"
            )
        return value
    if isinstance(pattern, PatternSeq):
        raise BudgetExceeded(
            message=f"sequence hole ??{pattern.name} not in arg position"
        )
    if not isinstance(pattern, PatternCall):
        raise ParseError(f"unsupported pattern node: {pattern!r}")
    if pattern.head.name == "Quote":
        return T.intern_expr(
            pattern.head,
            tuple(_instantiate_raw(argument, substitution) for argument in pattern.args),
        )
    output: list[T.Term] = []
    for argument in pattern.args:
        if isinstance(argument, PatternSeq):
            sequence = substitution.get(argument.name)
            if not isinstance(sequence, tuple):
                raise ParseError(
                    f"unbound sequence hole ??{argument.name} in rule template"
                )
            output.extend(sequence)
        else:
            output.append(instantiate(argument, substitution))
    return T.mk(pattern.head, output)


def _instantiate_raw(
    pattern: PatternLike,
    substitution: PatternSubstitution,
) -> T.Term:
    """Instantiate held structure without AC normalization."""
    if isinstance(pattern, T.Term):
        return pattern
    if isinstance(pattern, PatternVar):
        value = substitution.get(pattern.name)
        if not isinstance(value, T.Term):
            raise ParseError(
                f"unbound pattern variable ?{pattern.name} in rule template"
            )
        return value
    if isinstance(pattern, PatternSeq):
        raise BudgetExceeded(
            message=f"sequence hole ??{pattern.name} not in arg position"
        )
    if not isinstance(pattern, PatternCall):
        raise ParseError(f"unsupported pattern node: {pattern!r}")
    output: list[T.Term] = []
    for argument in pattern.args:
        if isinstance(argument, PatternSeq):
            sequence = substitution.get(argument.name)
            if not isinstance(sequence, tuple):
                raise ParseError(
                    f"unbound sequence hole ??{argument.name} in rule template"
                )
            output.extend(sequence)
        else:
            output.append(_instantiate_raw(argument, substitution))
    return T.intern_expr(pattern.head, tuple(output))
