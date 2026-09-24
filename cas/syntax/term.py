"""Interned pure-syntax terms and their structural constructors."""

from __future__ import annotations

import weakref
from dataclasses import dataclass
from fractions import Fraction
from functools import partial
from typing import Iterable, TypeGuard


@dataclass(frozen=True, order=True)
class SortKey:
    kind: int
    text: str = ""
    number: int | Fraction = 0
    children: tuple[SortKey, ...] = ()


_hc = 0


def _next_h() -> int:
    global _hc
    _hc += 1
    return _hc


class Term:
    __slots__ = ("_h", "__weakref__")
    _h: int

    def __hash__(self) -> int:
        return self._h

    def __eq__(self, other: object) -> bool:
        return self is other

    def __ne__(self, other: object) -> bool:
        return self is not other

    def __lt__(self, other: Term) -> bool:
        return sort_key(self) < sort_key(other)


class Sym(Term):
    __slots__ = ("name",)
    name: str

    def __init__(self, name: str) -> None:
        self.name = name
        self._h = _next_h()

    def __repr__(self) -> str:
        return self.name


class Const(Term):
    __slots__ = ("name",)
    name: str

    def __init__(self, name: str) -> None:
        self.name = name
        self._h = _next_h()

    def __repr__(self) -> str:
        return self.name


class DB(Term):
    __slots__ = ("i",)
    i: int

    def __init__(self, i: int) -> None:
        self.i = i
        self._h = _next_h()

    def __repr__(self) -> str:
        return f"#{self.i}"


class BVal(Term):
    __slots__ = ("val",)
    val: bool

    def __init__(self, val: bool) -> None:
        self.val = val
        self._h = _next_h()

    def __repr__(self) -> str:
        return "True" if self.val else "False"


class Int(Term):
    __slots__ = ("v",)
    v: int

    def __init__(self, value: int) -> None:
        self.v = value
        self._h = _next_h()

    def __repr__(self) -> str:
        return str(self.v)


class Rat(Term):
    __slots__ = ("f",)
    f: Fraction

    def __init__(self, value: Fraction) -> None:
        self.f = value
        self._h = _next_h()

    def __repr__(self) -> str:
        return f"{self.f.numerator}/{self.f.denominator}"


class Special(Term):
    __slots__ = ("name",)
    name: str

    def __init__(self, name: str) -> None:
        self.name = name
        self._h = _next_h()

    def __repr__(self) -> str:
        return self.name


class Expr(Term):
    __slots__ = ("head", "args")
    head: Sym
    args: tuple[Term, ...]

    def __init__(self, head: Sym, args: tuple[Term, ...], value_hash: int) -> None:
        self.head = head
        self.args = args
        self._h = value_hash

    def __repr__(self) -> str:
        if self.head.name in _INFIX:
            operator = _INFIX[self.head.name]
            return "(" + f" {operator} ".join(repr(argument) for argument in self.args) + ")"
        return f"{self.head.name}{tuple(repr(argument) for argument in self.args)}"


class Bound(Term):
    __slots__ = ("hint", "body")
    hint: str
    body: Term

    def __init__(self, hint: str, body: Term, value_hash: int) -> None:
        self.hint = hint
        self.body = body
        self._h = value_hash

    def __repr__(self) -> str:
        return f"bound<{self.hint}>({self.body!r})"


_INFIX: dict[str, str] = {
    "Plus": "+",
    "Times": "*",
    "Power": "^",
    "Eq": "==",
    "Ne": "!=",
    "Lt": "<",
    "Le": "<=",
    "Gt": ">",
    "Ge": ">=",
    "And": "&&",
    "Or": "||",
}

_SYMS: weakref.WeakValueDictionary[str, Sym] = weakref.WeakValueDictionary()
_CONSTS: weakref.WeakValueDictionary[str, Const] = weakref.WeakValueDictionary()
_NUMS: weakref.WeakValueDictionary[int | Fraction, Int | Rat] = weakref.WeakValueDictionary()
_SPECIALS: weakref.WeakValueDictionary[str, Special] = weakref.WeakValueDictionary()
_EXPRS: weakref.WeakValueDictionary[tuple[int, tuple[int, ...]], Expr] = (
    weakref.WeakValueDictionary()
)
_BOUNDS: weakref.WeakValueDictionary[int, Bound] = weakref.WeakValueDictionary()
_DBS: weakref.WeakValueDictionary[int, DB] = weakref.WeakValueDictionary()


def DB_(index: int) -> DB:
    term = _DBS.get(index)
    if term is None:
        term = DB(index)
        _DBS[index] = term
    return term


TRUE = BVal(True)
FALSE = BVal(False)
UND = _SPECIALS.setdefault("Undefined", Special("Undefined"))
INFINITY = _SPECIALS.setdefault("Infinity", Special("Infinity"))
EMPTY_SET = _SPECIALS.setdefault("EmptySet", Special("EmptySet"))

AC = {"Plus", "Times", "And", "Or"}
BOOL_HEADS = {"And", "Or", "Not"}


def S(name: str) -> Sym:
    term = _SYMS.get(name)
    if term is None:
        term = Sym(name)
        _SYMS[name] = term
    return term


def C(name: str) -> Const:
    term = _CONSTS.get(name)
    if term is None:
        term = Const(name)
        _CONSTS[name] = term
    return term


def N(value: int | Fraction) -> Int | Rat:
    if isinstance(value, int):
        term = _NUMS.get(value)
        if term is None:
            term = Int(value)
            _NUMS[value] = term
        return term
    fraction = Fraction(value)
    if fraction.denominator == 1:
        return N(fraction.numerator)
    term = _NUMS.get(fraction)
    if term is None:
        term = Rat(fraction)
        _NUMS[fraction] = term
    return term


def SP(name: str) -> Special:
    term = _SPECIALS.get(name)
    if term is None:
        term = Special(name)
        _SPECIALS[name] = term
    return term


def is_num(term: Term) -> TypeGuard[Int | Rat]:
    return isinstance(term, (Int, Rat))


def num_val(term: Term) -> Fraction:
    if isinstance(term, Int):
        return Fraction(term.v)
    if isinstance(term, Rat):
        return term.f
    raise TypeError(f"not a numeric term: {term!r}")


def sign_num(term: Term) -> int:
    value = num_val(term)
    return (value > 0) - (value < 0)


ZERO = N(0)
ONE = N(1)
TWO = N(2)
MONE = N(-1)


def sort_key(term: Term) -> SortKey:
    if isinstance(term, Sym):
        return SortKey(0, term.name)
    if isinstance(term, Const):
        return SortKey(1, term.name)
    if isinstance(term, BVal):
        return SortKey(2, number=0 if term.val else 1)
    if isinstance(term, DB):
        return SortKey(3, number=term.i)
    if isinstance(term, Int):
        return SortKey(25, number=Fraction(term.v))
    if isinstance(term, Rat):
        return SortKey(25, number=term.f)
    if isinstance(term, Special):
        return SortKey(8, term.name)
    if isinstance(term, Expr):
        return SortKey(20, children=(
            sort_key(term.head),
            *(sort_key(argument) for argument in term.args),
        ))
    if isinstance(term, Bound):
        return SortKey(21, children=(sort_key(term.body),))
    return SortKey(22, repr(term))


def _flatten_ac(head: Sym, args: Iterable[Term]) -> list[Term]:
    flat: list[Term] = []
    for argument in args:
        if isinstance(argument, Expr) and argument.head is head:
            flat.extend(argument.args)
        else:
            flat.append(argument)
    return sorted(flat)


def _fold_bool_ac(head: Sym, args: Iterable[Term]) -> Term | list[Term]:
    name = head.name
    flat: list[Term] = []
    for argument in args:
        if isinstance(argument, Expr) and argument.head is head:
            flat.extend(argument.args)
        else:
            flat.append(argument)
    output: list[Term] = []
    seen: set[int] = set()
    for argument in flat:
        if isinstance(argument, BVal):
            if (name == "And" and not argument.val) or (
                name == "Or" and argument.val
            ):
                return argument
            continue
        if argument._h in seen:
            continue
        seen.add(argument._h)
        output.append(argument)
    if not output:
        return TRUE if name == "And" else FALSE
    if len(output) == 1:
        return output[0]
    return sorted(output)


def intern_expr(head: Sym, args: tuple[Term, ...]) -> Expr:
    key = (head._h, tuple(argument._h for argument in args))
    term = _EXPRS.get(key)
    if term is None:
        value_hash = _next_h()
        term = Expr(head, args, value_hash)
        _EXPRS[key] = term
    return term


def mk(head: Sym, args: Iterable[Term]) -> Term:
    arguments = tuple(args)
    name = head.name
    if name in AC:
        if name in BOOL_HEADS:
            folded = _fold_bool_ac(head, arguments)
            if isinstance(folded, list):
                return intern_expr(head, tuple(folded))
            return folded
        return intern_expr(head, tuple(_flatten_ac(head, arguments)))
    return intern_expr(head, arguments)


def call(name: str, *args: Term) -> Term:
    return mk(S(name), args)


plus = partial(call, "Plus")
times = partial(call, "Times")
pw = partial(call, "Power")


def neg(argument: Term) -> Term:
    return times(MONE, argument)


def div(left: Term, right: Term) -> Term:
    return times(left, pw(right, MONE))


def eq(left: Term, right: Term) -> Expr:
    result = mk(S("Eq"), (left, right))
    assert isinstance(result, Expr)
    return result


def lt(left: Term, right: Term) -> Expr:
    result = mk(S("Lt"), (left, right))
    assert isinstance(result, Expr)
    return result


def le(left: Term, right: Term) -> Expr:
    result = mk(S("Le"), (left, right))
    assert isinstance(result, Expr)
    return result


def gt(left: Term, right: Term) -> Expr:
    result = mk(S("Gt"), (left, right))
    assert isinstance(result, Expr)
    return result


def ge(left: Term, right: Term) -> Expr:
    result = mk(S("Ge"), (left, right))
    assert isinstance(result, Expr)
    return result


def ne(left: Term, right: Term) -> Expr:
    result = mk(S("Ne"), (left, right))
    assert isinstance(result, Expr)
    return result


def and_(*args: Term) -> Term:
    return mk(S("And"), args)


def implies(left: Term, right: Term) -> Expr:
    result = mk(S("Implies"), (left, right))
    assert isinstance(result, Expr)
    return result


def is_eq(term: Term) -> bool:
    return isinstance(term, Expr) and term.head.name == "Eq"


def or_(*args: Term) -> Term:
    return mk(S("Or"), args)


def not_(argument: Term) -> Expr:
    result = mk(S("Not"), (argument,))
    assert isinstance(result, Expr)
    return result


def quote(argument: Term) -> Expr:
    result = mk(S("Quote"), (argument,))
    assert isinstance(result, Expr)
    return result


def _shift(term: Term, delta: int, cutoff: int) -> Term:
    if isinstance(term, DB):
        return DB_(term.i + delta) if term.i >= cutoff else term
    if isinstance(term, Expr):
        return mk(term.head, tuple(_shift(argument, delta, cutoff) for argument in term.args))
    if isinstance(term, Bound):
        return mk_bound(term.hint, _shift(term.body, delta, cutoff + 1))
    return term


def _abstract(term: Term, variable: Sym, depth: int) -> Term:
    if isinstance(term, Sym):
        return DB_(depth) if term is variable else term
    if isinstance(term, DB):
        return DB_(term.i + 1) if term.i >= depth else term
    if isinstance(term, Expr):
        return mk(term.head, tuple(_abstract(argument, variable, depth) for argument in term.args))
    if isinstance(term, Bound):
        return mk_bound(term.hint, _abstract(term.body, variable, depth + 1))
    return term


def mk_bound_canon(hint: str, canonical_body: Term) -> Bound:
    key = canonical_body._h
    term = _BOUNDS.get(key)
    if term is None:
        term = Bound(hint, canonical_body, _next_h())
        _BOUNDS[key] = term
    return term


def mk_bound(
    variable_hint: str | Sym,
    body: Term,
    variable: Sym | None = None,
) -> Bound:
    if variable is None:
        variable = S(variable_hint) if isinstance(variable_hint, str) else variable_hint
    hint = variable.name if isinstance(variable, Sym) else str(variable_hint)
    return mk_bound_canon(hint, _abstract(body, variable, 0))


def open_bound(bound: Bound) -> tuple[Sym, Term]:
    variable = S(bound.hint)
    return variable, lift(bound.body, variable, 0)


def lift(term: Term, variable: Sym, depth: int) -> Term:
    if isinstance(term, DB):
        return variable if term.i == depth else term
    if isinstance(term, Expr):
        args = tuple(lift(argument, variable, depth) for argument in term.args)
        return term if all(new is old for new, old in zip(args, term.args)) else mk(term.head, args)
    if isinstance(term, Bound):
        lifted_body = lift(term.body, variable, depth + 1)
        return (
            term
            if lifted_body is term.body
            else mk_bound_canon(term.hint, lifted_body)
        )
    return term
