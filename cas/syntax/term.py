"""Interned pure-syntax terms and their structural constructors."""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from functools import partial
from typing import Iterable, TypeGuard


@dataclass(frozen=True, order=True, slots=True)
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
    """A pure-syntax, interned value.

    `_key` is the term's position in the canonical order. It is computed once
    at construction from the already-built keys of the children, so ordering
    never re-derives a key tree: comparing two terms reads two existing
    objects. The canonical order itself is unchanged; only the cost of
    obtaining it moved from "every comparison" to "every construction".

    `_sh` is the term's structural hash and `_h` its unique serial. They are
    kept apart on purpose: the hash and the order are properties of a term's
    shape, while the serial names one particular object, which is what the
    intern tables and the union-find index by.

    Equality is structural, with the identity test first. The intern tables
    make structurally equal terms the same object, so the fast path is the
    overwhelmingly common one; the structural comparison is what keeps the
    meaning of `==` correct for a term that was built outside them (a
    reconstructed node, a term crossing a process boundary, a duplicate that
    interning could not merge). `hash` is the matching structural hash, so the
    hash/equality contract holds for equal terms whether or not they are the
    same object.
    """

    __slots__ = ("_h", "_key", "_sh")
    _h: int
    _key: SortKey
    _sh: int

    def __hash__(self) -> int:
        return self._sh

    def __lt__(self, other: Term) -> bool:
        return self._key < other._key


class Sym(Term):
    __slots__ = ("name",)
    name: str

    def __init__(self, name: str) -> None:
        self.name = name
        self._key = SortKey(0, name)
        self._sh = hash((0, name))
        self._h = _next_h()

    def __eq__(self, other: object) -> bool:
        if self is other:
            return True
        if not isinstance(other, Sym):
            return NotImplemented
        return self.name == other.name

    __hash__ = Term.__hash__

    def __repr__(self) -> str:
        return self.name


class Const(Term):
    __slots__ = ("name",)
    name: str

    def __init__(self, name: str) -> None:
        self.name = name
        self._key = SortKey(1, name)
        self._sh = hash((1, name))
        self._h = _next_h()

    def __eq__(self, other: object) -> bool:
        if self is other:
            return True
        if not isinstance(other, Const):
            return NotImplemented
        return self.name == other.name

    __hash__ = Term.__hash__

    def __repr__(self) -> str:
        return self.name


class DB(Term):
    __slots__ = ("i",)
    i: int

    def __init__(self, i: int) -> None:
        self.i = i
        self._key = SortKey(3, number=i)
        self._sh = hash((2, i))
        self._h = _next_h()

    def __eq__(self, other: object) -> bool:
        if self is other:
            return True
        if not isinstance(other, DB):
            return NotImplemented
        return self.i == other.i

    __hash__ = Term.__hash__

    def __repr__(self) -> str:
        return f"#{self.i}"


class BVal(Term):
    __slots__ = ("val",)
    val: bool

    def __init__(self, val: bool) -> None:
        self.val = val
        self._key = SortKey(2, number=0 if val else 1)
        self._sh = hash((3, val))
        self._h = _next_h()

    def __eq__(self, other: object) -> bool:
        if self is other:
            return True
        if not isinstance(other, BVal):
            return NotImplemented
        return self.val == other.val

    __hash__ = Term.__hash__

    def __repr__(self) -> str:
        return "True" if self.val else "False"


class Int(Term):
    __slots__ = ("v",)
    v: int

    def __init__(self, value: int) -> None:
        self.v = value
        self._key = SortKey(25, number=value)
        self._sh = hash((4, value))
        self._h = _next_h()

    def __eq__(self, other: object) -> bool:
        if self is other:
            return True
        if not isinstance(other, Int):
            return NotImplemented
        return self.v == other.v

    __hash__ = Term.__hash__

    def __repr__(self) -> str:
        return str(self.v)


class Rat(Term):
    __slots__ = ("f",)
    f: Fraction

    def __init__(self, value: Fraction) -> None:
        self.f = value
        self._key = SortKey(25, number=value)
        self._sh = hash((5, value))
        self._h = _next_h()

    def __eq__(self, other: object) -> bool:
        if self is other:
            return True
        if not isinstance(other, Rat):
            return NotImplemented
        return self.f == other.f

    __hash__ = Term.__hash__

    def __repr__(self) -> str:
        return f"{self.f.numerator}/{self.f.denominator}"


class Special(Term):
    __slots__ = ("name",)
    name: str

    def __init__(self, name: str) -> None:
        self.name = name
        self._key = SortKey(8, name)
        self._sh = hash((6, name))
        self._h = _next_h()

    def __eq__(self, other: object) -> bool:
        if self is other:
            return True
        if not isinstance(other, Special):
            return NotImplemented
        return self.name == other.name

    __hash__ = Term.__hash__

    def __repr__(self) -> str:
        return self.name


class Expr(Term):
    __slots__ = ("head", "args")
    head: Sym
    args: tuple[Term, ...]

    def __init__(self, head: Sym, args: tuple[Term, ...], value_hash: int) -> None:
        self.head = head
        self.args = args
        # Children are already constructed, so their keys and hashes are
        # already built: this is linear in the arity, not in the subtree.
        self._key = SortKey(
            20,
            children=(head._key, *(argument._key for argument in args)),
        )
        self._sh = hash((7, head._sh, tuple(argument._sh for argument in args)))
        self._h = value_hash

    def __eq__(self, other: object) -> bool:
        if self is other:
            return True
        if not isinstance(other, Expr):
            return NotImplemented
        return self.head == other.head and self.args == other.args

    __hash__ = Term.__hash__

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
        self._key = SortKey(21, children=(body._key,))
        self._sh = hash((8, body._sh))
        self._h = value_hash

    def __eq__(self, other: object) -> bool:
        if self is other:
            return True
        if not isinstance(other, Bound):
            return NotImplemented
        # `hint` is a display-only name for the bound variable; the de Bruijn
        # body is what carries the meaning, and `mk_bound_canon` interns a body
        # to one hint, so comparing the body alone is both sufficient and
        # consistent with what the table already merged.
        return self.body == other.body

    __hash__ = Term.__hash__

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

# Interning tables.
#
# Only the finite vocabulary is interned: symbols, constants, declared specials
# and de Bruijn indices. Those sets are bounded by the program's own vocabulary
# (the declarations DSL and the variables the user has typed), so they cannot
# grow without limit and sharing them is free.
#
# Expression nodes are NOT interned, and neither are numeric literals. Both
# used to be, and the reason is worth recording. Expression interning: `Term.__eq__`
# was pointer identity, so a dictionary keyed by a term only collapsed equal
# terms while the table held them, and dropping an entry silently split one
# expression into two dictionary keys. Numeric interning: a table keyed by value
# has a key space decided by the computation rather than by the program's
# declarations, so it grows with every distinct rational a run ever forms -
# 200k distinct rationals meant 200k permanently held literals. Equality and the
# hash are now both structural, which removes the correctness dependency
# entirely, so neither table buys anything but sharing, and an unbounded table
# costs more than that sharing is worth. `N` therefore builds a fresh literal
# and equal literals still collapse to one dictionary slot.
#
# Sharing is still real where it matters, because a subtree that is not rebuilt
# keeps its object: `lift` and the binder walks return the original child when
# the child is unchanged, so the identity fast path in `__eq__` fires and a
# rebuild allocates only the nodes it actually changed.
_SYMS: dict[str, Sym] = {}
_CONSTS: dict[str, Const] = {}
_SPECIALS: dict[str, Special] = {}
_DBS: dict[int, DB] = {}


def clear_interning() -> None:
    """Drop every interned vocabulary atom. Terms built from them stay valid.

    Only the finite tables are cleared; expression nodes and numeric literals
    are not tracked, so there is nothing to release for them.
    """
    _SYMS.clear()
    _CONSTS.clear()
    _SPECIALS.clear()
    _DBS.clear()


def interning_size() -> int:
    """Number of interned vocabulary atoms, for budget reporting."""
    return len(_SYMS) + len(_CONSTS) + len(_SPECIALS) + len(_DBS)


def DB_(index: int) -> DB:
    term = _DBS.get(index)
    if term is None:
        term = DB(index)
        _DBS[index] = term
    return term


TRUE = BVal(True)
FALSE = BVal(False)
UNDEFINED = _SPECIALS.setdefault("Undefined", Special("Undefined"))
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
    """Build a numeric literal. Deliberately not interned: see the table notes."""
    if isinstance(value, int):
        return Int(value)
    fraction = Fraction(value)
    if fraction.denominator == 1:
        return N(fraction.numerator)
    return Rat(fraction)


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
    """The term's position in the canonical order.

    The key is built once at construction (`Term._key`), so this is a field
    read. It stays a function because callers - the pattern layer in
    particular - treat it as the accessor for a term's canonical key.
    """
    return term._key


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
    """Build a call node. The name records the historical role; it no longer
    consults a table.

    Equality is structural and the hash is structural, so the constructor no
    longer has to make equal terms the same object for dictionaries, sets and
    `==` to behave. What it still buys is *sharing*, not correctness: the node
    is built once and every holder of it observes the same object, so the
    identity fast path in `__eq__` and the `is` checks in `lift` and friends
    keep firing on the unchanged parts of a tree. That sharing is what stops
    a rebuild from allocating a fresh object per node.
    """
    return Expr(head, args, _next_h())


def mk(head: Sym, args: Iterable[Term]) -> Term:
    arguments = tuple(args)
    name = head.name
    if name in AC:
        if name in BOOL_HEADS:
            folded = _fold_bool_ac(head, arguments)
            if isinstance(folded, list):
                return Expr(head, tuple(folded), _next_h())
            return folded
        return Expr(head, tuple(_flatten_ac(head, arguments)), _next_h())
    return Expr(head, arguments, _next_h())


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
    """Bind a canonical (already abstracted) body under a display name.

    Equality ignores `hint` and the hash ignores it too, so two bindings of
    the same body with different names compare equal; the table that used to
    collapse them is gone and no longer needed for that.
    """
    return Bound(hint, canonical_body, _next_h())


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
        # Share the unchanged children. This is what keeps a rebuild from
        # allocating a fresh node per subtree, and it is what makes the identity
        # fast path in `Term.__eq__` fire on the parts that did not change. The
        # test is `is`, and that is sound here precisely because `lift` returns
        # its input object for every leaf and for an unchanged child list, so
        # `new is old` is a real "nothing happened" signal rather than a guess.
        return (
            term
            if all(new is old for new, old in zip(args, term.args))
            else mk(term.head, args)
        )
    if isinstance(term, Bound):
        lifted_body = lift(term.body, variable, depth + 1)
        return (
            term
            if lifted_body is term.body
            else mk_bound_canon(term.hint, lifted_body)
        )
    return term
