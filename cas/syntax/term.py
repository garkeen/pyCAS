"""Pure syntax: immutable terms with structural identity and explicit binding.

The syntax layer knows no mathematics and no logic. It provides literals, symbol
references, bound variables, application, binders and quoted data, plus structural
equality, hash and a canonical order.

Rules:

- ``SymbolRef`` compares by ``symbol_id``; ``name`` is presentation only.
- ``BoundVar`` is a plain de Bruijn index. A ``Binder`` declares how many
  variables it introduces (``arity``), so binding checks never need a signature.
- ``Binder.hint`` is presentation only and takes no part in equality or order.
- Nothing is interned. Equal terms are not the same object, and that is fine
  because equality and hash are structural.
- No AC reordering and no simplification: operand order is the order the user
  wrote. Exchange laws belong to the algebra layer, which runs after typing.
"""

from __future__ import annotations

from fractions import Fraction

from cas.foundation.ids import SymbolId


class Term:
    """Base of the closed term hierarchy: immutable, structural, ordered."""

    __slots__ = ("_hash", "_key")

    _hash: int
    _key: tuple[object, ...]

    def __setattr__(self, name: str, value: object) -> None:
        # Every constructor publishes `_hash` last; until then the object is
        # still being built.
        try:
            object.__getattribute__(self, "_hash")
        except AttributeError:
            object.__setattr__(self, name, value)
            return
        raise AttributeError("terms are immutable")

    def __delattr__(self, name: str) -> None:
        raise AttributeError("terms are immutable")

    def __hash__(self) -> int:
        return self._hash

    def __eq__(self, other: object) -> bool:
        if self is other:
            return True
        if type(self) is not type(other):
            return NotImplemented
        return self._key == other._key

    def __lt__(self, other: Term) -> bool:
        return self._key < other._key

    def __repr__(self) -> str:
        return f"{type(self).__name__}()"


class IntLit(Term):
    """An exact integer literal."""

    __slots__ = ("value",)
    value: int

    def __init__(self, value: int) -> None:
        self.value = int(value)
        self._key = (0, self.value)
        self._hash = hash(self._key)

    def __repr__(self) -> str:
        return str(self.value)


class RatLit(Term):
    """An exact non-integral rational literal, always in lowest terms."""

    __slots__ = ("value",)
    value: Fraction

    def __init__(self, value: Fraction) -> None:
        fraction = Fraction(value)
        if fraction.denominator == 1:
            raise ValueError("an integral rational is an IntLit")
        self.value = fraction
        self._key = (1, fraction.numerator, fraction.denominator)
        self._hash = hash(self._key)

    def __repr__(self) -> str:
        return f"{self.value.numerator}/{self.value.denominator}"


class BoolLit(Term):
    """A boolean literal."""

    __slots__ = ("value",)
    value: bool

    def __init__(self, value: bool) -> None:
        self.value = bool(value)
        self._key = (2, 0 if self.value else 1)
        self._hash = hash(self._key)

    def __repr__(self) -> str:
        return "true" if self.value else "false"


class SymbolRef(Term):
    """A free symbol, identified by ``symbol_id``; ``name`` is display only."""

    __slots__ = ("symbol_id", "name")
    symbol_id: SymbolId
    name: str

    def __init__(self, symbol_id: SymbolId, name: str) -> None:
        if not name:
            raise ValueError("a symbol reference needs a display name")
        self.symbol_id = symbol_id
        self.name = name
        self._key = (3, int(symbol_id))
        self._hash = hash(self._key)

    def __repr__(self) -> str:
        return self.name


class BoundVar(Term):
    """A de Bruijn index: 0 is the innermost binder variable."""

    __slots__ = ("index",)
    index: int

    def __init__(self, index: int) -> None:
        if index < 0:
            raise ValueError("a de Bruijn index cannot be negative")
        self.index = index
        self._key = (4, index)
        self._hash = hash(self._key)

    def __repr__(self) -> str:
        return f"#{self.index}"


class Apply(Term):
    """Application: an operator term applied to arguments, order preserved."""

    __slots__ = ("operator", "arguments")
    operator: Term
    arguments: tuple[Term, ...]

    def __init__(self, operator: Term, arguments: tuple[Term, ...]) -> None:
        self.operator = operator
        self.arguments = tuple(arguments)
        self._key = (
            5,
            operator._key,
            tuple(argument._key for argument in self.arguments),
        )
        self._hash = hash(self._key)

    def __repr__(self) -> str:
        rendered = ", ".join(repr(argument) for argument in self.arguments)
        return f"{self.operator!r}({rendered})"


class Binder(Term):
    """A binding construct.

    ``signature`` names the binding form in the language layer, ``arity`` says
    how many variables it introduces, ``annotations`` are syntax terms evaluated
    in the *outer* context (for example integral bounds), and ``hint`` is a
    display name for the first bound variable only.
    """

    __slots__ = ("signature", "arity", "body", "annotations", "hint")
    signature: str
    arity: int
    body: Term
    annotations: tuple[Term, ...]
    hint: str

    def __init__(
        self,
        signature: str,
        arity: int,
        body: Term,
        annotations: tuple[Term, ...] = (),
        hint: str = "",
    ) -> None:
        if not signature:
            raise ValueError("a binder needs a signature name")
        if arity < 1:
            raise ValueError("a binder must introduce at least one variable")
        self.signature = signature
        self.arity = arity
        self.body = body
        self.annotations = tuple(annotations)
        self.hint = hint
        self._key = (
            6,
            signature,
            arity,
            body._key,
            tuple(annotation._key for annotation in self.annotations),
        )
        self._hash = hash(self._key)

    def __repr__(self) -> str:
        rendered = ", ".join(repr(annotation) for annotation in self.annotations)
        return f"{self.signature}[{self.hint}/{self.arity}; {rendered}]({self.body!r})"


class Quote(Term):
    """Held syntax data; no mathematical or binding meaning is assigned to it."""

    __slots__ = ("term",)
    term: Term

    def __init__(self, term: Term) -> None:
        self.term = term
        self._key = (7, term._key)
        self._hash = hash(self._key)

    def __repr__(self) -> str:
        return f"quote({self.term!r})"


TRUE = BoolLit(True)
FALSE = BoolLit(False)
ZERO = IntLit(0)
ONE = IntLit(1)


def number(value: int | Fraction) -> Term:
    """Build an exact literal: an IntLit when integral, a RatLit otherwise."""
    if isinstance(value, int):
        return IntLit(value)
    fraction = Fraction(value)
    if fraction.denominator == 1:
        return IntLit(fraction.numerator)
    return RatLit(fraction)


def symbol(symbol_id: SymbolId, name: str) -> SymbolRef:
    return SymbolRef(symbol_id, name)


def app(operator: Term, *arguments: Term) -> Apply:
    return Apply(operator, tuple(arguments))


def binder(
    signature: str,
    arity: int,
    body: Term,
    *annotations: Term,
    hint: str = "",
) -> Binder:
    return Binder(signature, arity, body, tuple(annotations), hint)


def quote(term: Term) -> Quote:
    return Quote(term)


__all__ = [
    "Apply",
    "Binder",
    "BoolLit",
    "BoundVar",
    "FALSE",
    "IntLit",
    "ONE",
    "Quote",
    "RatLit",
    "SymbolRef",
    "TRUE",
    "Term",
    "ZERO",
    "app",
    "binder",
    "number",
    "quote",
    "symbol",
]
