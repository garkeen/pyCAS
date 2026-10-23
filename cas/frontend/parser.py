"""Surface parsing: text to pure terms with stable symbol ids.

The parser knows only the language's structural signature plus a small surface
vocabulary: infix arithmetic, comparisons, boolean operators, `true`/`false`
and `quote(...)`. It assigns no mathematical meaning and performs no
simplification; `1 + 1` stays an application of `Plus`.

The one folding it does is lexical: a signed numeric literal and a quotient of
two numeric literals are read as one exact literal (`-1/2` is a rational
literal). Everything else is preserved as written, including operand order.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction

from cas.foundation.ids import SymbolId
from cas.frontend.errors import ParseError
from cas.language.signatures import LanguageSignature, StructuralHead
from cas.semantics.symbols import SymbolTable
from cas.syntax import term as T

_COMPARISONS: dict[str, StructuralHead] = {
    "==": StructuralHead.EQ,
    "=": StructuralHead.EQ,
    "!=": StructuralHead.NE,
    "<": StructuralHead.LT,
    "<=": StructuralHead.LE,
    ">": StructuralHead.GT,
    ">=": StructuralHead.GE,
}
_RESERVED = frozenset({"and", "or", "not"})
_TWO_CHARACTER = frozenset({"==", "!=", "<=", ">=", "=>", "->"})
_ONE_CHARACTER = frozenset("+-*/^(),=<>")


@dataclass(frozen=True, slots=True)
class _Token:
    kind: str
    value: str
    position: int


def _tokenize(text: str) -> tuple[_Token, ...]:
    tokens: list[_Token] = []
    index = 0
    while index < len(text):
        character = text[index]
        if character.isspace():
            index += 1
            continue
        if character.isdigit():
            start = index
            while index < len(text) and text[index].isdigit():
                index += 1
            tokens.append(_Token("number", text[start:index], start))
            continue
        if character.isalpha() or character == "_":
            start = index
            index += 1
            while index < len(text) and (
                text[index].isalnum() or text[index] == "_"
            ):
                index += 1
            tokens.append(_Token("name", text[start:index], start))
            continue
        pair = text[index : index + 2]
        if pair in _TWO_CHARACTER:
            tokens.append(_Token("symbol", pair, index))
            index += 2
            continue
        if character in _ONE_CHARACTER:
            tokens.append(_Token("symbol", character, index))
            index += 1
            continue
        raise ParseError(f"unexpected character {character!r}", index, text)
    tokens.append(_Token("end", "", len(text)))
    return tuple(tokens)


class _Parser:
    __slots__ = ("_index", "_signature", "_table", "_text", "_tokens")

    def __init__(
        self,
        tokens: tuple[_Token, ...],
        table: SymbolTable,
        signature: LanguageSignature,
        text: str,
    ) -> None:
        self._tokens = tokens
        self._index = 0
        self._table = table
        self._signature = signature
        self._text = text

    # --- token helpers ---

    def _peek(self) -> _Token:
        return self._tokens[self._index]

    def _advance(self) -> _Token:
        token = self._tokens[self._index]
        self._index += 1
        return token

    def _at(self, value: str) -> bool:
        return self._peek().value == value

    def _expect(self, value: str) -> _Token:
        token = self._peek()
        if token.value != value:
            raise ParseError(
                f"expected {value!r}, got {token.value!r}",
                token.position,
                self._text,
            )
        return self._advance()

    def _head(self, head: StructuralHead) -> SymbolId:
        identifier = self._signature.symbol_of(head)
        if identifier is None:
            raise ParseError(
                f"the language has no symbol for {head.value}",
                self._peek().position,
                self._text,
            )
        return identifier

    def _applied(self, head: StructuralHead, *arguments: T.Term) -> T.Apply:
        return T.app(
            T.symbol(self._head(head), head.value), *arguments
        )

    # --- grammar ---

    def parse(self) -> T.Term:
        term = self._implication()
        token = self._peek()
        if token.kind != "end":
            raise ParseError(
                f"unexpected token {token.value!r}",
                token.position,
                self._text,
            )
        return term

    def _implication(self) -> T.Term:
        left = self._or()
        if self._at("=>") or self._at("->"):
            self._advance()
            return self._applied(
                StructuralHead.IMPLIES, left, self._implication()
            )
        return left

    def _or(self) -> T.Term:
        parts = [self._and()]
        while self._at("or"):
            self._advance()
            parts.append(self._and())
        return parts[0] if len(parts) == 1 else self._applied(
            StructuralHead.OR, *parts
        )

    def _and(self) -> T.Term:
        parts = [self._not()]
        while self._at("and"):
            self._advance()
            parts.append(self._not())
        return parts[0] if len(parts) == 1 else self._applied(
            StructuralHead.AND, *parts
        )

    def _not(self) -> T.Term:
        if self._at("not"):
            self._advance()
            return self._applied(StructuralHead.NOT, self._not())
        return self._comparison()

    def _comparison(self) -> T.Term:
        left = self._sum()
        head = _COMPARISONS.get(self._peek().value)
        if head is None:
            return left
        self._advance()
        right = self._sum()
        if self._peek().value in _COMPARISONS:
            raise ParseError(
                "a chained comparison is not one formula; combine them with and",
                self._peek().position,
                self._text,
            )
        return self._applied(head, left, right)

    def _sum(self) -> T.Term:
        terms = [self._product()]
        while self._at("+") or self._at("-"):
            operator = self._advance().value
            right = self._product()
            terms.append(right if operator == "+" else self._negate(right))
        return terms[0] if len(terms) == 1 else self._applied(
            StructuralHead.PLUS, *terms
        )

    def _product(self) -> T.Term:
        factors = [self._unary()]
        while self._at("*") or self._at("/"):
            operator = self._advance().value
            right = self._unary()
            if operator == "*":
                factors.append(right)
            elif len(factors) == 1:
                factors = [self._divide(factors[0], right)]
            else:
                factors.append(self._reciprocal(right))
        return factors[0] if len(factors) == 1 else self._applied(
            StructuralHead.TIMES, *factors
        )

    def _unary(self) -> T.Term:
        if self._at("-"):
            self._advance()
            return self._negate(self._unary())
        if self._at("+"):
            self._advance()
            return self._unary()
        return self._power()

    def _power(self) -> T.Term:
        base = self._atom()
        if self._at("^"):
            self._advance()
            return self._applied(
                StructuralHead.POWER, base, self._unary()
            )
        return base

    def _atom(self) -> T.Term:
        token = self._peek()
        if token.kind == "number":
            self._advance()
            return T.number(int(token.value))
        if token.kind == "name":
            self._advance()
            if token.value == "true":
                return T.TRUE
            if token.value == "false":
                return T.FALSE
            if token.value in _RESERVED:
                raise ParseError(
                    f"{token.value!r} is an operator, not an expression",
                    token.position,
                    self._text,
                )
            if self._at("("):
                return self._call(token)
            identifier = self._table.intern(token.value)
            return T.symbol(identifier, token.value)
        if self._at("("):
            self._advance()
            term = self._implication()
            self._expect(")")
            return term
        raise ParseError("expected an expression", token.position, self._text)

    def _call(self, name: _Token) -> T.Term:
        self._expect("(")
        arguments: list[T.Term] = []
        if not self._at(")"):
            arguments.append(self._implication())
            while self._at(","):
                self._advance()
                arguments.append(self._implication())
        self._expect(")")
        if self._is_quote(name.value):
            if len(arguments) != 1:
                raise ParseError(
                    "quote takes exactly one argument",
                    name.position,
                    self._text,
                )
            return T.quote(arguments[0])
        identifier = self._table.intern(name.value)
        return T.app(
            T.symbol(identifier, name.value), *arguments
        )

    def _is_quote(self, name: str) -> bool:
        # `quote(...)` builds the held-data term; `Quote(...)` is the ordinary
        # structural application and therefore keeps its head in the term.
        return name == "quote"

    # --- literal helpers ---

    def _negate(self, term: T.Term) -> T.Term:
        if isinstance(term, T.IntLit):
            return T.number(-term.value)
        if isinstance(term, T.RatLit):
            return T.number(-term.value)
        return self._applied(StructuralHead.TIMES, T.number(-1), term)

    def _reciprocal(self, term: T.Term) -> T.Term:
        return self._applied(
            StructuralHead.POWER, term, T.number(-1)
        )

    def _divide(self, left: T.Term, right: T.Term) -> T.Term:
        if (
            isinstance(left, (T.IntLit, T.RatLit))
            and isinstance(right, (T.IntLit, T.RatLit))
            and right.value != 0
        ):
            return T.number(Fraction(left.value) / Fraction(right.value))
        return self._applied(
            StructuralHead.TIMES, left, self._reciprocal(right)
        )


def parse(
    text: str,
    table: SymbolTable,
    signature: LanguageSignature,
) -> T.Term:
    """Parse `text` into a term, resolving names through `table`.

    Unknown names are interned so that they keep one stable identity; whether a
    name is declared is a later semantic question.
    """
    tokens = _tokenize(text)
    return _Parser(tokens, table, signature, text).parse()


__all__ = ["ParseError", "parse"]
