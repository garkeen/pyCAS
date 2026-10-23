"""Rendering terms as readable text and as reparsable source.

`to_str` is the readable form used by the session. `to_source` writes every
application in fully applied form, so parsing it returns the same term for terms
whose applications use symbol operators and which contain no binders or free
bound variables. Binders have no surface source syntax yet, and the other two
cases are refused instead of emitting text that cannot be read back.

Rendering is presentation only: it never reorders operands, simplifies or
chooses a mathematical meaning. Structural heads come from the signature; other
operators are printed by their display name.
"""

from __future__ import annotations

from collections.abc import Iterator

from cas.language.signatures import LanguageSignature, StructuralHead
from cas.syntax import term as T

_IMPLIES = 1
_OR = 2
_AND = 3
_NOT = 4
_COMPARISON = 5
_PLUS = 6
_TIMES = 7
_POWER = 9
_ATOM = 10

_COMPARISON_TEXT = {
    StructuralHead.EQ: "==",
    StructuralHead.NE: "!=",
    StructuralHead.LT: "<",
    StructuralHead.LE: "<=",
    StructuralHead.GT: ">",
    StructuralHead.GE: ">=",
}

_Rendered = tuple[str, int]


def _wrap(text: str, precedence: int, minimum: int) -> str:
    return "(" + text + ")" if precedence < minimum else text


class _Printer:
    __slots__ = ("_signature", "_source")

    def __init__(self, signature: LanguageSignature, source: bool) -> None:
        self._signature = signature
        self._source = source

    def text(self, term: T.Term) -> str:
        return self.term(term)[0]

    def term(self, term: T.Term) -> _Rendered:
        if isinstance(term, T.IntLit):
            return str(term.value), _ATOM
        if isinstance(term, T.RatLit):
            return (
                f"{term.value.numerator}/{term.value.denominator}",
                _ATOM,
            )
        if isinstance(term, T.BoolLit):
            return ("true" if term.value else "false"), _ATOM
        if isinstance(term, T.SymbolRef):
            return term.name, _ATOM
        if isinstance(term, T.BoundVar):
            if self._source:
                raise ValueError("a free bound variable has no source form")
            return f"#{term.index}", _ATOM
        if isinstance(term, T.Quote):
            return "quote(" + self.text(term.term) + ")", _ATOM
        if isinstance(term, T.Binder):
            return self._binder(term)
        if isinstance(term, T.Apply):
            return self._application(term)
        raise TypeError(f"unsupported term variant: {type(term).__name__}")

    # --- binding ---

    def _binder(self, term: T.Binder) -> _Rendered:
        if self._source:
            raise ValueError("a binder has no surface source form yet")
        hint = term.hint or "_"
        parts = [self.text(term.body)]
        parts.extend(self.text(annotation) for annotation in term.annotations)
        return (
            f"{term.signature}[{hint}/{term.arity}]({', '.join(parts)})",
            _ATOM,
        )

    # --- application ---

    def _application(self, term: T.Apply) -> _Rendered:
        head = None
        if isinstance(term.operator, T.SymbolRef):
            head = self._signature.head_of(term.operator.symbol_id)
        if self._source or head is None:
            return self._call(term)
        if head is StructuralHead.PLUS:
            return self._plus(term)
        if head is StructuralHead.TIMES:
            return self._times(term)
        if head is StructuralHead.POWER:
            return self._power(term)
        if head in _COMPARISON_TEXT:
            return self._comparison(head, term)
        if head is StructuralHead.AND:
            return self._junction(term, " and ", _AND)
        if head is StructuralHead.OR:
            return self._junction(term, " or ", _OR)
        if head is StructuralHead.NOT:
            return self._not(term)
        if head is StructuralHead.IMPLIES:
            return self._implies(term)
        return self._call(term)

    def _call(self, term: T.Apply) -> _Rendered:
        if isinstance(term.operator, T.SymbolRef):
            name = term.operator.name
        elif self._source:
            raise ValueError("an applied operator needs a symbol for a source form")
        else:
            text, precedence = self.term(term.operator)
            name = _wrap(text, precedence, _ATOM)
        arguments = ", ".join(
            self.text(argument) for argument in term.arguments
        )
        return f"{name}({arguments})", _ATOM

    def _plus(self, term: T.Apply) -> _Rendered:
        if len(term.arguments) < 2:
            return self._call(term)
        parts: list[str] = []
        for index, argument in enumerate(term.arguments):
            text, precedence = self.term(argument)
            text = _wrap(text, precedence, _PLUS)
            if index == 0:
                parts.append(text)
            elif text.startswith("-"):
                parts.append("- " + text[1:])
            else:
                parts.append("+ " + text)
        return " ".join(parts), _PLUS

    def _factors(self, term: T.Apply) -> Iterator[T.Term]:
        """Flatten nested products for display; multiplication is associative."""
        for argument in term.arguments:
            nested = None
            if isinstance(argument, T.Apply) and isinstance(
                argument.operator, T.SymbolRef
            ):
                nested = self._signature.head_of(argument.operator.symbol_id)
            if nested is StructuralHead.TIMES:
                assert isinstance(argument, T.Apply)
                yield from self._factors(argument)
            else:
                yield argument

    def _times(self, term: T.Apply) -> _Rendered:
        if len(term.arguments) < 2:
            return self._call(term)
        arguments = tuple(self._factors(term))
        first = arguments[0]
        negative_one = isinstance(first, T.IntLit) and first.value == -1
        start = 1 if negative_one else 0
        remaining = len(arguments) - start
        minimum = _TIMES if negative_one else _TIMES + 1
        parts: list[str] = []
        for argument in arguments[start:]:
            if (
                isinstance(argument, T.IntLit)
                and argument.value == 1
                and remaining > 1
            ):
                continue
            text, precedence = self.term(argument)
            parts.append(_wrap(text, precedence, minimum))
        body = "*".join(parts) if parts else "1"
        if negative_one:
            body = "-" + body
        return body, _TIMES

    def _power(self, term: T.Apply) -> _Rendered:
        if len(term.arguments) != 2:
            return self._call(term)
        base, exponent = term.arguments
        base_text, base_precedence = self.term(base)
        base_text = _wrap(base_text, base_precedence, _POWER + 1)
        if isinstance(base, T.RatLit) or (
            isinstance(base, T.IntLit) and base.value < 0
        ):
            base_text = "(" + base_text + ")"
        exponent_text, exponent_precedence = self.term(exponent)
        exponent_text = _wrap(
            exponent_text, exponent_precedence, _POWER
        )
        return f"{base_text}^{exponent_text}", _POWER

    def _comparison(
        self, head: StructuralHead, term: T.Apply
    ) -> _Rendered:
        if len(term.arguments) != 2:
            return self._call(term)
        left_text, left_precedence = self.term(term.arguments[0])
        right_text, right_precedence = self.term(term.arguments[1])
        left = _wrap(left_text, left_precedence, _COMPARISON + 1)
        right = _wrap(right_text, right_precedence, _COMPARISON + 1)
        return f"{left} {_COMPARISON_TEXT[head]} {right}", _COMPARISON

    def _junction(
        self, term: T.Apply, separator: str, precedence: int
    ) -> _Rendered:
        if len(term.arguments) < 2:
            return self._call(term)
        parts = [
            _wrap(*self.term(argument), precedence)
            for argument in term.arguments
        ]
        return separator.join(parts), precedence

    def _not(self, term: T.Apply) -> _Rendered:
        if len(term.arguments) != 1:
            return self._call(term)
        text, precedence = self.term(term.arguments[0])
        return "not " + _wrap(text, precedence, _NOT), _NOT

    def _implies(self, term: T.Apply) -> _Rendered:
        if len(term.arguments) != 2:
            return self._call(term)
        left_text, left_precedence = self.term(term.arguments[0])
        right_text, right_precedence = self.term(term.arguments[1])
        left = _wrap(left_text, left_precedence, _IMPLIES + 1)
        right = _wrap(right_text, right_precedence, _IMPLIES)
        return f"{left} => {right}", _IMPLIES


def to_str(term: T.Term, signature: LanguageSignature) -> str:
    """The readable surface form of `term`."""
    return _Printer(signature, False).text(term)


def to_source(term: T.Term, signature: LanguageSignature) -> str:
    """A fully applied source form; binders are refused."""
    return _Printer(signature, True).text(term)


__all__ = ["to_source", "to_str"]
