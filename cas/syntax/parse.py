"""Expression parser for the term language and its pattern channel."""

from __future__ import annotations

import re
from collections.abc import Callable, Iterable, Mapping
from fractions import Fraction
from typing import Generic, Literal, TypeAlias, TypeVar, cast, overload

from cas.errors import ParseError
from cas.syntax import pattern as P
from cas.syntax import term as T
from cas.syntax.term import FALSE, INFINITY, TRUE, N, S

Token: TypeAlias = tuple[str, str]
ParseValue: TypeAlias = T.Term | P.Pattern
ConstantTable: TypeAlias = Mapping[str, T.Term]
AliasResolver: TypeAlias = Callable[[str], str | None]
ConstantResolver: TypeAlias = Callable[[str], T.Term | None]
BinderResolver: TypeAlias = Callable[[str], bool]

ValueT = TypeVar("ValueT", bound=ParseValue)

_TOKEN = re.compile(
    r"\s*(?:"
    r"(?P<num>\d+\.\d+|\d+)"
    r"|(?P<seq>\?\?[_A-Za-z]\w*)"
    r"|(?P<pvar>\?[_A-Za-z]\w*(?:::[_A-Za-z]\w*)?)"
    r"|(?P<db>@\d+)"
    r"|(?P<id>[A-Za-z_]\w*)"
    r"|(?P<op>&&|\|\||==|!=|<=|>=|->|[-+*/^()<>,='])"
    + r")"
)
_SYNTAX_ATOMS: dict[str, T.Term] = {
    "infinity": INFINITY,
    "true": TRUE,
    "false": FALSE,
}
_PREC: dict[str, int] = {
    "=": 1,
    "==": 2,
    "!=": 2,
    "<": 2,
    ">": 2,
    "<=": 2,
    ">=": 2,
    "+": 3,
    "-": 3,
    "*": 4,
    "/": 4,
    "^": 6,
}
_HEADMAP: dict[str, str] = {
    "==": "Eq",
    "!=": "Ne",
    "<": "Lt",
    ">": "Gt",
    "<=": "Le",
    ">=": "Ge",
    "+": "Plus",
    "-": "Plus",
    "*": "Times",
    "/": "Times",
    "^": "Power",
}



def tokenize(text: str) -> list[Token]:
    """Tokenize source text, preserving the surface grammar."""
    tokens: list[Token] = []
    index = 0
    while index < len(text):
        match = _TOKEN.match(text, index)
        if match is None:
            if text[index].isspace():
                index += 1
                continue
            raise ParseError(f"bad char {text[index]!r} at {index}")
        index = match.end()
        kind = match.lastgroup
        if kind is None:
            raise ParseError(f"token has no group at {index}")
        value = match.group(kind)
        if value is None:
            raise ParseError(f"token has no value at {index}")
        tokens.append((kind, value))
    tokens.append(("end", ""))
    return tokens


class Parser(Generic[ValueT]):
    """Parser whose construction channel is fixed at runtime."""

    def __init__(
        self,
        tokens: list[Token],
        *,
        raw: bool = False,
        pattern: bool = False,
        constants: ConstantTable | None = None,
        alias_fn: AliasResolver | None = None,
        const_fn: ConstantResolver | None = None,
        binder_fn: BinderResolver | None = None,
    ) -> None:
        self.tokens = tokens
        self.index = 0
        self.raw = raw
        self.pattern = pattern
        self.constants = constants
        self._alias_fn = alias_fn
        self._const_fn = const_fn
        self._binder_fn = binder_fn

    def _alias(self, name: str) -> str:
        if self.constants is not None:
            return name
        if self._alias_fn is not None:
            resolved = self._alias_fn(name)
            return resolved if resolved is not None else name
        return name

    def _is_binder(self, head: str) -> bool:
        return self._binder_fn is not None and self._binder_fn(head)

    def _const_atom(self, name: str) -> T.Term | None:
        if self.constants is not None:
            return self.constants.get(name)
        if self._const_fn is not None:
            return self._const_fn(name)
        return None

    def _mk(self, head: T.Sym, args: Iterable[ParseValue]) -> ValueT:
        arguments = tuple(args)
        if self.pattern:
            return cast(ValueT, P.pcall(head, arguments))
        terms = tuple(cast(T.Term, argument) for argument in arguments)
        if self.raw:
            return cast(ValueT, T.intern_expr(head, terms))
        return cast(ValueT, T.mk(head, terms))

    def _neg(self, value: ParseValue) -> ValueT:
        if self.pattern:
            return cast(ValueT, P.pcall(S("Times"), (T.MONE, value)))
        term = cast(T.Term, value)
        if self.raw:
            return cast(ValueT, T.intern_expr(S("Times"), (T.MONE, term)))
        return cast(ValueT, T.neg(term))

    def _quote(self, value: ParseValue) -> ValueT:
        if self.pattern:
            return cast(ValueT, P.pcall(S("Quote"), (value,)))
        return cast(ValueT, T.quote(cast(T.Term, value)))

    def _recip(self, value: ParseValue) -> ValueT:
        return self._mk(S("Power"), (value, T.MONE))

    def peek(self) -> Token:
        return self.tokens[self.index]

    def next(self) -> Token:
        token = self.tokens[self.index]
        self.index += 1
        return token

    def expect(self, value: str) -> None:
        _kind, actual = self.next()
        if actual != value:
            raise ParseError(f"expected {value!r}, got {actual!r}")

    def parse(self) -> ValueT:
        result = self.expr(0)
        kind, value = self.peek()
        if kind != "end":
            raise ParseError(f"unexpected {value!r}")
        return result

    def expr(self, minimum_precedence: int) -> ValueT:
        left = self.unary()
        while True:
            kind, value = self.peek()
            operator: str | None = None
            logic_precedence = 0
            if kind == "id" and value == "and":
                operator, logic_precedence = "&&", 1
            elif kind == "id" and value == "or":
                operator, logic_precedence = "||", 1
            elif kind == "op" and value in ("&&", "||"):
                operator, logic_precedence = value, 1
            if operator is not None:
                if logic_precedence < minimum_precedence:
                    break
                self.next()
                right = self.expr(logic_precedence + 1)
                head = S("And") if operator == "&&" else S("Or")
                left = self._mk(head, (left, right))
                continue
            precedence = _PREC.get(value)
            if precedence is None or precedence < minimum_precedence:
                break
            self.next()
            operation = "==" if value == "=" else value
            right = self.expr(precedence if operation == "^" else precedence + 1)
            head_name = _HEADMAP[operation]
            if operation == "-":
                right = self._neg(right)
            elif operation == "/":
                right = self._recip(right)
            left = self._mk(S(head_name), (left, right))
        return left

    def unary(self) -> ValueT:
        kind, value = self.peek()
        if kind == "op" and value == "-":
            self.next()
            expression = self.unary()
            if self.peek() == ("op", "^"):
                self.next()
                right = self.expr(_PREC["^"])
                expression = self._mk(S("Power"), (expression, right))
            return self._neg(expression)
        if kind == "op" and value == "'":
            self.next()
            old_raw, self.raw = self.raw, True
            try:
                return self._quote(self.expr(1))
            finally:
                self.raw = old_raw
        if kind == "op" and value == "(":
            self.next()
            expression = self.expr(0)
            self.expect(")")
            return expression
        if kind == "db":
            self.next()
            return cast(ValueT, T.DB_(int(value[1:])))
        if kind == "num":
            self.next()
            return cast(ValueT, N(Fraction(value)))
        if kind == "seq":
            self.next()
            if not self.pattern:
                raise ParseError(f"pattern hole {value!r} outside pattern context")
            return cast(ValueT, P.PS(value[2:]))
        if kind == "pvar":
            self.next()
            if not self.pattern:
                raise ParseError(f"pattern hole {value!r} outside pattern context")
            body = value[1:]
            if "::" in body:
                name, predicate = body.split("::", 1)
                return cast(ValueT, P.PV(name, predicate))
            return cast(ValueT, P.PV(body))
        if kind == "id":
            self.next()
            if value in _SYNTAX_ATOMS:
                return cast(ValueT, _SYNTAX_ATOMS[value])
            atom = self._const_atom(value)
            if atom is not None:
                return cast(ValueT, atom)
            canonical = self._alias(value)
            next_kind, next_value = self.peek()
            if next_kind == "op" and next_value == "(":
                self.next()
                args: list[ParseValue] = []
                if self.peek() != ("op", ")"):
                    args.append(self.expr(0))
                    while self.peek() == ("op", ","):
                        self.next()
                        args.append(self.expr(0))
                self.expect(")")
                if self._is_binder(canonical) and len(args) >= 2:
                    if self.pattern and P.has_holes(args[1]):
                        raise ParseError(
                            "binder pattern with a hole in variable position is not supported"
                        )
                    if not isinstance(args[0], T.Term) or not isinstance(args[1], T.Sym):
                        raise ParseError("binder arguments must be a term and a symbol")
                    bound = T.mk_bound(args[1], args[0])
                    return self._mk(S(canonical), (bound, *args[2:]))
                return self._mk(S(canonical), tuple(args))
            return cast(ValueT, S(canonical))
        raise ParseError(f"unexpected {value!r}")


@overload
def parse(
    text: str,
    pattern: Literal[False] = False,
    constants: ConstantTable | None = None,
    alias_fn: AliasResolver | None = None,
    const_fn: ConstantResolver | None = None,
    binder_fn: BinderResolver | None = None,
) -> T.Term: ...


@overload
def parse(
    text: str,
    pattern: Literal[True],
    constants: ConstantTable | None = None,
    alias_fn: AliasResolver | None = None,
    const_fn: ConstantResolver | None = None,
    binder_fn: BinderResolver | None = None,
) -> P.Pattern: ...


def parse(
    text: str,
    pattern: bool = False,
    constants: ConstantTable | None = None,
    alias_fn: AliasResolver | None = None,
    const_fn: ConstantResolver | None = None,
    binder_fn: BinderResolver | None = None,
) -> ParseValue:
    """Parse an expression in either the term or pattern channel."""
    return Parser[ParseValue](
        tokenize(text),
        pattern=pattern,
        constants=constants,
        alias_fn=alias_fn,
        const_fn=const_fn,
        binder_fn=binder_fn,
    ).parse()


def atom_notation(atom: T.Term) -> str | None:
    """Return the surface spelling of a language atom, if one exists."""
    for name, value in _SYNTAX_ATOMS.items():
        if value is atom:
            return name
    return None
