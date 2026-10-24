"""Data-only declarations for the elementary function fragment.

The file loaded here is not a proof system. It declares constants, unary
functions, their domains and derivative laws. A law is admitted for automatic
use only when the assembler marks it as a trusted standard basis and the law is
unconditional; conditional laws and user axioms stay visible data but are not
applied silently.

The declaration language is deliberately smaller than the user surface syntax:
one unary function form, exact numeric expressions, comparisons and boolean
connectives. It has its own parser because it must not depend on a session's
symbol table.
"""

from __future__ import annotations

import re
from collections.abc import Callable, Mapping
from dataclasses import dataclass
from enum import StrEnum
from fractions import Fraction
from pathlib import Path
from types import MappingProxyType
from typing import TypeAlias

from cas.foundation.ids import SymbolId
from cas.language import sorts as S
from cas.language.declarations import sort_from_name
from cas.language.signatures import LanguageSignature, OperatorSignature, StructuralHead
from cas.syntax import term as T

DEFAULT_DECLARATIONS = Path(__file__).with_name("declarations.dsl")


class LawOrigin(StrEnum):
    """Where an admitted law comes from."""

    BASIS = "basis"
    USER_AXIOM = "user_axiom"


@dataclass(frozen=True, slots=True)
class Name:
    name: str


@dataclass(frozen=True, slots=True)
class Num:
    value: Fraction


@dataclass(frozen=True, slots=True)
class Call:
    name: str
    arguments: tuple[LawExpr, ...]


@dataclass(frozen=True, slots=True)
class Sum:
    terms: tuple[LawExpr, ...]


@dataclass(frozen=True, slots=True)
class Product:
    factors: tuple[LawExpr, ...]


@dataclass(frozen=True, slots=True)
class Negate:
    operand: LawExpr


@dataclass(frozen=True, slots=True)
class Power:
    base: LawExpr
    exponent: LawExpr


@dataclass(frozen=True, slots=True)
class Compare:
    operator: str
    left: LawExpr
    right: LawExpr


@dataclass(frozen=True, slots=True)
class Junction:
    operator: str
    arguments: tuple[LawExpr, ...]


@dataclass(frozen=True, slots=True)
class Negation:
    operand: LawExpr


LawExpr: TypeAlias = (
    Name
    | Num
    | Call
    | Sum
    | Product
    | Negate
    | Power
    | Compare
    | Junction
    | Negation
)


class ElementaryDeclarationError(Exception):
    """A declaration line cannot be admitted."""

    def __init__(self, message: str, line: int) -> None:
        super().__init__(f"line {line}: {message}")
        self.message = message
        self.line = line


@dataclass(frozen=True, slots=True)
class ConstantSource:
    name: str
    sort: S.Sort


@dataclass(frozen=True, slots=True)
class FunctionSource:
    name: str
    arguments: tuple[S.Sort, ...]
    result: S.Sort
    domain: LawExpr | None
    line: int


@dataclass(frozen=True, slots=True)
class LawSource:
    function: str
    argument: str
    body: LawExpr
    condition: LawExpr | None
    origin: LawOrigin
    line: int


@dataclass(frozen=True, slots=True)
class ElementarySource:
    constants: tuple[ConstantSource, ...]
    functions: tuple[FunctionSource, ...]
    laws: tuple[LawSource, ...]


@dataclass(frozen=True, slots=True)
class ConstantSymbol:
    name: str
    symbol: SymbolId
    sort: S.Sort


@dataclass(frozen=True, slots=True)
class DerivativeLaw:
    argument: str
    body: LawExpr
    condition: LawExpr | None
    origin: LawOrigin
    line: int

    @property
    def is_unconditional(self) -> bool:
        return self.condition is None


@dataclass(frozen=True, slots=True)
class FunctionSymbol:
    name: str
    symbol: SymbolId
    arguments: tuple[S.Sort, ...]
    result: S.Sort
    domain: LawExpr | None
    law: DerivativeLaw | None


@dataclass(frozen=True, slots=True)
class ElementaryLibrary:
    """The assembled elementary signatures and laws, keyed by stable ids."""

    constants: Mapping[str, ConstantSymbol]
    constants_by_id: Mapping[SymbolId, ConstantSymbol]
    functions: Mapping[str, FunctionSymbol]
    functions_by_id: Mapping[SymbolId, FunctionSymbol]
    operators: Mapping[SymbolId, OperatorSignature]

    def is_constant(self, symbol_id: SymbolId) -> bool:
        return symbol_id in self.constants_by_id

    def constant_for(self, symbol_id: SymbolId) -> ConstantSymbol | None:
        return self.constants_by_id.get(symbol_id)

    def function_for(self, symbol_id: SymbolId) -> FunctionSymbol | None:
        return self.functions_by_id.get(symbol_id)

    def admissible_law(self, function: FunctionSymbol) -> DerivativeLaw | None:
        """The law this fragment may apply without an open condition."""
        law = function.law
        if law is None:
            return None
        if law.origin is not LawOrigin.BASIS:
            return None
        if law.condition is not None or function.domain is not None:
            return None
        if self.body_partiality(law.body) is not None:
            return None
        return law

    def body_partiality(self, expression: LawExpr) -> str | None:
        """Why an expression is not total on the declared real domain.

        A derivative law may be used unconditionally only when its body calls
        no function outside its own domain and contains no negative power.
        """
        return _body_partiality(expression, self.functions)

    def instantiate(
        self,
        expression: LawExpr,
        argument_name: str,
        argument: T.Term,
        signature: LanguageSignature,
    ) -> T.Term:
        """Turn a declaration expression into a term around `argument`."""
        number = numeric_value(expression)
        if number is not None:
            return T.number(number)
        if isinstance(expression, Name):
            if expression.name == argument_name:
                return argument
            constant = self.constants.get(expression.name)
            if constant is None:
                raise ValueError(
                    f"unknown name in a law: {expression.name!r}"
                )
            return T.symbol(constant.symbol, constant.name)
        if isinstance(expression, Call):
            function = self.functions.get(expression.name)
            if function is None:
                raise ValueError(
                    f"unknown function in a law: {expression.name!r}"
                )
            return T.app(
                T.symbol(function.symbol, function.name),
                *(
                    self.instantiate(
                        item, argument_name, argument, signature
                    )
                    for item in expression.arguments
                ),
            )
        if isinstance(expression, Sum):
            return T.app(
                _head(signature, StructuralHead.PLUS),
                *(
                    self.instantiate(
                        term, argument_name, argument, signature
                    )
                    for term in expression.terms
                ),
            )
        if isinstance(expression, Product):
            return T.app(
                _head(signature, StructuralHead.TIMES),
                *(
                    self.instantiate(
                        factor, argument_name, argument, signature
                    )
                    for factor in expression.factors
                ),
            )
        if isinstance(expression, Negate):
            return T.app(
                _head(signature, StructuralHead.TIMES),
                T.number(-1),
                self.instantiate(
                    expression.operand, argument_name, argument, signature
                ),
            )
        if isinstance(expression, Power):
            exponent = numeric_value(expression.exponent)
            if exponent is None:
                raise ValueError("a law exponent must be an exact number")
            return T.app(
                _head(signature, StructuralHead.POWER),
                self.instantiate(
                    expression.base, argument_name, argument, signature
                ),
                T.number(exponent),
            )
        if isinstance(expression, Compare):
            head = _COMPARISON_HEADS[expression.operator]
            return T.app(
                _head(signature, head),
                self.instantiate(
                    expression.left, argument_name, argument, signature
                ),
                self.instantiate(
                    expression.right, argument_name, argument, signature
                ),
            )
        if isinstance(expression, Junction):
            head = (
                StructuralHead.AND
                if expression.operator == "and"
                else StructuralHead.OR
            )
            return T.app(
                _head(signature, head),
                *(
                    self.instantiate(
                        item, argument_name, argument, signature
                    )
                    for item in expression.arguments
                ),
            )
        if isinstance(expression, Negation):
            return T.app(
                _head(signature, StructuralHead.NOT),
                self.instantiate(
                    expression.operand, argument_name, argument, signature
                ),
            )
        raise TypeError(
            f"unknown declaration expression: {type(expression).__name__}"
        )


_COMPARISON_HEADS = {
    "==": StructuralHead.EQ,
    "!=": StructuralHead.NE,
    "<": StructuralHead.LT,
    "<=": StructuralHead.LE,
    ">": StructuralHead.GT,
    ">=": StructuralHead.GE,
}


def _head(signature: LanguageSignature, head: StructuralHead) -> T.SymbolRef:
    symbol_id = signature.symbol_of(head)
    if symbol_id is None:
        raise ValueError(f"the language has no symbol for {head.value}")
    return T.symbol(symbol_id, head.value)


def _tokenize(text: str, line: int) -> tuple[_Token, ...]:
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
        if pair in {"<=", ">=", "==", "!="}:
            tokens.append(_Token("symbol", pair, index))
            index += 2
            continue
        if character in "+-*/^(),<>":
            tokens.append(_Token("symbol", character, index))
            index += 1
            continue
        raise ElementaryDeclarationError(
            f"unexpected character {character!r} at column {index + 1}", line
        )
    tokens.append(_Token("end", "", len(text)))
    return tuple(tokens)


@dataclass(frozen=True, slots=True)
class _Token:
    kind: str
    value: str
    position: int


class _ExpressionParser:
    __slots__ = ("_index", "_line", "_text", "_tokens")

    def __init__(self, text: str, line: int) -> None:
        self._text = text
        self._line = line
        self._tokens = _tokenize(text, line)
        self._index = 0

    def parse(self) -> LawExpr:
        expression = self._or()
        token = self._peek()
        if token.kind != "end":
            raise self._error(f"unexpected token {token.value!r}")
        return expression

    def _peek(self) -> _Token:
        return self._tokens[self._index]

    def _advance(self) -> _Token:
        token = self._tokens[self._index]
        self._index += 1
        return token

    def _at(self, value: str) -> bool:
        return self._peek().value == value

    def _expect(self, value: str) -> None:
        token = self._peek()
        if token.value != value:
            raise self._error(f"expected {value!r}, got {token.value!r}")
        self._advance()

    def _error(self, message: str) -> ElementaryDeclarationError:
        return ElementaryDeclarationError(
            f"{message} at column {self._peek().position + 1}", self._line
        )

    def _or(self) -> LawExpr:
        parts = [self._and()]
        while self._at("or"):
            self._advance()
            parts.append(self._and())
        return parts[0] if len(parts) == 1 else Junction("or", tuple(parts))

    def _and(self) -> LawExpr:
        parts = [self._not()]
        while self._at("and"):
            self._advance()
            parts.append(self._not())
        return parts[0] if len(parts) == 1 else Junction("and", tuple(parts))

    def _not(self) -> LawExpr:
        if self._at("not"):
            self._advance()
            return Negation(self._not())
        return self._comparison()

    def _comparison(self) -> LawExpr:
        left = self._sum()
        operator = self._peek().value
        if operator not in _COMPARISON_HEADS:
            return left
        self._advance()
        right = self._sum()
        if self._peek().value in _COMPARISON_HEADS:
            raise self._error("a chained comparison is not one condition")
        return Compare(operator, left, right)

    def _sum(self) -> LawExpr:
        terms = [self._product()]
        while self._at("+") or self._at("-"):
            operator = self._advance().value
            right = self._product()
            if operator == "+":
                terms.append(right)
            else:
                terms.append(Negate(right))
        return terms[0] if len(terms) == 1 else Sum(tuple(terms))

    def _product(self) -> LawExpr:
        factors = [self._unary()]
        while self._at("*") or self._at("/"):
            operator = self._advance().value
            right = self._unary()
            if operator == "*":
                factors.append(right)
            else:
                factors.append(Power(right, Num(Fraction(-1))))
        return (
            factors[0]
            if len(factors) == 1
            else Product(tuple(factors))
        )

    def _unary(self) -> LawExpr:
        if self._at("-"):
            self._advance()
            return Negate(self._unary())
        if self._at("+"):
            self._advance()
            return self._unary()
        return self._power()

    def _power(self) -> LawExpr:
        base = self._atom()
        if self._at("^"):
            self._advance()
            return Power(base, self._unary())
        return base

    def _atom(self) -> LawExpr:
        token = self._peek()
        if token.kind == "number":
            self._advance()
            return Num(Fraction(int(token.value)))
        if token.kind == "name":
            self._advance()
            if self._at("("):
                return self._call(token.value)
            return Name(token.value)
        if self._at("("):
            self._advance()
            expression = self._or()
            self._expect(")")
            return expression
        raise self._error("expected an expression")

    def _call(self, name: str) -> LawExpr:
        self._expect("(")
        arguments: list[LawExpr] = []
        if not self._at(")"):
            arguments.append(self._or())
            while self._at(","):
                self._advance()
                arguments.append(self._or())
        self._expect(")")
        return Call(name, tuple(arguments))


def _parse_expression(text: str, line: int) -> LawExpr:
    return _ExpressionParser(text, line).parse()


def numeric_value(expression: LawExpr) -> Fraction | None:
    """Evaluate an expression containing no names or calls, exactly."""
    if isinstance(expression, Num):
        return expression.value
    if isinstance(expression, Negate):
        value = numeric_value(expression.operand)
        return None if value is None else -value
    if isinstance(expression, Sum):
        total = Fraction(0)
        for term in expression.terms:
            value = numeric_value(term)
            if value is None:
                return None
            total += value
        return total
    if isinstance(expression, Product):
        product = Fraction(1)
        for factor in expression.factors:
            value = numeric_value(factor)
            if value is None:
                return None
            product *= value
        return product
    if isinstance(expression, Power):
        base = numeric_value(expression.base)
        exponent = numeric_value(expression.exponent)
        if base is None or exponent is None or exponent.denominator != 1:
            return None
        if exponent.numerator < 0 and base == 0:
            return None
        return base**exponent.numerator
    return None


def _body_partiality(
    expression: LawExpr,
    functions: Mapping[str, FunctionSymbol | FunctionSource],
) -> str | None:
    if isinstance(expression, (Num, Name)):
        return None
    if isinstance(expression, Call):
        function = functions.get(expression.name)
        if function is not None and function.domain is not None:
            return f"calls {function.name} outside its declared domain"
        for argument in expression.arguments:
            problem = _body_partiality(argument, functions)
            if problem is not None:
                return problem
        return None
    if isinstance(expression, Sum):
        for term in expression.terms:
            problem = _body_partiality(term, functions)
            if problem is not None:
                return problem
        return None
    if isinstance(expression, Product):
        for factor in expression.factors:
            problem = _body_partiality(factor, functions)
            if problem is not None:
                return problem
        return None
    if isinstance(expression, Negate):
        return _body_partiality(expression.operand, functions)
    if isinstance(expression, Power):
        exponent = numeric_value(expression.exponent)
        if (
            exponent is None
            or exponent.denominator != 1
            or exponent < 0
        ):
            return "contains a negative or non-integral power"
        return _body_partiality(expression.base, functions)
    if isinstance(expression, Compare):
        for side in (expression.left, expression.right):
            problem = _body_partiality(side, functions)
            if problem is not None:
                return problem
        return None
    if isinstance(expression, Junction):
        for item in expression.arguments:
            problem = _body_partiality(item, functions)
            if problem is not None:
                return problem
        return None
    if isinstance(expression, Negation):
        return _body_partiality(expression.operand, functions)
    return None


def _validate(
    expression: LawExpr,
    argument: str,
    constants: Mapping[str, ConstantSource | ConstantSymbol],
    functions: Mapping[str, FunctionSource | FunctionSymbol],
    line: int,
) -> None:
    if isinstance(expression, Num):
        return
    if isinstance(expression, Name):
        if expression.name == argument or expression.name in constants:
            return
        if expression.name in functions:
            raise ElementaryDeclarationError(
                f"function {expression.name!r} is used without arguments", line
            )
        raise ElementaryDeclarationError(
            f"unknown name {expression.name!r}", line
        )
    if isinstance(expression, Call):
        function = functions.get(expression.name)
        if function is None:
            raise ElementaryDeclarationError(
                f"unknown function {expression.name!r}", line
            )
        if len(expression.arguments) != len(function.arguments):
            raise ElementaryDeclarationError(
                f"function {expression.name!r} takes "
                f"{len(function.arguments)} arguments", line
            )
        for item in expression.arguments:
            _validate(item, argument, constants, functions, line)
        return
    if isinstance(expression, Sum):
        for term in expression.terms:
            _validate(term, argument, constants, functions, line)
        return
    if isinstance(expression, Product):
        for factor in expression.factors:
            _validate(factor, argument, constants, functions, line)
        return
    if isinstance(expression, Negate):
        _validate(expression.operand, argument, constants, functions, line)
        return
    if isinstance(expression, Power):
        _validate(expression.base, argument, constants, functions, line)
        if numeric_value(expression.exponent) is None:
            raise ElementaryDeclarationError(
                "a power exponent must be an exact number", line
            )
        return
    if isinstance(expression, Compare):
        _validate(expression.left, argument, constants, functions, line)
        _validate(expression.right, argument, constants, functions, line)
        return
    if isinstance(expression, Junction):
        for item in expression.arguments:
            _validate(item, argument, constants, functions, line)
        return
    if isinstance(expression, Negation):
        _validate(expression.operand, argument, constants, functions, line)
        return
    raise TypeError(
        f"unknown declaration expression: {type(expression).__name__}"
    )


def _split_condition(text: str) -> tuple[str, str | None]:
    depth = 0
    for index, character in enumerate(text):
        if character == "(":
            depth += 1
        elif character == ")":
            depth -= 1
        elif (
            depth == 0
            and text.startswith("on", index)
            and (index == 0 or text[index - 1].isspace())
            and (
                index + 2 == len(text)
                or text[index + 2].isspace()
            )
        ):
            return text[:index].strip(), text[index + 2 :].strip()
    return text.strip(), None


_CONSTANT = re.compile(r"constant\s+([A-Za-z_][A-Za-z0-9_]*)\s*:\s*(\w+)\Z")
_FUNCTION = re.compile(
    r"function\s+([A-Za-z_][A-Za-z0-9_]*)\s*:\s*(\w+)\s*->\s*(\w+)"
    r"(?:\s+on\s+(.+))?\Z"
)
_DERIVATIVE = re.compile(
    r"derivative\s+([A-Za-z_][A-Za-z0-9_]*)\s*"
    r"\(\s*([A-Za-z_][A-Za-z0-9_]*)\s*\)\s*=\s*(.+)\Z"
)


def load_elementary(
    text: str,
    *,
    origin: LawOrigin = LawOrigin.USER_AXIOM,
) -> ElementarySource:
    """Parse elementary declarations; nothing is registered."""
    constants: list[ConstantSource] = []
    functions: list[FunctionSource] = []
    laws: list[LawSource] = []
    seen: set[str] = set()
    for number, raw in enumerate(text.splitlines(), start=1):
        line = raw.split("#", 1)[0].strip()
        if not line:
            continue
        constant = _CONSTANT.fullmatch(line)
        if constant is not None:
            name, sort_name = constant.groups()
            if name in seen:
                raise ElementaryDeclarationError(
                    f"duplicate declaration {name!r}", number
                )
            seen.add(name)
            sort = sort_from_name(sort_name)
            if sort is None:
                raise ElementaryDeclarationError(
                    f"unknown sort {sort_name!r}", number
                )
            constants.append(ConstantSource(name, sort))
            continue
        function = _FUNCTION.fullmatch(line)
        if function is not None:
            name, argument_name, result_name, domain_text = function.groups()
            if name in seen:
                raise ElementaryDeclarationError(
                    f"duplicate declaration {name!r}", number
                )
            seen.add(name)
            argument_sort = sort_from_name(argument_name)
            if argument_sort is None:
                raise ElementaryDeclarationError(
                    f"unknown sort {argument_name!r}", number
                )
            result_sort = sort_from_name(result_name)
            if result_sort is None:
                raise ElementaryDeclarationError(
                    f"unknown sort {result_name!r}", number
                )
            domain = (
                None
                if domain_text is None
                else _parse_expression(domain_text, number)
            )
            functions.append(
                FunctionSource(
                    name, (argument_sort,), result_sort, domain, number
                )
            )
            continue
        derivative = _DERIVATIVE.fullmatch(line)
        if derivative is not None:
            name, argument, body_text = derivative.groups()
            body_text, condition_text = _split_condition(body_text)
            body = _parse_expression(body_text, number)
            condition = (
                None
                if condition_text is None
                else _parse_expression(condition_text, number)
            )
            laws.append(
                LawSource(
                    name, argument, body, condition, origin, number
                )
            )
            continue
        raise ElementaryDeclarationError(
            "expected 'constant NAME : SORT', "
            "'function NAME : SORT -> SORT [on CONDITION]' or "
            "'derivative NAME(ARG) = EXPR [on CONDITION]'",
            number,
        )
    return ElementarySource(
        tuple(constants), tuple(functions), tuple(laws)
    )


def load_elementary_file(
    path: str | Path,
    *,
    origin: LawOrigin = LawOrigin.USER_AXIOM,
) -> ElementarySource:
    """Read and parse an elementary declaration file."""
    return load_elementary(
        Path(path).read_text(encoding="utf-8"), origin=origin
    )


def default_elementary_source() -> ElementarySource:
    """The standard elementary basis, admitted at assembly time."""
    return load_elementary_file(
        DEFAULT_DECLARATIONS, origin=LawOrigin.BASIS
    )


def build_elementary(
    intern: Callable[[str], SymbolId],
    source: ElementarySource,
    *,
    reserved: frozenset[str] = frozenset(),
) -> ElementaryLibrary:
    """Build stable ids, operator signatures and law data."""
    reserved_names = (
        frozenset(head.value for head in StructuralHead) | reserved
    )
    constants: dict[str, ConstantSymbol] = {}
    functions: dict[str, FunctionSymbol] = {}
    laws: dict[str, DerivativeLaw] = {}
    for constant_declaration in source.constants:
        if constant_declaration.name in reserved_names:
            raise ValueError(
                f"{constant_declaration.name!r} is a reserved name"
            )
        if constant_declaration.name in functions:
            raise ValueError(
                f"{constant_declaration.name!r} is declared twice"
            )
        symbol_id = intern(constant_declaration.name)
        constants[constant_declaration.name] = ConstantSymbol(
            constant_declaration.name, symbol_id, constant_declaration.sort
        )
    for function_declaration in source.functions:
        if function_declaration.name in reserved_names:
            raise ValueError(
                f"{function_declaration.name!r} is a reserved name"
            )
        if (
            function_declaration.name in constants
            or function_declaration.name in functions
        ):
            raise ValueError(
                f"{function_declaration.name!r} is declared twice"
            )
        symbol_id = intern(function_declaration.name)
        functions[function_declaration.name] = FunctionSymbol(
            function_declaration.name,
            symbol_id,
            function_declaration.arguments,
            function_declaration.result,
            function_declaration.domain,
            None,
        )
    for function_declaration in source.functions:
        if function_declaration.domain is not None:
            _validate(
                function_declaration.domain,
                "u",
                constants,
                functions,
                function_declaration.line,
            )
    for law_declaration in source.laws:
        function = functions.get(law_declaration.function)
        if function is None:
            raise ElementaryDeclarationError(
                f"derivative law for unknown function "
                f"{law_declaration.function!r}",
                law_declaration.line,
            )
        if law_declaration.function in laws:
            raise ElementaryDeclarationError(
                f"duplicate derivative law for {law_declaration.function!r}",
                law_declaration.line,
            )
        if len(function.arguments) != 1:
            raise ElementaryDeclarationError(
                "the elementary fragment has unary derivative laws only",
                law_declaration.line,
            )
        if (
            law_declaration.argument in constants
            or law_declaration.argument in functions
            or law_declaration.argument in reserved_names
        ):
            raise ElementaryDeclarationError(
                f"{law_declaration.argument!r} is not a fresh law argument",
                law_declaration.line,
            )
        _validate(
            law_declaration.body,
            law_declaration.argument,
            constants,
            functions,
            law_declaration.line,
        )
        if law_declaration.condition is not None:
            _validate(
                law_declaration.condition,
                law_declaration.argument,
                constants,
                functions,
                law_declaration.line,
            )
        else:
            problem = _body_partiality(
                law_declaration.body, functions
            )
            if problem is not None:
                raise ElementaryDeclarationError(
                    "an unconditional derivative law must be total: "
                    f"{problem}",
                    law_declaration.line,
                )
        law = DerivativeLaw(
            law_declaration.argument,
            law_declaration.body,
            law_declaration.condition,
            law_declaration.origin,
            law_declaration.line,
        )
        laws[law_declaration.function] = law
        functions[law_declaration.function] = FunctionSymbol(
            function.name,
            function.symbol,
            function.arguments,
            function.result,
            function.domain,
            law,
        )
    operators: dict[SymbolId, OperatorSignature] = {}
    for function in functions.values():
        operators[function.symbol] = OperatorSignature(
            function.arguments, function.result
        )
    return ElementaryLibrary(
        MappingProxyType(constants),
        MappingProxyType(
            {
                constant.symbol: constant
                for constant in constants.values()
            }
        ),
        MappingProxyType(functions),
        MappingProxyType(
            {
                function.symbol: function
                for function in functions.values()
            }
        ),
        MappingProxyType(operators),
    )


__all__ = [
    "Call",
    "Compare",
    "ConstantSource",
    "ConstantSymbol",
    "DEFAULT_DECLARATIONS",
    "DerivativeLaw",
    "ElementaryDeclarationError",
    "ElementaryLibrary",
    "ElementarySource",
    "FunctionSource",
    "FunctionSymbol",
    "Junction",
    "LawExpr",
    "LawOrigin",
    "LawSource",
    "Name",
    "Negate",
    "Negation",
    "Num",
    "Power",
    "Product",
    "Sum",
    "build_elementary",
    "default_elementary_source",
    "load_elementary",
    "load_elementary_file",
    "numeric_value",
]
