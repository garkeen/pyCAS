"""The single data-only declaration language.

The file describes constants, operators, functions, binders and derivative
laws. It is data, not a proof system: loading it assigns no truth and installs
nothing. A math module consumes the resulting `DeclarationSet` and decides
which laws it admits.

The declaration language has its own tokenizer and expression grammar because it
must be independent of a session's symbol table. It is the only declaration
parser in the tree; math modules do not carry a second parser.
"""

from __future__ import annotations

import hashlib
import re
from collections.abc import Callable, Mapping
from dataclasses import dataclass
from enum import StrEnum
from fractions import Fraction
from pathlib import Path
from typing import TypeAlias

from cas.foundation.ids import SymbolId
from cas.language import sorts as S
from cas.language.numbers import exact_power
from cas.language.signatures import (
    COMPARISON_BY_TEXT,
    BindingSignature,
    LanguageSignature,
    OperatorSignature,
    StructuralHead,
)

DOMAIN_ARGUMENT = "u"

_SORTS: dict[str, S.Sort] = {
    "Integer": S.INTEGER,
    "Rational": S.RATIONAL,
    "Real": S.REAL,
    "Complex": S.COMPLEX,
    "Proposition": S.PROPOSITION,
    "Region": S.REGION,
    "Syntax": S.SYNTAX,
    "Unknown": S.UNKNOWN_SCALAR,
}
_RESERVED_HEADS = frozenset(head.value for head in StructuralHead)
_IDENTIFIER = re.compile(r"[A-Za-z_]\w*\Z")


class DeclarationOrigin(StrEnum):
    """Where a law comes from; admission is the consuming module's decision."""

    BASIS = "basis"
    USER_AXIOM = "user_axiom"


# --- declaration expressions ---


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

_LAW_NODES = (
    Name,
    Num,
    Call,
    Sum,
    Product,
    Negate,
    Power,
    Compare,
    Junction,
    Negation,
)


def is_law_expression(value: object) -> bool:
    """Whether `value` is a node of the declaration expression language."""
    return isinstance(value, _LAW_NODES)


def law_children(expression: LawExpr) -> tuple[LawExpr, ...]:
    """The immediate subexpressions of one declaration expression.

    This is the single owner of the declaration syntax tree. Consumers that
    validate, evaluate or inspect law expressions recurse through this function
    instead of repeating the node-type dispatch.
    """
    if isinstance(expression, (Name, Num)):
        return ()
    if isinstance(expression, Call):
        return expression.arguments
    if isinstance(expression, Sum):
        return expression.terms
    if isinstance(expression, Product):
        return expression.factors
    if isinstance(expression, (Negate, Negation)):
        return (expression.operand,)
    if isinstance(expression, Power):
        return (expression.base, expression.exponent)
    if isinstance(expression, Compare):
        return (expression.left, expression.right)
    if isinstance(expression, Junction):
        return expression.arguments
    raise TypeError(
        f"unknown declaration expression: {type(expression).__name__}"
    )


class DeclarationError(ValueError):
    """A declaration line or a declaration relation cannot be admitted."""

    def __init__(self, message: str, line: int) -> None:
        super().__init__(f"line {line}: {message}")
        self.message = message
        self.line = line


# --- declaration records ---


@dataclass(frozen=True, slots=True)
class ConstantDeclaration:
    name: str
    sort: S.Sort
    line: int = 0


@dataclass(frozen=True, slots=True)
class OperatorDeclaration:
    name: str
    arguments: tuple[S.Sort, ...]
    result: S.Sort
    line: int = 0


@dataclass(frozen=True, slots=True)
class FunctionDeclaration:
    name: str
    arguments: tuple[S.Sort, ...]
    result: S.Sort
    domain: LawExpr | None
    line: int = 0


@dataclass(frozen=True, slots=True)
class BinderDeclaration:
    name: str
    parameter_sorts: tuple[S.Sort, ...]
    result: S.Sort | None
    line: int = 0

    @property
    def arity(self) -> int:
        return len(self.parameter_sorts)


@dataclass(frozen=True, slots=True)
class LawDeclaration:
    function: str
    argument: str
    body: LawExpr
    condition: LawExpr | None
    origin: DeclarationOrigin
    line: int = 0


@dataclass(frozen=True, slots=True)
class DeclarationSet:
    """The admitted declarations, in file order."""

    constants: tuple[ConstantDeclaration, ...] = ()
    operators: tuple[OperatorDeclaration, ...] = ()
    functions: tuple[FunctionDeclaration, ...] = ()
    binders: tuple[BinderDeclaration, ...] = ()
    laws: tuple[LawDeclaration, ...] = ()
    name: str = "<memory>"
    digest: str = ""

    def __post_init__(self) -> None:
        """Validate the whole declaration set, however it was constructed.

        The loader parses text into these records and this is the single
        admission rule for both paths. Without it, a `DeclarationSet`
        assembled directly would be a way around the loader.
        """
        for field_name in (
            "constants",
            "operators",
            "functions",
            "binders",
            "laws",
        ):
            object.__setattr__(
                self, field_name, tuple(getattr(self, field_name))
            )
        if not isinstance(self.name, str) or not self.name:
            raise ValueError("a declaration set needs a source name")
        if not isinstance(self.digest, str):
            raise TypeError("a declaration set digest must be a string")

        seen: set[str] = set()
        constants: dict[str, ConstantDeclaration] = {}
        for constant in self.constants:
            if not isinstance(constant, ConstantDeclaration):
                raise TypeError(
                    "constants must be ConstantDeclaration records"
                )
            _validate_name(constant.name, seen, constant.line)
            if not isinstance(constant.sort, S.Sort):
                raise TypeError("a constant declaration needs a sort")
            constants[constant.name] = constant

        operators: dict[str, OperatorDeclaration] = {}
        for operator in self.operators:
            if not isinstance(operator, OperatorDeclaration):
                raise TypeError(
                    "operators must be OperatorDeclaration records"
                )
            _validate_name(operator.name, seen, operator.line)
            if not isinstance(operator.arguments, tuple) or any(
                not isinstance(sort, S.Sort)
                for sort in operator.arguments
            ):
                raise TypeError(
                    "an operator takes a tuple of declared sorts"
                )
            if not isinstance(operator.result, S.Sort):
                raise TypeError("an operator needs a result sort")
            operators[operator.name] = operator

        functions: dict[str, FunctionDeclaration] = {}
        for function in self.functions:
            if not isinstance(function, FunctionDeclaration):
                raise TypeError(
                    "functions must be FunctionDeclaration records"
                )
            _validate_name(function.name, seen, function.line)
            if not isinstance(function.arguments, tuple) or not function.arguments:
                raise DeclarationError(
                    "a function needs at least one argument sort",
                    function.line,
                )
            if any(
                not isinstance(sort, S.Sort)
                for sort in function.arguments
            ):
                raise TypeError("a function takes declared sorts")
            if not isinstance(function.result, S.Sort):
                raise TypeError("a function needs a result sort")
            if function.domain is not None and not is_law_expression(
                function.domain
            ):
                raise TypeError(
                    "a function domain must be a declaration expression"
                )
            functions[function.name] = function

        for binder in self.binders:
            if not isinstance(binder, BinderDeclaration):
                raise TypeError(
                    "binders must be BinderDeclaration records"
                )
            _validate_name(binder.name, seen, binder.line)
            if (
                not isinstance(binder.parameter_sorts, tuple)
                or not binder.parameter_sorts
            ):
                raise DeclarationError(
                    "a binder needs at least one parameter sort",
                    binder.line,
                )
            if any(
                not isinstance(sort, S.Sort)
                for sort in binder.parameter_sorts
            ):
                raise TypeError("a binder takes declared sorts")
            if binder.result is not None and not isinstance(
                binder.result, S.Sort
            ):
                raise TypeError("a binder result must be a sort")

        for function in self.functions:
            if function.domain is not None:
                if len(function.arguments) != 1:
                    raise DeclarationError(
                        "a function domain is only defined for unary functions",
                        function.line,
                    )
                _validate_expression(
                    function.domain,
                    DOMAIN_ARGUMENT,
                    constants,
                    functions,
                    function.line,
                )

        law_functions: set[str] = set()
        for law in self.laws:
            if not isinstance(law, LawDeclaration):
                raise TypeError("laws must be LawDeclaration records")
            if not isinstance(law.origin, DeclarationOrigin):
                raise TypeError("a law needs a declaration origin")
            if not is_law_expression(law.body):
                raise TypeError(
                    "a derivative law body must be a declaration expression"
                )
            if law.condition is not None and not is_law_expression(
                law.condition
            ):
                raise TypeError(
                    "a derivative law condition must be a declaration "
                    "expression"
                )
            if law.function not in functions:
                raise DeclarationError(
                    f"derivative law for unknown function {law.function!r}",
                    law.line,
                )
            if law.function in law_functions:
                raise DeclarationError(
                    f"duplicate derivative law for {law.function!r}",
                    law.line,
                )
            law_functions.add(law.function)
            if (
                not isinstance(law.argument, str)
                or _IDENTIFIER.fullmatch(law.argument) is None
            ):
                raise DeclarationError(
                    f"{law.argument!r} is not a valid law argument",
                    law.line,
                )
            if (
                law.argument in constants
                or law.argument in functions
                or law.argument in _RESERVED_HEADS
            ):
                raise DeclarationError(
                    f"{law.argument!r} is not a fresh law argument",
                    law.line,
                )
            _validate_expression(
                law.body,
                law.argument,
                constants,
                functions,
                law.line,
            )
            if law.condition is not None:
                _validate_expression(
                    law.condition,
                    law.argument,
                    constants,
                    functions,
                    law.line,
                )


# --- expression tokenizer and parser ---


@dataclass(frozen=True, slots=True)
class _Token:
    kind: str
    value: str
    position: int


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
        raise DeclarationError(
            f"unexpected character {character!r} at column {index + 1}", line
        )
    tokens.append(_Token("end", "", len(text)))
    return tuple(tokens)


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

    def _error(self, message: str) -> DeclarationError:
        return DeclarationError(
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
        if operator not in COMPARISON_BY_TEXT:
            return left
        self._advance()
        right = self._sum()
        if self._peek().value in COMPARISON_BY_TEXT:
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
            factors[0] if len(factors) == 1 else Product(tuple(factors))
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
        value = numeric_value(law_children(expression)[0])
        return None if value is None else -value
    if isinstance(expression, Sum):
        total = Fraction(0)
        for term in law_children(expression):
            value = numeric_value(term)
            if value is None:
                return None
            total += value
        return total
    if isinstance(expression, Product):
        product = Fraction(1)
        for factor in law_children(expression):
            value = numeric_value(factor)
            if value is None:
                return None
            product *= value
        return product
    if isinstance(expression, Power):
        base_expression, exponent_expression = law_children(expression)
        base = numeric_value(base_expression)
        exponent = numeric_value(exponent_expression)
        if base is None or exponent is None or exponent.denominator != 1:
            return None
        return exact_power(base, exponent.numerator)
    return None


# --- declaration parsing ---


_CONSTANT = re.compile(r"constant\s+([A-Za-z_]\w*)\s*:\s*(\w+)\Z")
_OPERATOR = re.compile(
    r"operator\s+([A-Za-z_]\w*)\s*\(([^)]*)\)\s*->\s*(\S+)\Z"
)
_FUNCTION = re.compile(
    r"function\s+([A-Za-z_]\w*)\s*:\s*(.+?)\s*->\s*(\w+)"
    r"(?:\s+on\s+(.+))?\Z"
)
_BINDER = re.compile(
    r"binder\s+([A-Za-z_]\w*)\s*\(([^)]*)\)\s*->\s*(\S+)\Z"
)
_DERIVATIVE = re.compile(
    r"derivative\s+([A-Za-z_]\w*)\s*"
    r"\(\s*([A-Za-z_]\w*)\s*\)\s*=\s*(.+)\Z"
)


def _parse_sort(text: str, line: int) -> S.Sort:
    sort = sort_from_name(text)
    if sort is None:
        raise DeclarationError(f"unknown sort {text!r}", line)
    return sort


def sort_from_name(name: str) -> S.Sort | None:
    """The declared sort called `name`, or None when the language has none."""
    return _SORTS.get(name)


def _parse_sorts(text: str, line: int) -> tuple[S.Sort, ...]:
    stripped = text.strip()
    if not stripped:
        return ()
    parts = [part.strip() for part in stripped.split(",")]
    if any(not part for part in parts):
        raise DeclarationError("empty parameter sort", line)
    return tuple(_parse_sort(part, line) for part in parts)


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
            and (index + 2 == len(text) or text[index + 2].isspace())
        ):
            return text[:index].strip(), text[index + 2 :].strip()
    return text.strip(), None


def load_declarations(
    text: str,
    *,
    origin: DeclarationOrigin = DeclarationOrigin.USER_AXIOM,
    source_name: str = "<memory>",
) -> DeclarationSet:
    """Parse all declaration forms; nothing is registered or trusted."""
    constants: list[ConstantDeclaration] = []
    operators: list[OperatorDeclaration] = []
    functions: list[FunctionDeclaration] = []
    binders: list[BinderDeclaration] = []
    laws: list[LawDeclaration] = []
    for number, raw in enumerate(text.splitlines(), start=1):
        line = raw.split("#", 1)[0].strip()
        if not line:
            continue

        constant = _CONSTANT.fullmatch(line)
        if constant is not None:
            name, sort_name = constant.groups()
            constants.append(
                ConstantDeclaration(
                    name, _parse_sort(sort_name, number), number
                )
            )
            continue

        operator = _OPERATOR.fullmatch(line)
        if operator is not None:
            name, parameters_text, result_text = operator.groups()
            arguments = _parse_sorts(parameters_text, number)
            if result_text == "function":
                raise DeclarationError(
                    "an operator cannot be function-valued", number
                )
            operators.append(
                OperatorDeclaration(
                    name,
                    arguments,
                    _parse_sort(result_text, number),
                    number,
                )
            )
            continue

        function = _FUNCTION.fullmatch(line)
        if function is not None:
            name, arguments_text, result_name, domain_text = function.groups()
            arguments = _parse_sorts(arguments_text, number)
            domain = (
                None
                if domain_text is None
                else _parse_expression(domain_text, number)
            )
            functions.append(
                FunctionDeclaration(
                    name,
                    arguments,
                    _parse_sort(result_name, number),
                    domain,
                    number,
                )
            )
            continue

        binder = _BINDER.fullmatch(line)
        if binder is not None:
            name, parameters_text, result_text = binder.groups()
            parameters = _parse_sorts(parameters_text, number)
            result = (
                None
                if result_text == "function"
                else _parse_sort(result_text, number)
            )
            binders.append(
                BinderDeclaration(name, parameters, result, number)
            )
            continue

        derivative = _DERIVATIVE.fullmatch(line)
        if derivative is not None:
            function_name, argument, body_text = derivative.groups()
            body_text, condition_text = _split_condition(body_text)
            body = _parse_expression(body_text, number)
            condition = (
                None
                if condition_text is None
                else _parse_expression(condition_text, number)
            )
            laws.append(
                LawDeclaration(
                    function_name,
                    argument,
                    body,
                    condition,
                    origin,
                    number,
                )
            )
            continue

        raise DeclarationError(
            "expected 'constant NAME : SORT', 'operator NAME (SORTS) -> SORT', "
            "'function NAME : SORTS -> SORT [on CONDITION]', "
            "'binder NAME (SORTS) -> function|SORT' or "
            "'derivative NAME(ARG) = EXPR [on CONDITION]'",
            number,
        )

    return DeclarationSet(
        tuple(constants),
        tuple(operators),
        tuple(functions),
        tuple(binders),
        tuple(laws),
        source_name,
        hashlib.sha256(text.encode("utf-8")).hexdigest(),
    )


def _validate_name(name: str, seen: set[str], line: int) -> None:
    if not isinstance(name, str) or _IDENTIFIER.fullmatch(name) is None:
        raise DeclarationError(
            f"{name!r} is not a valid declaration name", line
        )
    if name in _RESERVED_HEADS:
        raise DeclarationError(
            f"{name!r} is a structural head name", line
        )
    if name in seen:
        raise DeclarationError(f"duplicate declaration {name!r}", line)
    seen.add(name)


def _validate_expression(
    expression: LawExpr,
    argument: str,
    constants: Mapping[str, ConstantDeclaration],
    functions: Mapping[str, FunctionDeclaration],
    line: int,
) -> None:
    if isinstance(expression, Num):
        return
    if isinstance(expression, Name):
        if expression.name == argument or expression.name in constants:
            return
        if expression.name in functions:
            raise DeclarationError(
                f"function {expression.name!r} is used without arguments", line
            )
        raise DeclarationError(
            f"unknown name {expression.name!r}", line
        )
    if isinstance(expression, Call):
        function = functions.get(expression.name)
        if function is None:
            raise DeclarationError(
                f"unknown function {expression.name!r}", line
            )
        if len(expression.arguments) != len(function.arguments):
            raise DeclarationError(
                f"function {expression.name!r} takes "
                f"{len(function.arguments)} arguments", line
            )
    elif isinstance(expression, Power):
        if numeric_value(law_children(expression)[1]) is None:
            raise DeclarationError(
                "a power exponent must be an exact number", line
            )
    elif isinstance(expression, Compare):
        if expression.operator not in COMPARISON_BY_TEXT:
            raise DeclarationError(
                f"unknown comparison {expression.operator!r}", line
            )
    elif isinstance(expression, Junction):
        if expression.operator not in ("and", "or"):
            raise DeclarationError(
                f"unknown logical connective {expression.operator!r}", line
            )
    elif not isinstance(expression, (Sum, Product, Negate, Negation)):
        raise TypeError(
            f"unknown declaration expression: {type(expression).__name__}"
        )
    for child in law_children(expression):
        _validate_expression(
            child, argument, constants, functions, line
        )


def load_declarations_file(
    path: str | Path,
    *,
    origin: DeclarationOrigin = DeclarationOrigin.USER_AXIOM,
) -> DeclarationSet:
    """Read and parse a declaration file."""
    source = Path(path)
    return load_declarations(
        source.read_text(encoding="utf-8"),
        origin=origin,
        source_name=source.name,
    )


# --- language assembly ---


def build_language(
    intern: Callable[[str], SymbolId],
    declarations: DeclarationSet,
    operators: Mapping[SymbolId, OperatorSignature] | None = None,
) -> LanguageSignature:
    """Build a language signature from names and declarations.

    Constants are names with a sort, not zero-arity operators: a bare constant
    is typed through its declaration, and `c()` is not silently accepted.
    Extra operators (for example a predicate the consumer assembles) must not
    collide with structural heads or declared operators.
    """
    heads = {intern(head.value): head for head in StructuralHead}
    constants = {
        intern(constant.name) for constant in declarations.constants
    }
    table: dict[SymbolId, OperatorSignature] = {}

    def add(symbol_id: SymbolId, signature: OperatorSignature) -> None:
        if symbol_id in heads:
            raise ValueError(
                "a declared operator cannot use a structural head symbol"
            )
        if symbol_id in constants:
            raise ValueError(
                "a declared operator cannot reuse a constant symbol"
            )
        if symbol_id in table:
            raise ValueError("an operator symbol is declared twice")
        table[symbol_id] = signature

    for operator in declarations.operators:
        add(
            intern(operator.name),
            OperatorSignature(operator.arguments, operator.result),
        )
    for function in declarations.functions:
        add(
            intern(function.name),
            OperatorSignature(function.arguments, function.result),
        )
    for symbol_id, signature in (operators or {}).items():
        if not isinstance(signature, OperatorSignature):
            raise TypeError("an extra operator needs an OperatorSignature")
        add(symbol_id, signature)
    binders = {
        binder.name: BindingSignature(
            binder.name,
            binder.arity,
            binder.parameter_sorts,
            binder.result,
        )
        for binder in declarations.binders
    }
    return LanguageSignature.build(heads, binders, table)


__all__ = [
    "BinderDeclaration",
    "Call",
    "Compare",
    "ConstantDeclaration",
    "DOMAIN_ARGUMENT",
    "DeclarationError",
    "DeclarationOrigin",
    "DeclarationSet",
    "FunctionDeclaration",
    "Junction",
    "LawDeclaration",
    "LawExpr",
    "Name",
    "Negate",
    "Negation",
    "Num",
    "OperatorDeclaration",
    "Power",
    "Product",
    "Sum",
    "build_language",
    "is_law_expression",
    "law_children",
    "load_declarations",
    "load_declarations_file",
    "numeric_value",
    "sort_from_name",
]
