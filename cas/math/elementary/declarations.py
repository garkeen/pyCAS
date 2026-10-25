"""The admitted elementary library built from the shared declaration language.

Loading and parsing live in `cas.language.declarations`. This module decides
which declared functions and derivative laws the elementary fragment admits and
builds stable symbol ids; it does not carry a second parser.
"""

from __future__ import annotations

from collections.abc import Callable, Mapping
from dataclasses import dataclass
from pathlib import Path
from types import MappingProxyType

from cas.foundation.ids import SymbolId
from cas.kernel.trust import BasisKind, BasisRef
from cas.language import sorts as S
from cas.language.declarations import (
    Call,
    Compare,
    DeclarationError,
    DeclarationOrigin,
    DeclarationSet,
    Junction,
    LawExpr,
    Name,
    Negate,
    Negation,
    Num,
    Power,
    Product,
    Sum,
    is_law_expression,
    law_children,
    load_declarations_file,
    numeric_value,
)
from cas.language.signatures import (
    COMPARISON_BY_TEXT,
    LanguageSignature,
    StructuralHead,
)
from cas.syntax import term as T

DEFAULT_DECLARATIONS = Path(__file__).with_name("declarations.dsl")


@dataclass(frozen=True, slots=True)
class ConstantSymbol:
    name: str
    symbol: SymbolId
    sort: S.Sort

    def __post_init__(self) -> None:
        if not isinstance(self.name, str) or not self.name:
            raise ValueError("a constant symbol needs a name")
        if not isinstance(self.symbol, int) or isinstance(self.symbol, bool):
            raise TypeError("a constant symbol needs a SymbolId")
        if not isinstance(self.sort, S.Sort):
            raise TypeError("a constant symbol needs a sort")


@dataclass(frozen=True, slots=True)
class DerivativeLaw:
    argument: str
    body: LawExpr
    condition: LawExpr | None
    origin: DeclarationOrigin
    line: int

    def __post_init__(self) -> None:
        if not isinstance(self.argument, str) or not self.argument:
            raise ValueError("a derivative law needs an argument name")
        if not is_law_expression(self.body):
            raise TypeError("a derivative law body must be an expression")
        if self.condition is not None and not is_law_expression(
            self.condition
        ):
            raise TypeError("a derivative law condition must be an expression")
        if not isinstance(self.origin, DeclarationOrigin):
            raise TypeError("a derivative law needs an origin")
        if not isinstance(self.line, int) or self.line < 0:
            raise TypeError("a derivative law needs a source line")


@dataclass(frozen=True, slots=True)
class FunctionSymbol:
    name: str
    symbol: SymbolId
    arguments: tuple[S.Sort, ...]
    result: S.Sort
    domain: LawExpr | None
    law: DerivativeLaw | None

    def __post_init__(self) -> None:
        if not isinstance(self.name, str) or not self.name:
            raise ValueError("a function symbol needs a name")
        if not isinstance(self.symbol, int) or isinstance(self.symbol, bool):
            raise TypeError("a function symbol needs a SymbolId")
        if not self.arguments or not isinstance(self.arguments, tuple):
            raise TypeError("a function symbol needs argument sorts")
        if any(not isinstance(sort, S.Sort) for sort in self.arguments):
            raise TypeError("a function symbol needs declared argument sorts")
        if not isinstance(self.result, S.Sort):
            raise TypeError("a function symbol needs a result sort")
        if self.domain is not None and not is_law_expression(self.domain):
            raise TypeError("a function domain must be an expression")
        if self.law is not None and not isinstance(
            self.law, DerivativeLaw
        ):
            raise TypeError("a function law must be a DerivativeLaw")


@dataclass(frozen=True, slots=True)
class ElementaryLibrary:
    """The assembled elementary signatures and laws, keyed by stable ids.

    Construction is validated even when the library is assembled by hand:
    name maps and id maps must describe the same records, constants and
    functions must not share a symbol, and a basis law needs an admitted basis.
    """

    constants: Mapping[str, ConstantSymbol]
    constants_by_id: Mapping[SymbolId, ConstantSymbol]
    functions: Mapping[str, FunctionSymbol]
    functions_by_id: Mapping[SymbolId, FunctionSymbol]
    basis: BasisRef | None = None

    def __post_init__(self) -> None:
        for field_name in (
            "constants",
            "constants_by_id",
            "functions",
            "functions_by_id",
        ):
            object.__setattr__(
                self,
                field_name,
                MappingProxyType(dict(getattr(self, field_name))),
            )
        if self.basis is not None:
            if not isinstance(self.basis, BasisRef):
                raise TypeError("a library basis must be a BasisRef")
            if self.basis.kind is not BasisKind.DECLARATION_FILE:
                raise ValueError(
                    "an elementary basis must be a declaration file"
                )
            if not self.basis.digest:
                raise ValueError("an elementary basis needs a digest")

        expected_constants = {
            constant.symbol: constant
            for constant in self.constants.values()
        }
        if dict(self.constants_by_id) != expected_constants:
            raise ValueError(
                "the constant id map disagrees with the name map"
            )
        expected_functions = {
            function.symbol: function
            for function in self.functions.values()
        }
        if dict(self.functions_by_id) != expected_functions:
            raise ValueError(
                "the function id map disagrees with the name map"
            )

        reserved = frozenset(head.value for head in StructuralHead)
        symbols: set[SymbolId] = set()
        for name, constant in self.constants.items():
            if not isinstance(name, str) or not name:
                raise ValueError("a constant map needs a name key")
            if not isinstance(constant, ConstantSymbol):
                raise TypeError("a constant map holds ConstantSymbol values")
            if constant.name != name:
                raise ValueError("a constant name disagrees with its key")
            if name in reserved:
                raise ValueError(f"{name!r} is a structural head name")
            if constant.symbol in symbols:
                raise ValueError(
                    "a symbol is declared both as constant and function"
                )
            symbols.add(constant.symbol)

        for name, function in self.functions.items():
            if not isinstance(name, str) or not name:
                raise ValueError("a function map needs a name key")
            if not isinstance(function, FunctionSymbol):
                raise TypeError("a function map holds FunctionSymbol values")
            if function.name != name:
                raise ValueError("a function name disagrees with its key")
            if name in reserved:
                raise ValueError(f"{name!r} is a structural head name")
            if function.symbol in symbols:
                raise ValueError(
                    "a symbol is declared both as constant and function"
                )
            symbols.add(function.symbol)

        for function in self.functions.values():
            law = function.law
            if (
                law is not None
                and law.origin is DeclarationOrigin.BASIS
                and self.basis is None
            ):
                raise ValueError(
                    "a BASIS derivative law requires an admitted BasisRef"
                )

    def is_constant(self, symbol_id: SymbolId) -> bool:
        return symbol_id in self.constants_by_id

    def constant_for(self, symbol_id: SymbolId) -> ConstantSymbol | None:
        return self.constants_by_id.get(symbol_id)

    def function_for(self, symbol_id: SymbolId) -> FunctionSymbol | None:
        return self.functions_by_id.get(symbol_id)

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
                signature.head_term(StructuralHead.PLUS),
                *(
                    self.instantiate(
                        term, argument_name, argument, signature
                    )
                    for term in expression.terms
                ),
            )
        if isinstance(expression, Product):
            return T.app(
                signature.head_term(StructuralHead.TIMES),
                *(
                    self.instantiate(
                        factor, argument_name, argument, signature
                    )
                    for factor in expression.factors
                ),
            )
        if isinstance(expression, Negate):
            return T.app(
                signature.head_term(StructuralHead.TIMES),
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
                signature.head_term(StructuralHead.POWER),
                self.instantiate(
                    expression.base, argument_name, argument, signature
                ),
                T.number(exponent),
            )
        if isinstance(expression, Compare):
            head = COMPARISON_BY_TEXT[expression.operator]
            return T.app(
                signature.head_term(head),
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
                signature.head_term(head),
                *(
                    self.instantiate(
                        item, argument_name, argument, signature
                    )
                    for item in expression.arguments
                ),
            )
        if isinstance(expression, Negation):
            return T.app(
                signature.head_term(StructuralHead.NOT),
                self.instantiate(
                    expression.operand, argument_name, argument, signature
                ),
            )
        raise TypeError(
            f"unknown declaration expression: {type(expression).__name__}"
        )


def _body_partiality(
    expression: LawExpr,
    functions: Mapping[str, FunctionSymbol],
) -> str | None:
    if isinstance(expression, (Num, Name)):
        return None
    if isinstance(expression, Call):
        function = functions.get(expression.name)
        if function is not None and function.domain is not None:
            return f"calls {function.name} outside its declared domain"
    elif isinstance(expression, Power):
        exponent = numeric_value(law_children(expression)[1])
        if (
            exponent is None
            or exponent.denominator != 1
            or exponent < 0
        ):
            return "contains a negative or non-integral power"
    for child in law_children(expression):
        problem = _body_partiality(child, functions)
        if problem is not None:
            return problem
    return None


def default_elementary_declarations() -> DeclarationSet:
    """The standard elementary basis, admitted at assembly time."""
    return load_declarations_file(
        DEFAULT_DECLARATIONS, origin=DeclarationOrigin.BASIS
    )


def build_elementary(
    intern: Callable[[str], SymbolId],
    declarations: DeclarationSet,
    *,
    reserved: frozenset[str] = frozenset(),
    basis: BasisRef | None = None,
) -> ElementaryLibrary:
    """Build stable ids, operator signatures and admitted law data."""
    if basis is not None:
        if basis.kind is not BasisKind.DECLARATION_FILE:
            raise ValueError(
                "an elementary basis must be a declaration file"
            )
        if not declarations.digest:
            raise ValueError(
                "a declaration basis needs a source digest"
            )
        if basis.name != declarations.name:
            raise ValueError(
                "the basis name does not match the declaration source"
            )
        if basis.digest != declarations.digest:
            raise ValueError(
                "the basis digest does not match the declaration source"
            )
    reserved_names = (
        frozenset(head.value for head in StructuralHead) | reserved
    )
    constants: dict[str, ConstantSymbol] = {}
    functions: dict[str, FunctionSymbol] = {}
    laws: dict[str, DerivativeLaw] = {}
    for constant_declaration in declarations.constants:
        if constant_declaration.name in reserved_names:
            raise ValueError(
                f"{constant_declaration.name!r} is a reserved name"
            )
        if (
            constant_declaration.name in constants
            or constant_declaration.name in functions
        ):
            raise ValueError(
                f"{constant_declaration.name!r} is declared twice"
            )
        symbol_id = intern(constant_declaration.name)
        constants[constant_declaration.name] = ConstantSymbol(
            constant_declaration.name, symbol_id, constant_declaration.sort
        )
    for function_declaration in declarations.functions:
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
    for law_declaration in declarations.laws:
        function = functions.get(law_declaration.function)
        if function is None:
            raise DeclarationError(
                f"derivative law for unknown function "
                f"{law_declaration.function!r}",
                law_declaration.line,
            )
        if law_declaration.function in laws:
            raise DeclarationError(
                f"duplicate derivative law for "
                f"{law_declaration.function!r}",
                law_declaration.line,
            )
        if len(function.arguments) != 1:
            raise DeclarationError(
                "the elementary fragment has unary derivative laws only",
                law_declaration.line,
            )
        if (
            law_declaration.argument in constants
            or law_declaration.argument in functions
            or law_declaration.argument in reserved_names
        ):
            raise DeclarationError(
                f"{law_declaration.argument!r} is not a fresh law argument",
                law_declaration.line,
            )
        if law_declaration.condition is None:
            problem = _body_partiality(
                law_declaration.body, functions
            )
            if problem is not None:
                raise DeclarationError(
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
        basis,
    )


__all__ = [
    "ConstantSymbol",
    "DEFAULT_DECLARATIONS",
    "DerivativeLaw",
    "ElementaryLibrary",
    "FunctionSymbol",
    "build_elementary",
    "default_elementary_declarations",
]
