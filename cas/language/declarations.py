"""A data-only declaration language for binder and operator signatures.

The first slice covers the two declarations the language layer can consume
directly:

    # comments and blank lines are ignored
    operator Sin (Real) -> Real
    operator pi () -> Real
    binder Lambda (Real) -> function
    binder Integral (Real) -> Real

`function` on a binder marks a function-valued binder: typing yields
`FunctionSort(parameter_sorts, body_sort)`. A concrete result marks a value
binder and the body must embed into it. Nothing here registers truth, rules or
derivative laws; those declarations arrive with their own consumers later.
"""

from __future__ import annotations

import re
from collections.abc import Callable
from dataclasses import dataclass
from pathlib import Path

from cas.foundation.ids import SymbolId
from cas.language import sorts as S
from cas.language.signatures import (
    BindingSignature,
    LanguageSignature,
    OperatorSignature,
    StructuralHead,
)

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
_DECLARATION = re.compile(
    r"(operator|binder)\s+([A-Za-z_][A-Za-z0-9_]*)\s*"
    r"\(([^)]*)\)\s*->\s*(\S+)\s*\Z"
)


class DeclarationError(Exception):
    """A declaration line cannot be admitted."""

    def __init__(self, message: str, line: int) -> None:
        super().__init__(f"line {line}: {message}")
        self.message = message
        self.line = line


@dataclass(frozen=True, slots=True)
class OperatorDeclaration:
    """A declared function or constant symbol."""

    name: str
    arguments: tuple[S.Sort, ...]
    result: S.Sort


@dataclass(frozen=True, slots=True)
class BinderDeclaration:
    """A declared binding form.

    `result=None` means function-valued; a concrete sort means the binder
    denotes a value of that sort.
    """

    name: str
    parameter_sorts: tuple[S.Sort, ...]
    result: S.Sort | None

    @property
    def arity(self) -> int:
        return len(self.parameter_sorts)


@dataclass(frozen=True, slots=True)
class DeclarationSet:
    """The admitted declarations, in file order."""

    operators: tuple[OperatorDeclaration, ...]
    binders: tuple[BinderDeclaration, ...]


def _parse_sort(text: str, line: int) -> S.Sort:
    sort = sort_from_name(text)
    if sort is None:
        raise DeclarationError(f"unknown sort {text!r}", line)
    return sort


def sort_from_name(name: str) -> S.Sort | None:
    """The declared sort called `name`, or None when the language has none."""
    return _SORTS.get(name)


def _parse_parameters(text: str, line: int) -> tuple[S.Sort, ...]:
    stripped = text.strip()
    if not stripped:
        return ()
    parts = [part.strip() for part in stripped.split(",")]
    if any(not part for part in parts):
        raise DeclarationError("empty parameter sort", line)
    return tuple(_parse_sort(part, line) for part in parts)


def load_declarations(text: str) -> DeclarationSet:
    """Parse declaration text; no file access and no registration."""
    operators: list[OperatorDeclaration] = []
    binders: list[BinderDeclaration] = []
    seen: set[str] = set()
    for number, raw in enumerate(text.splitlines(), start=1):
        line = raw.split("#", 1)[0].strip()
        if not line:
            continue
        match = _DECLARATION.fullmatch(line)
        if match is None:
            raise DeclarationError(
                "expected 'operator NAME (SORTS) -> SORT' or "
                "'binder NAME (SORTS) -> function|SORT'",
                number,
            )
        kind, name, parameters_text, result_text = match.groups()
        if name in _RESERVED_HEADS:
            raise DeclarationError(
                f"{name!r} is a structural head name", number
            )
        if name in seen:
            raise DeclarationError(f"duplicate declaration {name!r}", number)
        seen.add(name)
        parameters = _parse_parameters(parameters_text, number)
        if kind == "binder":
            if not parameters:
                raise DeclarationError(
                    "a binder needs at least one parameter sort", number
                )
            result = (
                None
                if result_text == "function"
                else _parse_sort(result_text, number)
            )
            binders.append(BinderDeclaration(name, parameters, result))
        else:
            if result_text == "function":
                raise DeclarationError(
                    "an operator cannot be function-valued", number
                )
            operators.append(
                OperatorDeclaration(
                    name,
                    parameters,
                    _parse_sort(result_text, number),
                )
            )
    return DeclarationSet(tuple(operators), tuple(binders))


def load_declarations_file(path: str | Path) -> DeclarationSet:
    """Read and parse a declaration file."""
    return load_declarations(Path(path).read_text(encoding="utf-8"))


def build_language(
    intern: Callable[[str], SymbolId],
    declarations: DeclarationSet,
) -> LanguageSignature:
    """Build a language signature from names and declarations.

    `intern` is the session name table's intern function; this function owns no
    global registry and performs no import-time work.
    """
    heads = {intern(head.value): head for head in StructuralHead}
    operators: dict[SymbolId, OperatorSignature] = {}
    for operator in declarations.operators:
        if operator.name in _RESERVED_HEADS:
            raise ValueError(f"{operator.name!r} is a structural head name")
        operators[intern(operator.name)] = OperatorSignature(
            operator.arguments, operator.result
        )
    binders = {
        binder.name: BindingSignature(
            binder.name,
            binder.arity,
            binder.parameter_sorts,
            binder.result,
        )
        for binder in declarations.binders
    }
    return LanguageSignature.build(heads, binders, operators)


__all__ = [
    "BinderDeclaration",
    "DeclarationError",
    "DeclarationSet",
    "OperatorDeclaration",
    "build_language",
    "load_declarations",
    "load_declarations_file",
    "sort_from_name",
]
