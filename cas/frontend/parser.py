"""Runtime-aware frontend wrapper around the pure syntax parser."""

from __future__ import annotations

from typing import Literal, overload

from cas.runtime.runtime import Runtime
from cas.syntax import pattern as P
from cas.syntax.parse import ConstantTable, Parser, ParseValue, tokenize
from cas.syntax.term import Term


@overload
def parse(
    runtime: Runtime,
    text: str,
    pattern: Literal[False] = False,
    constants: ConstantTable | None = None,
) -> Term: ...


@overload
def parse(
    runtime: Runtime,
    text: str,
    pattern: Literal[True],
    constants: ConstantTable | None = None,
) -> P.Pattern: ...


def parse(
    runtime: Runtime,
    text: str,
    pattern: bool = False,
    constants: ConstantTable | None = None,
) -> ParseValue:
    """Parse a surface expression using the explicitly supplied runtime."""
    def alias(name: str) -> str:
        resolved = runtime.alias_head(name)
        return resolved if resolved is not None else name

    def const_atom(name: str) -> Term | None:
        declaration = runtime.const_by_name(name)
        return declaration.atom if declaration is not None else None

    def is_binder(name: str) -> bool:
        return runtime.is_binder(name)

    return Parser[ParseValue](
        tokenize(text),
        pattern=pattern,
        constants=constants,
        alias_fn=alias,
        const_fn=const_atom,
        binder_fn=is_binder,
    ).parse()
