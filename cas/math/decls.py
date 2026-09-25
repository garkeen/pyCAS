"""Immutable mathematical declaration records and assembled declaration sets."""

from __future__ import annotations

from dataclasses import dataclass
from enum import StrEnum
from fractions import Fraction
from typing import TYPE_CHECKING

from cas.syntax.term import Const, Term

if TYPE_CHECKING:
    from cas.math.rules import Rule


@dataclass(frozen=True, slots=True)
class ConstantDecl:
    """A mathematical constant and the coarse facts declared for it."""

    atom: Const
    name: str
    print_name: str
    real: bool | None = None
    positive: bool | None = None
    bounds: tuple[int, int] | None = None


class LiftPolicy(StrEnum):
    """How a declared mathematical head participates in equality lifting."""

    CONGRUENT = "congruent"
    CONDITIONAL = "conditional"
    FORBIDDEN = "forbidden"


@dataclass(frozen=True, slots=True)
class FunctionDecl:
    """A declared mathematical function and its admitted properties."""

    name: str
    print_name: str
    arity: int
    real_on_real: bool | None = None
    bound: tuple[Fraction | None, Fraction | None] | None = None
    zero_iff_arg_zero: bool = False
    deriv: Term | None = None
    domain: Term | None = None
    note: str = ""
    lift: LiftPolicy = LiftPolicy.FORBIDDEN


@dataclass(frozen=True, slots=True)
class AliasDecl:
    surface: str
    head: str


@dataclass(frozen=True, slots=True)
class BinderDecl:
    """A binder head plus its optional display symbol (declared surface data)."""

    head: str
    print_name: str | None = None


@dataclass(frozen=True, slots=True)
class RoleDecl:
    role: str
    head: str


@dataclass(frozen=True, slots=True)
class LiftDecl:
    head: str
    policy: LiftPolicy


@dataclass(frozen=True, slots=True)
class DeclarationSet:
    """All records parsed from one declaration DSL document."""

    constants: tuple[ConstantDecl, ...]
    functions: tuple[FunctionDecl, ...]
    aliases: tuple[AliasDecl, ...]
    binders: tuple[BinderDecl, ...]
    roles: tuple[RoleDecl, ...]
    lifts: tuple[LiftDecl, ...]
    rules: tuple[Rule, ...]
