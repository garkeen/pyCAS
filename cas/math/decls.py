"""Declaration data types: the shape of what the declaration DSL produces.

A declaration is **data**, not behaviour: a constant declares its atom and the
decidable properties it carries lemata for, a function declares its head, print
name, arity, properties, derivative template and domain-condition template. The
admission discipline (what may be declared) is checked mechanically against the
DSL text, and the assembly-time builder holds the declaration tables.

These types live in the math layer because they are mathematical semantics --
"which functions exist and what is true of them" belongs to `math/*`, and the
runtime layer composes them into its own registry.
"""

from dataclasses import dataclass
from fractions import Fraction

from cas.syntax.term import Const


@dataclass(frozen=True, slots=True)
class ConstantDecl:
    """Mathematical constant: the atom plus lemma declarations for decidable
    properties."""
    atom: Const
    name: str
    print_name: str
    real: bool | None = None
    positive: bool | None = None
    bounds: tuple[int, int] | None = None


@dataclass(frozen=True, slots=True)
class FunctionDecl:
    """A declared mathematical function and its registered properties."""

    name: str
    print_name: str
    arity: int | None
    real_on_real: bool | None = None
    bound: tuple[Fraction | None, Fraction | None] | None = None
    zero_iff_arg_zero: bool = False
    deriv: object = None
    domain: object = None
    deriv_note: str = ""
    note: str = ""
    lift: str = "forbidden"
