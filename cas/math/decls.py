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
    """Mathematical function: head name, print name, properties, derivative
    template, and domain-condition template.

    Every field comes from the declaration DSL
    (`math/elementary/declarations.dsl`); this layer holds pure data only.
    `deriv` is a derivative template containing the `DB(0)` placeholder, meaning
    `f'(u) = template[DB(0) := u]`, with the chain-rule factor multiplied in by the
    differentiation layer; a template whose branch splits is None and carries a
    `deriv_note`, since derivative templates are only admitted when unconditionally
    provable. `domain` is a domain-condition template using the same `DB(0)`
    placeholder (None when absent).
    """
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
