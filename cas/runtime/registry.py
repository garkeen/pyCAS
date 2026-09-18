# -*- coding: utf-8 -*-
"""Assembly-time registry (`RuntimeBuilder`).

`RuntimeBuilder` is the **only write entry during assembly**: math modules register
their declarations inside their own `install(builder)`, and once assembly finishes
`Runtime` freezes it into a read-only snapshot.

**Only categories with actual content get a table.** A registry that is always empty
is a husk, so the builder holds only what is really used today: constants, function
declarations, domain conditions, identity-decision stages, and domain builders.
Rules are assembled by `math/rules.py` from function declarations, and checkers are
owned by the kernel's CheckerRegistry, so neither is duplicated here; a table gets
added when it has content.

**No import-time global state mutation**: this module writes to the builder only
when explicitly called, and math modules register nothing on import. Assembly is
triggered explicitly by `bootstrap()`.
"""

from dataclasses import dataclass
from fractions import Fraction

from cas.syntax.term import C as _mk_const
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


class RuntimeBuilder:
    """The set of assembly-time registries. A duplicate declaration raises, since
    one declaration has exactly one home."""

    def __init__(self):
        self.constants: dict[str, ConstantDecl] = {}
        self.functions: dict[str, FunctionDecl] = {}
        self.aliases: dict[str, str] = {}  # surface name -> canonical head (parser notation)
        self.roles: dict[str, str] = {}    # role -> canonical head (algorithms fetch by role)
        self.rule_lines: list[str] = []    # rule lines (DSL text; math/rules.py parses)
        self.eq_stages: list = []          # (name, run)
        self.domains: list = []            # resident base field builders (ladder order)
        self.checkers: list = []           # (checker_id, checker) installed by math modules

    # --- checkers (a math module's install registers its own checkers here,
    #     so adding a module never requires editing a second hardcoded list) ---

    def register_checker(self, checker_id: str, checker) -> None:
        """Register one checker. A duplicate id raises, matching the
        duplicate-reject policy of every other registry here: a collision
        between two modules' checker ids is a decision that must surface, not
        one to resolve silently by registration order."""
        if any(cid == checker_id for cid, _ in self.checkers):
            raise ValueError(f"checker already registered: {checker_id}")
        self.checkers.append((checker_id, checker))

    # --- constants ---

    def declare_constant(self, *, name, print_name, real=None, positive=None,
                         bounds=None) -> ConstantDecl:
        return self.register_constant(ConstantDecl(
            atom=_mk_const(name), name=name, print_name=print_name,
            real=real, positive=positive, bounds=bounds))

    def register_constant(self, decl: ConstantDecl) -> ConstantDecl:
        if decl.name in self.constants:
            raise ValueError(f"constant redeclared: {decl.name}")
        self.constants[decl.name] = decl
        return decl

    def require_constant(self, name) -> ConstantDecl:
        """Fetch an already-declared constant; a miss raises, which makes the
        assembly-order dependency explicit."""
        d = self.constants.get(name)
        if d is None:
            raise KeyError(f"constant not declared: {name} (check install order)")
        return d

    # --- functions ---

    def declare_function(self, **kw) -> FunctionDecl:
        return self.register_function(FunctionDecl(**kw))

    def register_function(self, decl: FunctionDecl) -> FunctionDecl:
        if decl.name in self.functions:
            raise ValueError(f"function redeclared: {decl.name}")
        self.functions[decl.name] = decl
        return decl

    # --- aliases / rules / decision stages / domains ---

    def declare_alias(self, surface: str, head: str) -> None:
        """Parser surface name -> canonical head (e.g. ln->Log, sqrt->Sqrt).

        An alias is a **declaration**, not parser hardcoding: a different surface
        name needs no parser change.
        """
        if surface in self.aliases:
            raise ValueError(f"alias redeclared: {surface}")
        self.aliases[surface] = head

    def declare_role(self, role: str, head: str) -> None:
        """Canonical function an algorithm refers to by role (e.g. `logarithm` -> Log).

        The general power rule of differentiation needs "the logarithm function" but
        must not hardcode `Log`; it fetches by **declared role**, so renaming the
        function needs no algorithm change.
        """
        if role in self.roles:
            raise ValueError(f"role redeclared: {role}")
        self.roles[role] = head

    def declare_rule(self, line: str) -> None:
        """Register the **text** of one rule DSL line (parsing happens at the
        consumption point in math/rules.py).

        A rule is data, not a Python registration call, so the admission discipline
        (unconditional identity, no guard on auto) can be checked mechanically
        against the text.
        """
        self.rule_lines.append(line)

    def register_eq_stage(self, name, run, prepend=False) -> None:
        entry = (name, run)
        if prepend:
            self.eq_stages.insert(0, entry)
        else:
            self.eq_stages.append(entry)

    def register_domain(self, domain) -> None:
        self.domains.append(domain)
