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
The declaration **data types** live in the math layer (`cas.math.decls`), because
"which functions exist and what is true of them" is mathematical semantics; this
module imports them and holds the assembly-time tables.
"""

from cas.math.decls import ConstantDecl, FunctionDecl
from cas.syntax.term import C as _mk_const


class RuntimeBuilder:
    """The set of assembly-time registries. A duplicate declaration raises, since
    one declaration has exactly one home."""

    def __init__(self):
        self.constants: dict[str, ConstantDecl] = {}
        self.functions: dict[str, FunctionDecl] = {}
        self.aliases: dict[str, str] = {}  # surface name -> canonical head
        self.binders: list[str] = []       # canonical heads whose surface word binds a variable
        self.roles: dict[str, str] = {}    # role -> canonical head
        self.lifts: dict[str, str] = {}    # mathematical head -> lift policy
        self.rule_lines: list[str] = []    # rule lines (DSL text; math/rules.py parses)
        self.eq_stages: list = []          # (name, run)
        self.domains: list = []            # resident base field builders (ladder order)
        self.checkers: list = []           # (checker_id, factory) registered by math modules
        self.commands: dict[str, tuple] = {}  # name -> (help, argument kind, checker id)
    #     so adding a module never requires editing a second hardcoded list) ---

    def register_checker(self, checker_id: str, factory) -> None:
        """Register one checker as a **factory** `(math_context) -> checker`.

        A factory rather than a ready instance, because every checker reads
        declarations and therefore needs the math context -- and the context does
        not exist while `install(builder)` runs (assembly order is: every module
        installs, then the context is assembled from what the builder holds).

        A duplicate id raises, matching the duplicate-reject policy of every other
        registry here: a collision between two modules' checker ids is a decision
        that must surface, not one to resolve silently by registration order.
        """
        if any(cid == checker_id for cid, _ in self.checkers):
            raise ValueError(f"checker already registered: {checker_id}")
        self.checkers.append((checker_id, factory))

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
        """Register a role used by an algorithm to fetch a canonical head."""
        if role in self.roles:
            raise ValueError(f"role redeclared: {role}")
        self.roles[role] = head

    def declare_lift(self, head: str, policy: str) -> None:
        if policy not in {"congruent", "conditional", "forbidden"}:
            raise ValueError(f"unknown lift policy: {policy}")
        if head in self.lifts:
            raise ValueError(f"lift policy redeclared: {head}")
        self.lifts[head] = policy

    def declare_binder(self, head: str) -> None:
        """Declare a canonical head as a binder head: its surface word takes the bound
        variable as its second argument and the parser builds the bound form.

        The head is declaration data like an alias, so the syntax layer knows no
        binder by name; a new binder needs a declaration, not a parser change.
        """
        if head in self.binders:
            raise ValueError(f"binder redeclared: {head}")
        self.binders.append(head)

    def declare_rule(self, line: str) -> None:
        """Register the text of one rule DSL line."""
        self.rule_lines.append(line)

    def register_command(self, name: str, help: str, args: str, checker_id: str) -> None:
        if name in self.commands:
            raise ValueError(f"command redeclared: {name}")
        self.commands[name] = (help, args, checker_id)

    def register_eq_stage(self, name, run, prepend=False) -> None:
        entry = (name, run)
        if prepend:
            self.eq_stages.insert(0, entry)
        else:
            self.eq_stages.append(entry)

    def register_domain(self, domain) -> None:
        self.domains.append(domain)
