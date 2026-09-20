# -*- coding: utf-8 -*-
"""`Runtime`: the read-only query surface once assembly is complete.

It composes the math context (the declaration query surface plus the
assembly-computed configuration) with what only this layer needs: surface names
for the parser, print names for the printer, the binder heads, the resident
domains, and the checkers the math modules registered as factories.

Consumers (parser / pprint / decide / project / rules / domcond / diff ...)
receive `None` for an unknown name and degrade on their own -- **no semantic
fallback**, this layer never guesses. The declaration surface itself is reachable
as `Runtime.math` and is passed explicitly to every algorithm that needs it, so
no module depends on a handle that assembly fills in behind its back.
"""

from cas.syntax.term import Const
from cas.math.context import MathContext


class Runtime:
    """Read-only snapshot. It does not change after construction, and construction
    happens only in bootstrap."""

    def __init__(self, builder, math: MathContext):
        self._math = math
        self._aliases = dict(builder.aliases)
        self._binders = frozenset(builder.binders)
        self._domains = tuple(builder.domains)
        # A checker reads declarations and therefore needs the math context, which
        # does not exist while `install(builder)` runs; modules therefore register a
        # factory and the context is supplied here -- the single point where
        # checkers meet declarations.
        self._checkers = tuple((cid, factory(math))
                               for cid, factory in builder.checkers)

    @property
    def math(self) -> MathContext:
        """The declaration query surface and the assembly configuration."""
        return self._math

    # --- constants (the context owns the data, this layer owns the surface) ---

    def const_by_atom(self, atom: Const):
        return self._math.const_by_atom(atom)

    def const_by_name(self, name: str):
        return self._math.const_by_name(name)

    def is_const_name(self, name: str) -> bool:
        return self._math.is_const_name(name)

    def const_positive(self, atom):
        return self._math.const_positive(atom)

    def const_real(self, atom):
        return self._math.const_real(atom)

    def const_bounds(self, atom):
        return self._math.const_bounds(atom)

    # --- functions ---

    def lookup_function(self, name: str):
        return self._math.lookup_function(name)

    def function_deriv(self, name: str):
        return self._math.function_deriv(name)

    def all_functions(self) -> tuple:
        return self._math.all_functions()

    def print_name(self, head_name: str):
        """Display name: constants by internal name, functions by head name (the
        two namespaces do not overlap)."""
        c = self._math.const_by_name(head_name)
        if c is not None:
            return c.print_name
        d = self._math.lookup_function(head_name)
        return d.print_name if d else None

    # --- domain conditions / decision stages / domains ---

    def lookup_domain_cond(self, name: str):
        return self._math.lookup_domain_cond(name)

    def alias_head(self, surface: str):
        """Surface name -> canonical head (None when absent). Parser aliases are
        declaration data."""
        return self._aliases.get(surface)

    def is_binder(self, head_name: str) -> bool:
        """Whether a canonical head is a declared binder head.

        The parser resolves a surface word through the alias table and then asks
        this question, so a bound form (integrate/sum/product/limit and the
        definite integral) comes from declarations rather than from a parser table.
        """
        return head_name in self._binders

    def role_head(self, role: str):
        """Role -> canonical head (None when absent). Algorithms fetch by role and
        never hardcode a function name."""
        return self._math.role_head(role)

    @property
    def rules(self) -> tuple:
        """Rule DSL line texts (parsed at the consumption point in math/rules.py).
        Rules are data."""
        return self._math.rules

    @property
    def eq_stages(self) -> tuple:
        return self._math.eq_stages

    @property
    def domains(self) -> tuple:
        return self._domains

    @property
    def checkers(self) -> tuple:
        """The (checker_id, checker) pairs each math module registered through
        its `install(builder)`. Pulled into a session's checker store by
        `new_workflow`, so a new module adds checkers in exactly one place
        (its own install) rather than in a second hardcoded list."""
        return self._checkers

    def stats(self):
        return {"constants": len(self._math.consts),
                "functions": len(self._math.funcs),
                "aliases": len(self._aliases), "binders": len(self._binders),
                "rules": len(self._math.rule_lines),
                "domain_conds": len(self._math._domain_conds),
                "eq_stages": len(self._math.eq_stages),
                "domains": len(self._domains),
                "checkers": len(self._checkers)}


# ---------------------------------------------------------------------------
# Session assembly: checkers and decision services are injected by this layer
# (the workflow does not depend on cas.math)
# ---------------------------------------------------------------------------

def new_workflow(**kw):
    """Build a workflow session: ledger + kernel checkers + math checkers +
    decision services.

    The workflow never imports `cas.math`, so checkers and decision services must
    be injected by this layer. The math checkers come from the assembled runtime
    (each math module registered its own checkers through `install(builder)`), so
    "which checkers exist" is read from the runtime snapshot rather than from a
    hardcoded module list here.

    Assembly is guaranteed: the runtime is taken from the installed one, so
    constructing a workflow requires an application that assembled explicitly.
    """
    from cas.runtime.dispatch import get_runtime
    rt = get_runtime()
    from cas.kernel.services import register_core_checkers
    from cas.kernel.store import KernelStore
    from cas.runtime.algorithms import Algorithms
    from cas.runtime.services import ScopeServices
    from cas.workflow.workflow import Workflow

    store = kw.pop("store", None)
    if store is None:
        store = KernelStore()
    register_core_checkers(store)
    for checker_id, checker in rt.checkers:
        store.checkers.register(checker_id, checker)
    return Workflow(store=store, services=ScopeServices(store.scopes, rt.math),
                    algorithms=Algorithms(rt.math), **kw)
