# -*- coding: utf-8 -*-
"""`Runtime`: the read-only query surface once assembly is complete.

It exposes print names, positivity, coarse bounds, derivative templates, domain
conditions, and the function list -- every read-only exit for math semantics.
The only write entry is `RuntimeBuilder` (during assembly); there is no runtime
write path.

Consumers (parser / pprint / decide / project / rules / domcond / diff ...) receive
`None` for an unknown name and degrade on their own -- **no semantic fallback**,
this layer never guesses.
"""

from cas.syntax.term import Const


def _domain_callable(template):
    """Domain-condition template -> callable `fn(call) -> [condition terms]`.

    The template contains the `DB(0)` placeholder (the function argument slot) and
    is instantiated through the syntax layer's `_lift` -- the same de Bruijn
    mechanism as derivative templates, not a second substitution scheme.
    """
    from cas.syntax.term import _lift

    def cond(t):
        return [_lift(template, t.args[0], 0)]

    return cond


class Runtime:
    """Read-only snapshot. It does not change after construction, and construction
    happens only in bootstrap."""

    def __init__(self, builder):
        self._consts = dict(builder.constants)
        self._funcs = dict(builder.functions)
        self._aliases = dict(builder.aliases)
        self._roles = dict(builder.roles)
        self._rule_lines = tuple(builder.rule_lines)
        self._eq_stages = tuple(builder.eq_stages)
        self._domains = tuple(builder.domains)
        self._by_atom = {id(d.atom): d for d in self._consts.values()}
        # Domain conditions come from each function declaration's domain template
        # (DSL) and are instantiated on demand: the condition of f(u) is
        # template[DB(0) := u], the same de Bruijn mechanism as derivative templates.
        self._domain_conds = {
            name: _domain_callable(d.domain)
            for name, d in self._funcs.items() if d.domain is not None
        }

    # --- constants ---

    def const_by_atom(self, atom: Const):
        return self._by_atom.get(id(atom))

    def const_by_name(self, name: str):
        return self._consts.get(name)

    def is_const_name(self, name: str) -> bool:
        return name in self._consts

    def const_positive(self, atom):
        d = self.const_by_atom(atom)
        return d.positive if d else None

    def const_real(self, atom):
        d = self.const_by_atom(atom)
        return d.real if d else None

    def const_bounds(self, atom):
        d = self.const_by_atom(atom)
        return d.bounds if d else None

    # --- functions ---

    def lookup_function(self, name: str):
        return self._funcs.get(name)

    def function_deriv(self, name: str):
        d = self._funcs.get(name)
        return (None, "") if d is None else (d.deriv, d.deriv_note)

    def all_functions(self) -> tuple:
        return tuple(self._funcs.values())

    def print_name(self, head_name: str):
        """Display name: constants by internal name, functions by head name (the
        two namespaces do not overlap)."""
        c = self._consts.get(head_name)
        if c is not None:
            return c.print_name
        d = self._funcs.get(head_name)
        return d.print_name if d else None

    # --- domain conditions / decision stages / domains ---

    def lookup_domain_cond(self, name: str):
        return self._domain_conds.get(name)

    def alias_head(self, surface: str):
        """Surface name -> canonical head (None when absent). Parser aliases are
        declaration data."""
        return self._aliases.get(surface)

    def role_head(self, role: str):
        """Role -> canonical head (None when absent). Algorithms fetch by role and
        never hardcode a function name."""
        return self._roles.get(role)

    @property
    def rules(self) -> tuple:
        """Rule DSL line texts (parsed at the consumption point in math/rules.py).
        Rules are data."""
        return self._rule_lines

    @property
    def eq_stages(self) -> tuple:
        return self._eq_stages

    @property
    def domains(self) -> tuple:
        return self._domains

    def stats(self):
        return {"constants": len(self._consts), "functions": len(self._funcs),
                "aliases": len(self._aliases),
                "rules": len(self._rule_lines),
                "domain_conds": len(self._domain_conds),
                "eq_stages": len(self._eq_stages),
                "domains": len(self._domains)}


# ---------------------------------------------------------------------------
# Session assembly: checkers and decision services are injected by this layer
# (the workflow does not depend on cas.math)
# ---------------------------------------------------------------------------

def register_math_checkers(store) -> None:
    """Register each math module's checkers into the ledger."""
    from cas.math.base import checkers as base_c
    from cas.math.calculus.differentiation import checkers as diff_c
    from cas.math.calculus.integration import checkers as int_c
    from cas.math.solving.equations import checkers as eq_c
    for m in (base_c, diff_c, int_c, eq_c):
        m.register(store)


def new_workflow(**kw):
    """Build a workflow session: ledger + kernel checkers + math checkers +
    decision services.

    The workflow never imports `cas.math`, so checkers and decision services **must
    be injected by this layer**. That also makes "the workflow does not know which
    checkers it has" a structural fact rather than a convention.
    """
    from cas.kernel.services import register_core_checkers
    from cas.kernel.store import KernelStore
    from cas.runtime.algorithms import Algorithms
    from cas.runtime.services import ScopeServices
    from cas.workflow.workflow import Workflow

    store = kw.pop("store", None)
    if store is None:
        store = KernelStore()
    register_core_checkers(store)
    register_math_checkers(store)
    return Workflow(store=store, services=ScopeServices(store.scopes),
                    algorithms=Algorithms(), **kw)
