# -*- coding: utf-8 -*-
"""The explicit math context: the declaration query surface plus the configuration
assembly hands to the algorithms.

Two parts, both produced by `bootstrap()`:

· the **declaration query surface** -- constants and their declared properties,
  function declarations (arity, derivative template, domain-condition template),
  declared roles, and the rule-line texts of the declaration DSL;
· the **assembly-provided configuration** -- the identity-decision stages, the
  projection ladder, and the default coefficient ring of the parameterized
  domains (the K in K[x] / K(x)).

Nothing keeps this in module-level state and no algorithm reads it implicitly: a
function that needs it takes it as its first parameter. A module-level handle
filled in at assembly time turns "forgot to assemble" into a run-time surprise
somewhere deep inside an algorithm, whereas an explicit parameter makes the call
impossible to write without one. Querying an undeclared name still returns None:
"no such name" is a different case from "not assembled", and only the former
belongs to this layer.
"""

from dataclasses import dataclass, field
from types import MappingProxyType
from typing import Mapping

from cas.syntax.term import lift


def _domain_condition_callable(template):
    """Domain-condition template -> callable `fn(call) -> [condition terms]`.

    The template contains the `DB(0)` placeholder (the function argument slot) and
    is instantiated through the syntax layer's `lift` -- the same de Bruijn
    mechanism as derivative templates, not a second substitution scheme.
    """
    def cond(t):
        return [lift(template, t.args[0], 0)]

    return cond


@dataclass(frozen=True, slots=True)
class MathContext:
    """Declarations and assembly configuration, read through explicit parameters.

    `consts` / `funcs` / `roles` / `rule_lines` carry the declarations; the
    identity-decision stages, the projection ladder and the coefficient ring are
    the configuration the projection layer computes during assembly. The two
    indexes are derived here once, in `__post_init__`, so a context built by hand
    (a test assembling its own ladder, say) is indexed exactly like one built by
    `bootstrap()`.
    """

    consts: Mapping = field(default_factory=dict)      # name -> ConstantDecl
    funcs: Mapping = field(default_factory=dict)       # name -> FunctionDecl
    roles: Mapping = field(default_factory=dict)       # role -> canonical head
    rule_lines: tuple = ()                             # declaration DSL texts
    eq_stages: tuple = ()                              # (name, run) identity-decision stages
    projection_stages: tuple = ()                      # ProjectionStage rungs, in order
    coeff_ring: object = None                          # K of K[x] / K(x)
    _by_atom: Mapping = field(default=None, repr=False, compare=False)
    _domain_conds: Mapping = field(default=None, repr=False, compare=False)

    def __post_init__(self):
        object.__setattr__(self, "consts", MappingProxyType(dict(self.consts)))
        object.__setattr__(self, "funcs", MappingProxyType(dict(self.funcs)))
        object.__setattr__(self, "roles", MappingProxyType(dict(self.roles)))
        object.__setattr__(self, "rule_lines", tuple(self.rule_lines))
        object.__setattr__(self, "eq_stages", tuple(self.eq_stages))
        object.__setattr__(self, "projection_stages", tuple(self.projection_stages))
        if self._by_atom is None:
            object.__setattr__(self, "_by_atom", MappingProxyType(
                {id(d.atom): d for d in self.consts.values()}))
        if self._domain_conds is None:
            object.__setattr__(self, "_domain_conds", MappingProxyType({
                name: _domain_condition_callable(d.domain)
                for name, d in self.funcs.items() if d.domain is not None}))

    # --- constants ---

    def const_by_atom(self, atom):
        return self._by_atom.get(id(atom))

    def const_by_name(self, name: str):
        return self.consts.get(name)

    def is_const_name(self, name: str) -> bool:
        return name in self.consts

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
        return self.funcs.get(name)

    def function_deriv(self, name: str):
        d = self.funcs.get(name)
        return (None, "") if d is None else (d.deriv, d.deriv_note)

    def all_functions(self) -> tuple:
        return tuple(self.funcs.values())

    # --- roles / domain conditions / rules ---

    def role_head(self, role: str):
        """Role -> canonical head (None when absent). Algorithms fetch by role and
        never hardcode a function name."""
        return self.roles.get(role)

    def lookup_domain_cond(self, name: str):
        return self._domain_conds.get(name)

    @property
    def rules(self) -> tuple:
        """Rule DSL line texts (parsed at the consumption point in math/rules.py).
        Rules are data."""
        return self.rule_lines
