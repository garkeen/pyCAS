"""Immutable assembled mathematical declarations and algorithm configuration."""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass
from types import MappingProxyType
from typing import Mapping, TypeAlias

from cas.math.builder import DecisionStage
from cas.math.decls import ConstantDecl, FunctionDecl, LiftPolicy
from cas.math.domains.base import DomainCatalog, Ring
from cas.math.project import ProjectionLadder
from cas.math.rules import RuleCatalog
from cas.syntax.term import Const, Expr, S, Term, lift
from cas.syntax.termpath import subst

DomainCondition: TypeAlias = Callable[[Expr], tuple[Term, ...]]


def _domain_condition(template: Term) -> DomainCondition:
    """Instantiate a declared ``DB(0)`` domain condition for one call."""

    def condition(call: Expr) -> tuple[Term, ...]:
        if not call.args:
            return ()
        argument = call.args[0]
        placeholder = S("__domain_condition_argument")
        lifted = lift(template, placeholder, 0)
        return (subst(lifted, {placeholder: argument}),)
    return condition


@dataclass(frozen=True, slots=True)
class DeclarationCatalog:
    """Read-only mathematical declarations and all derived lookup indexes."""

    constants: Mapping[str, ConstantDecl]
    constants_by_atom: Mapping[Const, ConstantDecl]
    functions: Mapping[str, FunctionDecl]
    roles: Mapping[str, str]
    lift_policies: Mapping[str, LiftPolicy]
    domain_conditions: Mapping[str, DomainCondition]

    @classmethod
    def from_records(
        cls,
        constants: tuple[ConstantDecl, ...],
        functions: tuple[FunctionDecl, ...],
        roles: Mapping[str, str],
        lift_policies: Mapping[str, LiftPolicy],
    ) -> DeclarationCatalog:
        constant_map = MappingProxyType({record.name: record for record in constants})
        return cls(
            constants=constant_map,
            constants_by_atom=MappingProxyType({
                record.atom: record for record in constants
            }),
            functions=MappingProxyType({record.name: record for record in functions}),
            roles=MappingProxyType(dict(roles)),
            lift_policies=MappingProxyType(dict(lift_policies)),
            domain_conditions=MappingProxyType({
                record.name: _domain_condition(record.domain)
                for record in functions
                if record.domain is not None
            }),
        )

    def const_by_atom(self, atom: Const) -> ConstantDecl | None:
        return self.constants_by_atom.get(atom)

    def const_by_name(self, name: str) -> ConstantDecl | None:
        return self.constants.get(name)

    def is_const_name(self, name: str) -> bool:
        return name in self.constants

    def const_positive(self, atom: Const) -> bool | None:
        declaration = self.const_by_atom(atom)
        return declaration.positive if declaration is not None else None

    def const_real(self, atom: Const) -> bool | None:
        declaration = self.const_by_atom(atom)
        return declaration.real if declaration is not None else None

    def const_bounds(self, atom: Const) -> tuple[int, int] | None:
        declaration = self.const_by_atom(atom)
        return declaration.bounds if declaration is not None else None

    def lookup_function(self, name: str) -> FunctionDecl | None:
        return self.functions.get(name)

    def function_deriv(self, name: str) -> tuple[Term | None, str]:
        declaration = self.functions.get(name)
        if declaration is None:
            return None, ""
        return declaration.deriv, declaration.note

    def all_functions(self) -> tuple[FunctionDecl, ...]:
        return tuple(self.functions.values())

    def role_head(self, role: str) -> str | None:
        return self.roles.get(role)

    def lift_policy(self, head: str) -> LiftPolicy:
        return self.lift_policies.get(head, LiftPolicy.FORBIDDEN)

    def lookup_domain_cond(self, name: str) -> DomainCondition | None:
        return self.domain_conditions.get(name)


@dataclass(frozen=True, slots=True)
class MathContext:
    """The complete immutable math configuration consumed by algorithms."""

    declarations: DeclarationCatalog
    domains: DomainCatalog
    rule_catalog: RuleCatalog
    decision_stages: tuple[DecisionStage, ...]
    projection_ladder: ProjectionLadder

    @property
    def coeff_ring(self) -> Ring:
        """Coefficient ring selected for parameterized projection domains."""
        return self.projection_ladder.coeff_ring

    def const_by_atom(self, atom: Const) -> ConstantDecl | None:
        return self.declarations.const_by_atom(atom)

    def const_by_name(self, name: str) -> ConstantDecl | None:
        return self.declarations.const_by_name(name)

    def is_const_name(self, name: str) -> bool:
        return self.declarations.is_const_name(name)

    def const_positive(self, atom: Const) -> bool | None:
        return self.declarations.const_positive(atom)

    def const_real(self, atom: Const) -> bool | None:
        return self.declarations.const_real(atom)

    def const_bounds(self, atom: Const) -> tuple[int, int] | None:
        return self.declarations.const_bounds(atom)

    def lookup_function(self, name: str) -> FunctionDecl | None:
        return self.declarations.lookup_function(name)

    def function_deriv(self, name: str) -> tuple[Term | None, str]:
        return self.declarations.function_deriv(name)

    def all_functions(self) -> tuple[FunctionDecl, ...]:
        return self.declarations.all_functions()

    def role_head(self, role: str) -> str | None:
        return self.declarations.role_head(role)

    def lift_policy(self, head: str) -> LiftPolicy:
        return self.declarations.lift_policy(head)

    def lookup_domain_cond(self, name: str) -> DomainCondition | None:
        return self.declarations.lookup_domain_cond(name)
