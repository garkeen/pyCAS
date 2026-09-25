"""Assembly-only math builder and its immutable frozen registration snapshot."""

from __future__ import annotations

from dataclasses import dataclass, replace
from types import MappingProxyType
from typing import Mapping

from cas.math.builder import CheckerRegistration, CommandSpec, DecisionStage
from cas.math.decls import ConstantDecl, DeclarationSet, FunctionDecl, LiftPolicy
from cas.math.domains.base import Domain
from cas.math.rules import RuleCatalog, RuleSet
from cas.syntax.term import Const


@dataclass(frozen=True, slots=True)
class RuntimeAssembly:
    """Read-only registration data frozen at the end of bootstrap."""

    constants: tuple[ConstantDecl, ...]
    functions: tuple[FunctionDecl, ...]
    aliases: Mapping[str, str]
    binders: frozenset[str]
    roles: Mapping[str, str]
    lifts: Mapping[str, LiftPolicy]
    binder_prints: Mapping[str, str]
    rules: RuleCatalog
    decision_stages: tuple[DecisionStage, ...]
    domains: tuple[Domain, ...]
    checkers: tuple[CheckerRegistration, ...]
    commands: Mapping[str, CommandSpec]


class RuntimeBuilder:
    """The sole write surface during explicit mathematical assembly."""

    def __init__(self) -> None:
        self._constants: list[ConstantDecl] = []
        self._constant_names: set[str] = set()
        self._constant_atoms: set[Const] = set()
        self._functions: list[FunctionDecl] = []
        self._function_names: set[str] = set()
        self._aliases: dict[str, str] = {}
        self._binders: set[str] = set()
        self._binder_prints: dict[str, str] = {}
        self._roles: dict[str, str] = {}
        self._lifts: dict[str, LiftPolicy] = {}
        self._rule_set = RuleSet()
        self._decision_stages: list[DecisionStage] = []
        self._stage_names: set[str] = set()
        self._domains: list[Domain] = []
        self._domain_names: set[str] = set()
        self._checkers: list[CheckerRegistration] = []
        self._checker_ids: set[str] = set()
        self._commands: dict[str, CommandSpec] = {}

    def require_constant(self, name: str) -> ConstantDecl:
        for declaration in self._constants:
            if declaration.name == name:
                return declaration
        raise KeyError(f"constant not declared: {name} (check install order)")

    def register_declarations(self, declarations: DeclarationSet) -> None:
        """Register one fully parsed declaration set and validate references."""

        policies = {record.head: record.policy for record in declarations.lifts}
        for constant in declarations.constants:
            if constant.name in self._constant_names:
                raise ValueError(f"constant redeclared: {constant.name}")
            if constant.atom in self._constant_atoms:
                raise ValueError(f"constant atom redeclared: {constant.name}")
            self._constant_names.add(constant.name)
            self._constant_atoms.add(constant.atom)
            self._constants.append(constant)

        for original in declarations.functions:
            if original.name in self._function_names:
                raise ValueError(f"function redeclared: {original.name}")
            function = replace(
                original,
                lift=policies.get(original.name, original.lift),
            )
            self._function_names.add(function.name)
            self._functions.append(function)

        for binder in declarations.binders:
            if binder.head in self._binders:
                raise ValueError(f"binder redeclared: {binder.head}")
            self._binders.add(binder.head)
            if binder.print_name is not None:
                self._binder_prints[binder.head] = binder.print_name
        for alias in declarations.aliases:
            if alias.surface in self._aliases:
                raise ValueError(f"alias redeclared: {alias.surface}")
            self._aliases[alias.surface] = alias.head
        for role in declarations.roles:
            if role.role in self._roles:
                raise ValueError(f"role redeclared: {role.role}")
            self._roles[role.role] = role.head
        for lift in declarations.lifts:
            if lift.head in self._lifts:
                raise ValueError(f"lift policy redeclared: {lift.head}")
            self._lifts[lift.head] = lift.policy
        for rule in declarations.rules:
            self._rule_set.add(rule)

        known_heads = self._function_names | self._binders
        for surface, head in self._aliases.items():
            if head not in known_heads:
                raise ValueError(f"alias {surface!r} targets undeclared head {head!r}")
        for role_name, head in self._roles.items():
            if head not in known_heads:
                raise ValueError(
                    f"role {role_name!r} targets undeclared head {head!r}"
                )
        for head in self._lifts:
            if head not in known_heads:
                raise ValueError(f"lift targets undeclared head {head!r}")
        for head in self._binders:
            if not any(alias_head == head for alias_head in self._aliases.values()):
                raise ValueError(f"binder {head!r} has no declared surface alias")

    def register_domain(self, domain: Domain) -> None:
        if domain.scoped:
            raise ValueError(f"scoped domain cannot be resident: {domain.name}")
        if domain.name in self._domain_names:
            raise ValueError(f"domain redeclared: {domain.name}")
        self._domain_names.add(domain.name)
        self._domains.append(domain)

    def register_checker(self, registration: CheckerRegistration) -> None:
        if registration.checker_id in self._checker_ids:
            raise ValueError(
                f"checker already registered: {registration.checker_id}")
        self._checker_ids.add(registration.checker_id)
        self._checkers.append(registration)

    def register_decision_stage(
        self,
        stage: DecisionStage,
        *,
        prepend: bool = False,
    ) -> None:
        if stage.name in self._stage_names:
            raise ValueError(f"decision stage already registered: {stage.name}")
        self._stage_names.add(stage.name)
        if prepend:
            self._decision_stages.insert(0, stage)
        else:
            self._decision_stages.append(stage)

    def register_command(self, command: CommandSpec) -> None:
        if command.name in self._commands:
            raise ValueError(f"command redeclared: {command.name}")
        self._commands[command.name] = command

    def freeze(self) -> RuntimeAssembly:
        """Return the immutable assembly snapshot consumed by runtime."""

        return RuntimeAssembly(
            constants=tuple(self._constants),
            functions=tuple(self._functions),
            aliases=MappingProxyType(dict(self._aliases)),
            binders=frozenset(self._binders),
            roles=MappingProxyType(dict(self._roles)),
            lifts=MappingProxyType(dict(self._lifts)),
            binder_prints=MappingProxyType(dict(self._binder_prints)),
            rules=RuleCatalog.from_set(self._rule_set),
            decision_stages=tuple(self._decision_stages),
            domains=tuple(self._domains),
            checkers=tuple(self._checkers),
            commands=MappingProxyType(dict(self._commands)),
        )
