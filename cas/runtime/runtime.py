"""Immutable assembled runtime query surface and workflow construction."""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING, Mapping

from cas.kernel.commit import GuardPolicy
from cas.kernel.evidence import Checker
from cas.kernel.mode import ExecutionMode
from cas.kernel.store import KernelStore
from cas.math.builder import CommandSpec, DecisionStage
from cas.math.context import DomainCondition, MathContext
from cas.math.decls import ConstantDecl, FunctionDecl
from cas.math.domains.base import Domain
from cas.math.rules import RuleCatalog
from cas.runtime.registry import RuntimeAssembly
from cas.syntax.term import Const, Term

if TYPE_CHECKING:
    from cas.workflow.workflow import Workflow


@dataclass(frozen=True, slots=True)
class RuntimeStats:
    """Stable typed snapshot of assembled registration counts."""

    constants: int
    functions: int
    aliases: int
    binders: int
    rules: int
    domain_conditions: int
    decision_stages: int
    domains: int
    checkers: int
    commands: int


class Runtime:
    """Read-only runtime assembled by one explicit bootstrap call."""

    def __init__(self, assembly: RuntimeAssembly, math: MathContext) -> None:
        self._assembly = assembly
        self._math = math
        self._aliases = assembly.aliases
        self._binders = assembly.binders
        self._binder_prints = assembly.binder_prints
        self._checkers = tuple(
            (registration.checker_id, registration.factory(math))
            for registration in assembly.checkers
        )

    @property
    def math(self) -> MathContext:
        """The assembled mathematical context."""
        return self._math

    def const_by_atom(self, atom: Const) -> ConstantDecl | None:
        return self._math.const_by_atom(atom)

    def const_by_name(self, name: str) -> ConstantDecl | None:
        return self._math.const_by_name(name)

    def is_const_name(self, name: str) -> bool:
        return self._math.is_const_name(name)

    def const_positive(self, atom: Const) -> bool | None:
        return self._math.const_positive(atom)

    def const_real(self, atom: Const) -> bool | None:
        return self._math.const_real(atom)

    def const_bounds(self, atom: Const) -> tuple[int, int] | None:
        return self._math.const_bounds(atom)

    def lookup_function(self, name: str) -> FunctionDecl | None:
        return self._math.lookup_function(name)

    def function_deriv(self, name: str) -> tuple[Term | None, str]:
        return self._math.function_deriv(name)

    def all_functions(self) -> tuple[FunctionDecl, ...]:
        return self._math.all_functions()

    def print_name(self, head_name: str) -> str | None:
        constant = self._math.const_by_name(head_name)
        if constant is not None:
            return constant.print_name
        function = self._math.lookup_function(head_name)
        return function.print_name if function is not None else None

    def lookup_domain_cond(self, name: str) -> DomainCondition | None:
        return self._math.lookup_domain_cond(name)

    def alias_head(self, surface: str) -> str | None:
        return self._aliases.get(surface)

    def is_binder(self, head_name: str) -> bool:
        return head_name in self._binders

    def role_head(self, role: str) -> str | None:
        return self._math.role_head(role)

    @property
    def rules(self) -> RuleCatalog:
        return self._assembly.rules

    def binder_print(self, head_name: str) -> str | None:
        """The declared display symbol of a binder head, if one is declared."""
        return self._binder_prints.get(head_name)

    @property
    def decision_stages(self) -> tuple[DecisionStage, ...]:
        return self._assembly.decision_stages

    @property
    def domains(self) -> tuple[Domain, ...]:
        return self._assembly.domains

    @property
    def checkers(self) -> tuple[tuple[str, Checker], ...]:
        return self._checkers

    @property
    def commands(self) -> Mapping[str, CommandSpec]:
        return self._assembly.commands

    def stats(self) -> RuntimeStats:
        return RuntimeStats(
            constants=len(self._assembly.constants),
            functions=len(self._assembly.functions),
            aliases=len(self._aliases),
            binders=len(self._binders),
            rules=len(self._assembly.rules.rules),
            domain_conditions=len(self._math.declarations.domain_conditions),
            decision_stages=len(self._assembly.decision_stages),
            domains=len(self._assembly.domains),
            checkers=len(self._checkers),
            commands=len(self._assembly.commands),
        )

    def new_workflow(
        self,
        *,
        store: KernelStore | None = None,
        mode: ExecutionMode | None = None,
        policy: GuardPolicy | None = None,
    ) -> Workflow:
        """Create a workflow bound to this runtime and its checker registry."""
        from cas.kernel.services import register_core_checkers
        from cas.runtime.algorithms import Algorithms
        from cas.runtime.services import ScopeServices
        from cas.workflow.workflow import Workflow

        kernel_store = KernelStore() if store is None else store
        register_core_checkers(kernel_store)
        for checker_id, checker in self.checkers:
            kernel_store.checkers.register(checker_id, checker)
        return Workflow(
            store=kernel_store,
            services=ScopeServices(kernel_store.scopes, self.math),
            algorithms=Algorithms(self.math),
            mode=mode,
            policy=policy,
        )


def new_workflow(
    runtime: Runtime,
    *,
    store: KernelStore | None = None,
    mode: ExecutionMode | None = None,
    policy: GuardPolicy | None = None,
) -> Workflow:
    """Module-level explicit constructor retained as a static function."""
    return runtime.new_workflow(store=store, mode=mode, policy=policy)
