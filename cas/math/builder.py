"""Consumer-owned contracts for explicit mathematical module assembly."""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass
from typing import TYPE_CHECKING, Protocol, TypeAlias

from cas.kernel.scope import Assumptions
from cas.kernel.verdict import Verdict
from cas.math.decls import ConstantDecl, DeclarationSet
from cas.syntax.term import Term

if TYPE_CHECKING:
    from cas.kernel.evidence import Checker
    from cas.math.context import MathContext
    from cas.math.domains.base import Domain


DecisionStageRunner: TypeAlias = Callable[
    ["MathContext", Term, Term, Term, Assumptions],
    Verdict | None,
]


class CheckerFactory(Protocol):
    """Callable that constructs one context-bound checker."""

    def __call__(self, ctx: MathContext) -> Checker:
        ...


@dataclass(frozen=True, slots=True)
class CheckerRegistration:
    """A checker factory that receives the assembled math context."""

    checker_id: str
    factory: CheckerFactory


@dataclass(frozen=True, slots=True)
class DecisionStage:
    """One named identity-decision stage."""

    name: str
    run: DecisionStageRunner


@dataclass(frozen=True, slots=True)
class CommandSpec:
    """User-visible command metadata supplied by a math module.

    Frontend wiring adds the executable handler later.  Keeping this record free of
    frontend types lets mathematical modules remain independent of the REPL.
    """

    name: str
    help: str
    arguments: str
    checker_id: str | None


class MathBuilder(Protocol):
    """Fixed assembly surface consumed by math modules."""

    def register_declarations(self, declarations: DeclarationSet) -> None:
        """Register one parsed declaration set."""

    def require_constant(self, name: str) -> ConstantDecl:
        """Return an earlier-declared constant or fail assembly."""

    def register_domain(self, domain: Domain) -> None:
        """Register one resident or computation-scoped domain value."""

    def register_checker(self, registration: CheckerRegistration) -> None:
        """Register one checker factory."""

    def register_decision_stage(
        self,
        stage: DecisionStage,
        *,
        prepend: bool = False,
    ) -> None:
        """Register one identity-decision stage."""

    def register_command(self, command: CommandSpec) -> None:
        """Register one user-visible command specification."""
