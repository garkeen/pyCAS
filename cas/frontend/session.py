"""Explicit frontend session state and command bindings."""

from __future__ import annotations

from collections.abc import Callable, Mapping
from dataclasses import dataclass
from types import MappingProxyType
from typing import TypeAlias

from cas.runtime.runtime import Runtime
from cas.workflow.branch import BranchGroup
from cas.workflow.workflow import Workflow

CommandHandler: TypeAlias = Callable[["Session", str], None]


@dataclass(frozen=True, slots=True)
class CommandDescriptor:
    """Complete frontend command metadata and its executable handler."""

    name: str
    help: str
    arguments: str
    checker_id: str | None
    handler: CommandHandler


class Session:
    """One isolated frontend conversation bound to one runtime.

    Handler wiring is part of session construction. A runtime supplies command
    specifications; this class pairs each one with its frontend callable and
    rejects an incomplete or over-complete table before the session is usable.
    """

    def __init__(
        self,
        runtime: Runtime,
        handlers: Mapping[str, CommandHandler],
    ) -> None:
        self.runtime = runtime
        expected = set(runtime.commands)
        actual = set(handlers)
        missing = sorted(expected - actual)
        extra = sorted(actual - expected)
        if missing or extra:
            details: list[str] = []
            if missing:
                details.append("missing=" + ",".join(missing))
            if extra:
                details.append("extra=" + ",".join(extra))
            raise ValueError("command handler table mismatch: " + "; ".join(details))
        invalid = sorted(
            name for name, handler in handlers.items() if not callable(handler)
        )
        if invalid:
            raise TypeError("command handler is not callable: " + ",".join(invalid))

        bound = {
            name: CommandDescriptor(
                name=spec.name,
                help=spec.help,
                arguments=spec.arguments,
                checker_id=spec.checker_id,
                handler=handlers[name],
            )
            for name, spec in sorted(runtime.commands.items())
        }
        self._commands: Mapping[str, CommandDescriptor] = MappingProxyType(bound)
        self.workflow: Workflow = runtime.new_workflow()
        self.focus: int | None = None
        self.branch_group: BranchGroup | None = None

    @property
    def commands(self) -> Mapping[str, CommandDescriptor]:
        return self._commands

    def handler(self, name: str) -> CommandHandler | None:
        command = self._commands.get(name)
        return None if command is None else command.handler
