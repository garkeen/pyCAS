"""Session: one conversation over one runtime and workspace.

The session owns presentation labels and focus. It never decides mathematics:
every answer comes from the workspace, which in turn commits only through the
kernel. Undo and redo move the visible revision; the ledger is untouched.
"""

from __future__ import annotations

import re
from typing import TYPE_CHECKING, Any

from cas.foundation.ids import ObjectVersionId
from cas.frontend.errors import SessionError
from cas.frontend.parser import parse
from cas.frontend.pprint import to_str
from cas.syntax import term as T
from cas.workflow.records import DerivativeResult, Expression, OperationStatus
from cas.workflow.workspace import Workspace

if TYPE_CHECKING:
    from cas.runtime.bootstrap import Runtime

_LABEL = re.compile(r"[A-Za-z_][A-Za-z0-9_]*\Z")
_ASSIGNMENT = re.compile(
    r"expr(?:\s+([A-Za-z_][A-Za-z0-9_]*))?\s*:=\s*(.+)\Z"
)

_HELP = """commands:
  <expression>          store an expression object
  expr LABEL := EXPR    store an expression object with a label
  diff [@LABEL]         differentiate the focused or named expression
  show [@LABEL]         show an expression
  list                  list the visible expressions
  undo                  move one revision back
  redo                  move one revision forward
  help                  this text
  quit                  leave the session"""


class Session:
    """A labelled, focused view over a Workspace."""

    def __init__(self, runtime: Runtime[Any]) -> None:
        self._runtime = runtime
        self.workspace = Workspace(runtime)
        self._labels: dict[ObjectVersionId, str] = {}
        self._by_label: dict[str, ObjectVersionId] = {}
        self._next_label = 0
        self._focus: Expression | None = None
        self.closed = False

    @property
    def runtime(self) -> Runtime[Any]:
        return self._runtime

    @property
    def focus(self) -> Expression | None:
        return self._focus

    def visible(self) -> tuple[tuple[str, Expression], ...]:
        return tuple(
            (self._labels[expression.version], expression)
            for expression in self.workspace.expressions()
        )

    def label_of(self, expression: Expression) -> str:
        label = self._labels.get(expression.version)
        if label is None:
            raise SessionError("the expression does not belong to this session")
        return label

    def object(self, label: str) -> Expression:
        version = self._by_label.get(label)
        if version is None:
            raise SessionError(f"no object named @{label}")
        for expression in self.workspace.expressions():
            if expression.version == version:
                return expression
        raise SessionError(f"@{label} is not visible in the current revision")

    # --- operations ---

    def parse(self, text: str) -> T.Term:
        return parse(text, self._runtime.table, self._runtime.signature)

    def intake(self, text: str, label: str | None = None) -> Expression:
        term = self.parse(text)
        chosen = self._choose_label(label)
        expression = self.workspace.intake(term)
        self._register(expression, chosen)
        self._focus = expression
        return expression

    def differentiate(
        self, source: Expression | None = None
    ) -> DerivativeResult:
        if source is None:
            source = self._focus
        if source is None:
            raise SessionError(
                "nothing to differentiate; enter an expression or name one "
                "with @LABEL"
            )
        if source.version not in {
            expression.version for expression in self.workspace.expressions()
        }:
            raise SessionError("the source is not visible in the current revision")
        result = self.workspace.differentiate(
            source, self._runtime.variable
        )
        if result.result is not None:
            chosen = self._choose_label(None)
            self._register(result.result, chosen)
            self._focus = result.result
        return result

    def undo(self) -> str:
        if not self.workspace.undo():
            return "undo: at the beginning"
        self._focus = self._last_visible()
        return "undo: " + (
            f"@{self._labels[self._focus.version]}"
            if self._focus is not None
            else "empty view"
        )

    def redo(self) -> str:
        if not self.workspace.redo():
            return "redo: at the end"
        self._focus = self._last_visible()
        return "redo: " + (
            f"@{self._labels[self._focus.version]}"
            if self._focus is not None
            else "empty view"
        )

    # --- commands ---

    def execute(self, line: str) -> str:
        text = line.strip()
        if not text:
            return ""
        parts = text.split(None, 1)
        command = parts[0]
        argument = parts[1].strip() if len(parts) == 2 else ""
        if command in ("quit", "exit"):
            self.closed = True
            return "bye"
        if command == "help":
            return _HELP
        if command == "list":
            self._require_no_argument(command, argument)
            return self._list()
        if command == "undo":
            self._require_no_argument(command, argument)
            return self.undo()
        if command == "redo":
            self._require_no_argument(command, argument)
            return self.redo()
        if command == "show":
            return self._show(argument)
        if command == "diff":
            return self._differentiate(argument)
        if command == "expr":
            return self._assign(text)
        expression = self.intake(text)
        return self._line(expression)

    # --- command helpers ---

    def _assign(self, text: str) -> str:
        match = _ASSIGNMENT.fullmatch(text)
        if match is None:
            raise SessionError("usage: expr [LABEL] := EXPRESSION")
        expression = self.intake(match.group(2), match.group(1))
        return self._line(expression)

    def _show(self, argument: str) -> str:
        expression = self._resolve(argument, "show")
        return self._line(expression)

    def _differentiate(self, argument: str) -> str:
        source = self._resolve(argument, "diff")
        result = self.differentiate(source)
        if result.status is OperationStatus.VERIFIED:
            assert result.result is not None
            return "verified " + self._line(result.result)
        return f"{result.status.value}: {result.detail}"

    def _resolve(self, argument: str, command: str) -> Expression:
        if argument:
            if not argument.startswith("@"):
                raise SessionError(f"usage: {command} [@LABEL]")
            return self.object(argument[1:])
        if self._focus is None:
            raise SessionError(
                "there is no focused expression; enter one or name it with "
                "@LABEL"
            )
        return self._focus

    def _list(self) -> str:
        expressions = self.workspace.expressions()
        if not expressions:
            return "no expressions"
        lines = []
        for expression in expressions:
            label = self._labels[expression.version]
            marker = (
                ">"
                if self._focus is not None
                and expression.version == self._focus.version
                else " "
            )
            lines.append(f"{marker} @{label}: {self._render(expression)}")
        return "\n".join(lines)

    def _last_visible(self) -> Expression | None:
        expressions = self.workspace.expressions()
        return expressions[-1] if expressions else None

    def _line(self, expression: Expression) -> str:
        return f"@{self.label_of(expression)}: {self._render(expression)}"

    def _render(self, expression: Expression) -> str:
        return to_str(expression.term, self._runtime.signature)

    def _require_no_argument(self, command: str, argument: str) -> None:
        if argument:
            raise SessionError(f"{command} takes no argument")

    def _choose_label(self, requested: str | None) -> str:
        if requested is not None:
            if _LABEL.fullmatch(requested) is None:
                raise SessionError(f"invalid object label {requested!r}")
            if requested in self._by_label:
                raise SessionError(f"label @{requested} is already used")
            return requested
        while True:
            candidate = f"E{self._next_label}"
            self._next_label += 1
            if candidate not in self._by_label:
                return candidate

    def _register(self, expression: Expression, label: str) -> None:
        self._labels[expression.version] = label
        self._by_label[label] = expression.version


__all__ = ["Session", "SessionError"]
