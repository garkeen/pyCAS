"""Session: one conversation over one runtime and workspace.

The session owns presentation labels.  Its focus is derived from the visible
workspace revision, never stored as a second mutable pointer.  It never decides
mathematics: every answer comes from the workspace, which in turn commits only
through the kernel.  Undo and redo move the visible revision; the ledger is
untouched.
"""

from __future__ import annotations

import re
from fractions import Fraction
from typing import TYPE_CHECKING, Any

from cas.foundation.ids import CandidateId, ObjectVersionId, SymbolId
from cas.frontend.errors import SessionError
from cas.frontend.parser import parse
from cas.frontend.pprint import to_str
from cas.kernel.verdict import (
    Verdict,
    VerdictNo,
    VerdictUnknown,
    VerdictYes,
)
from cas.language import sorts as S
from cas.language.decisions import Blocker
from cas.language.problems import Coverage
from cas.syntax import binding as B
from cas.syntax import term as T
from cas.workflow.records import (
    CandidateFocus,
    Event,
    Expression,
    Focus,
    ObjectFocus,
    ObjectVersion,
    OccurrenceFocus,
    OperationResult,
    OperationStatus,
    TaskFocus,
)
from cas.workflow.workspace import Workspace

if TYPE_CHECKING:
    from cas.runtime.bootstrap import Runtime

_LABEL = re.compile(r"[A-Za-z_][A-Za-z0-9_]*\Z")
_OBJECT_REFERENCE = re.compile(r"@([A-Za-z_][A-Za-z0-9_]*)")
_ASSIGNMENT = re.compile(
    r"expr(?:\s+([A-Za-z_][A-Za-z0-9_]*))?\s*:=\s*(.+)\Z"
)

_SORT_NAMES: dict[str, S.Sort] = {
    "integer": S.INTEGER,
    "rational": S.RATIONAL,
    "real": S.REAL,
    "complex": S.COMPLEX,
    "proposition": S.PROPOSITION,
    "scalar": S.UNKNOWN_SCALAR,
}

_HELP = """commands:
  <expression>          store an expression object
  expr LABEL := EXPR    store an expression object with a label
  declare NAME : SORT   declare a scalar or proposition name in a child frame
  define NAME := EXPR   define an alias in a child frame
  assume FORMULA        add a hypothesis in a child frame
  diff [@LABEL]         differentiate the focused or named expression
  integrate [@LABEL]    integrate a polynomial in the focused or named expression
  hermite [@LABEL]      reduce the repeated denominator of a rational function
  solve [sound] [@LABEL]
                        solve a linear polynomial as a finite set
  gcd @A @B             compute the monic polynomial gcd
  resultant @A @B       compute the univariate resultant
  specialize [@LABEL] a=VALUE ...
                        apply exact parameter values to a verified family
  show [@LABEL]         show an expression
  object @LABEL         show an object version's artifact kind and source
  list                  list the visible expressions
  candidates            list the visible candidates
  relations             list the visible construction relations
  check ID              re-run the recorded checker for a candidate
  decide ID             check a candidate without publishing the judgment
  edit ID = EXPR        create a new unchecked candidate version
  history               show the visible revision's event history
  undo                  move one revision back
  redo                  move one revision forward
  help                  this text
  quit                  leave the session"""


_PLACEHOLDER = "__pycas_object_reference_{}__"


def _mentions_symbol(term: T.Term, symbols: frozenset[SymbolId]) -> bool:
    """Whether any listed symbol occurs anywhere, including quoted data."""
    stack: list[T.Term] = [term]
    while stack:
        current = stack.pop()
        if isinstance(current, T.SymbolRef):
            if current.symbol_id in symbols:
                return True
        elif isinstance(current, T.Apply):
            stack.append(current.operator)
            stack.extend(current.arguments)
        elif isinstance(current, T.Binder):
            stack.append(current.body)
            stack.extend(current.annotations)
        elif isinstance(current, T.Quote):
            stack.append(current.term)
    return False


class Session:
    """A labelled, focused view over a Workspace."""

    def __init__(self, runtime: Runtime[Any]) -> None:
        self._runtime = runtime
        self.workspace = Workspace(runtime)
        self._labels: dict[ObjectVersionId, str] = {}
        self._by_label: dict[str, ObjectVersionId] = {}
        self._next_label = 0
        self._next_placeholder = 0
        self.closed = False

    @property
    def runtime(self) -> Runtime[Any]:
        return self._runtime

    @property
    def focus_ref(self) -> Focus | None:
        """The revision's UI focus, including task/candidate/occurrence."""
        return self.workspace.revision.focus

    @property
    def focus(self) -> Expression | None:
        """The focused visible expression, derived from the revision.

        A task, candidate or occurrence focus has no expression source, and a
        revision without a recorded focus has none either; the command layer
        reports that honestly instead of guessing the last expression.
        """
        focus = self.workspace.revision.focus
        if isinstance(focus, ObjectFocus):
            for expression in self.workspace.expressions():
                if expression.version == focus.version:
                    return expression
        return None

    def visible(self) -> tuple[tuple[str, Expression], ...]:
        """The visible expressions with their session labels.

        An expression recorded directly through the workspace has no session
        label; it is still visible, so it receives the stable display name
        `v{version}` instead of making the listing fail.
        """
        return tuple(
            (self._display_name(expression.version), expression)
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

    def history(self) -> tuple[str, ...]:
        """The visible revision's events as immutable, user-readable lines."""
        return tuple(
            self._history_line(event) for event in self.workspace.events()
        )

    # --- operations ---

    def parse(self, text: str) -> T.Term:
        """Parse text, embedding the exact object snapshots named by `@LABEL`.

        An embedded reference is resolved against the visible revision before
        parsing.  The parser sees a private placeholder symbol instead of the
        reference spelling, and the resulting term receives the captured object
        term through the capture-avoiding free-symbol substitution.  No
        `@LABEL` spelling enters the symbol table, and no placeholder survives
        in the returned term.
        """
        matches = tuple(_OBJECT_REFERENCE.finditer(text))
        if text.count("@") != len(matches):
            raise SessionError("invalid object reference; expected @LABEL")
        if not matches:
            return parse(text, self._runtime.table, self._runtime.signature)

        references: dict[str, T.Term] = {}
        for match in matches:
            label = match[1]
            if label not in references:
                references[label] = self.object(label).term
        placeholders = {
            label: self._fresh_placeholder(text) for label in references
        }
        parts: list[str] = []
        cursor = 0
        for match in matches:
            parts.append(text[cursor : match.start()])
            # Spaces keep the placeholder a separate token: `x@F` must not
            # become the single user name `x__pycas_object_reference_0__`.
            parts.append(f" {placeholders[match[1]]} ")
            cursor = match.end()
        parts.append(text[cursor:])
        term = parse(
            "".join(parts), self._runtime.table, self._runtime.signature
        )
        mapping: dict[SymbolId, T.Term] = {}
        for label, placeholder in placeholders.items():
            identifier = self._runtime.table.lookup(placeholder)
            if identifier is None:
                raise AssertionError("the parser did not intern its placeholder")
            mapping[identifier] = references[label]
        result = B.substitute_free(term, mapping)
        if _mentions_symbol(result, frozenset(mapping)):
            raise SessionError(
                "an object reference inside quote(...) is held syntax data; "
                "it cannot be embedded as a mathematical term"
            )
        return result

    def _fresh_placeholder(self, text: str) -> str:
        """A name no user symbol or formula occurrence can already own."""
        while True:
            name = _PLACEHOLDER.format(self._next_placeholder)
            self._next_placeholder += 1
            if (
                self._runtime.table.lookup(name) is None
                and name not in text
            ):
                return name

    def intake(self, text: str, label: str | None = None) -> Expression:
        term = self.parse(text)
        chosen = self._choose_label(label)
        expression = self.workspace.intake(term)
        self._register(expression, chosen)
        return expression

    def differentiate(
        self, source: Expression | None = None
    ) -> OperationResult:
        if source is None:
            source = self.focus
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
        return result

    def undo(self) -> str:
        if not self.workspace.undo():
            return "undo: at the beginning"
        return "undo: " + self._history_view()

    def redo(self) -> str:
        if not self.workspace.redo():
            return "redo: at the end"
        return "redo: " + self._history_view()

    # --- commands ---

    def execute(self, line: str) -> str:
        """Dispatch user commands; mathematical dispatch stays in the registry."""
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
        if command == "history":
            self._require_no_argument(command, argument)
            return self._history()
        if command == "undo":
            self._require_no_argument(command, argument)
            return self.undo()
        if command == "redo":
            self._require_no_argument(command, argument)
            return self.redo()
        if command == "show":
            return self._show(argument)
        if command == "object":
            return self._object(argument)
        if command == "diff":
            return self._differentiate(argument)
        if command == "integrate":
            return self._integrate(argument)
        if command == "hermite":
            return self._hermite(argument)
        if command == "solve":
            return self._solve(argument)
        if command == "gcd":
            return self._gcd(argument)
        if command == "resultant":
            return self._resultant(argument)
        if command == "declare":
            return self._declare(argument)
        if command == "define":
            return self._define(argument)
        if command == "assume":
            return self._assume(argument)
        if command == "specialize":
            return self._specialize(argument)
        if command == "candidates":
            self._require_no_argument(command, argument)
            return self._candidates()
        if command == "relations":
            self._require_no_argument(command, argument)
            return self._relations()
        if command == "check":
            return self._check(argument)
        if command == "decide":
            return self._decide(argument)
        if command == "edit":
            return self._edit(argument)
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

    def _object(self, argument: str) -> str:
        """Show one visible object version without changing the revision."""
        if not argument.startswith("@"):
            raise SessionError("usage: object @LABEL")
        label = argument[1:]
        return self._object_version_line(
            self._object_version_for_label(label), label
        )

    def _object_version_for_label(self, label: str) -> ObjectVersion:
        """Resolve a read-only object view by session or function label.

        Session expression labels take precedence.  A function label is
        presentation metadata on the visible `FunctionObject`; if more than one
        visible function version carries the same label the reference is
        ambiguous and is refused rather than silently choosing one.  This is a
        lookup only: it neither moves focus nor records a revision.
        """
        version = self._by_label.get(label)
        if version is None:
            matches = tuple(
                function.version
                for function in self.workspace.functions()
                if function.label == label
            )
            if len(matches) > 1:
                raise SessionError(
                    f"@{label} names more than one visible function"
                )
            if not matches:
                raise SessionError(f"no object named @{label}")
            version = matches[0]
        view = self.workspace.object_version(version)
        if view is None:
            raise SessionError(
                f"@{label} is not visible in the current revision"
            )
        return view

    def _object_version_line(
        self, view: ObjectVersion, label: str
    ) -> str:
        """Render an object version without changing the visible revision."""
        artifact = view.artifact
        if artifact.term is not None:
            kind = "term"
            rendered = to_str(artifact.term, self._runtime.signature)
        elif artifact.function is not None:
            kind = "function"
            rendered = to_str(
                artifact.function.representations[0].term,
                self._runtime.signature,
            )
        else:
            raise TypeError("an artifact has no payload")
        operation = view.source_operation or "none"
        return (
            f"@{label}: {rendered} "
            f"[artifact={kind}; operation={operation}]"
        )

    def _declare(self, argument: str) -> str:
        parts = argument.split(":")
        if len(parts) != 2:
            raise SessionError("usage: declare NAME : SORT")
        name = parts[0].strip()
        sort_name = parts[1].strip()
        if (
            _LABEL.fullmatch(name) is None
            or _LABEL.fullmatch(sort_name) is None
        ):
            raise SessionError("usage: declare NAME : SORT")
        sort = _SORT_NAMES.get(sort_name)
        if sort is None:
            raise SessionError(
                f"unknown sort {sort_name!r}; accepted sorts: "
                + ", ".join(_SORT_NAMES)
            )
        result = self.workspace.declare(name, sort)
        if result.status is OperationStatus.VERIFIED:
            assert result.declaration is not None
            return (
                f"declared {result.declaration.name} : {sort_name} "
                f"in F{result.frame}"
            )
        return f"{result.status.value}: {result.detail}"

    def _define(self, argument: str) -> str:
        parts = argument.split(":=")
        if len(parts) != 2:
            raise SessionError("usage: define NAME := EXPRESSION")
        name = parts[0].strip()
        text = parts[1].strip()
        if _LABEL.fullmatch(name) is None or not text:
            raise SessionError("usage: define NAME := EXPRESSION")
        body = self.parse(text)
        result = self.workspace.define(name, body)
        if result.status is OperationStatus.VERIFIED:
            assert result.definition is not None
            return (
                f"defined {result.definition.name} := "
                f"{to_str(result.definition.body, self._runtime.signature)} "
                f"in F{result.frame}"
            )
        return f"{result.status.value}: {result.detail}"

    def _assume(self, argument: str) -> str:
        if not argument:
            raise SessionError("usage: assume FORMULA")
        result = self.workspace.assume(self.parse(argument))
        if result.status is OperationStatus.VERIFIED:
            assert result.proposition is not None
            return "assumed: " + to_str(
                result.proposition.term, self._runtime.signature
            )
        return f"{result.status.value}: {result.detail}"

    def _differentiate(self, argument: str) -> str:
        source = self._resolve(argument, "diff")
        result = self.differentiate(source)
        if result.status in (
            OperationStatus.VERIFIED,
            OperationStatus.CONDITIONAL,
        ):
            return self._success_line(result)
        return self._report(result)

    def _integrate(self, argument: str) -> str:
        source = self._resolve(argument, "integrate")
        result = self.workspace.integrate(source, self._runtime.variable)
        if result.status in (
            OperationStatus.VERIFIED,
            OperationStatus.CONDITIONAL,
        ):
            assert result.result is not None
            self._register(result.result, self._choose_label(None))
            return self._success_line(result)
        return self._report(result)

    def _hermite(self, argument: str) -> str:
        source = self._resolve(argument, "hermite")
        result = self.workspace.hermite_reduce(
            source, self._runtime.variable
        )
        if result.status in (
            OperationStatus.VERIFIED,
            OperationStatus.CONDITIONAL,
        ):
            assert result.result is not None
            self._register(result.result, self._choose_label(None))
            return self._success_line(result)
        return self._report(result)

    def _solve(self, argument: str) -> str:
        coverage = Coverage.COMPLETE_SET
        text = argument
        if text.startswith("sound"):
            coverage = Coverage.SOUND_SET
            text = text[len("sound"):].strip()
        source = self._resolve(text, "solve")
        result = self.workspace.solve_linear(
            source, self._runtime.variable, coverage
        )
        if result.status in (
            OperationStatus.VERIFIED,
            OperationStatus.CONDITIONAL,
        ):
            assert result.result is not None
            self._register(result.result, self._choose_label(None))
            return self._success_line(result)
        return self._report(result)

    def _gcd(self, argument: str) -> str:
        parts = argument.split()
        if len(parts) != 2:
            raise SessionError("usage: gcd @A @B")
        left = self._resolve(parts[0], "gcd")
        right = self._resolve(parts[1], "gcd")
        result = self.workspace.gcd(
            left, right, self._runtime.variable
        )
        if result.status in (
            OperationStatus.VERIFIED,
            OperationStatus.CONDITIONAL,
        ):
            assert result.result is not None
            self._register(result.result, self._choose_label(None))
            return self._success_line(result)
        return self._report(result)

    def _resultant(self, argument: str) -> str:
        parts = argument.split()
        if len(parts) != 2:
            raise SessionError("usage: resultant @A @B")
        left = self._resolve(parts[0], "resultant")
        right = self._resolve(parts[1], "resultant")
        result = self.workspace.resultant(
            left, right, self._runtime.variable
        )
        if result.status in (
            OperationStatus.VERIFIED,
            OperationStatus.CONDITIONAL,
        ):
            assert result.result is not None
            self._register(result.result, self._choose_label(None))
            return self._success_line(result)
        return self._report(result)

    def _candidate_id(self, text: str) -> CandidateId:
        value = text.strip()
        if value.startswith("C"):
            value = value[1:]
        try:
            return CandidateId(int(value))
        except ValueError as error:
            raise SessionError("a candidate id must be an integer") from error

    def _candidates(self) -> str:
        candidates = self.workspace.candidates()
        if not candidates:
            return "no candidates"
        return "\n".join(
            f"C{candidate.id}: "
            f"{to_str(candidate.term, self._runtime.signature)} "
            f"[state={candidate.state.value}; "
            f"applicability={candidate.applicability.value}; "
            f"coverage={candidate.coverage.value}; "
            f"language={candidate.language_fit.value}]"
            for candidate in candidates
        )

    def _relations(self) -> str:
        """List the visible construction relations without changing the view."""
        relations = self.workspace.construction_relations()
        if not relations:
            return "no relations"
        return "\n".join(
            f"{relation.kind}: "
            f"{self._object_name(relation.source)} -> "
            f"{self._object_name(relation.target)} | "
            f"{to_str(relation.specification.term, self._runtime.signature)}"
            for relation in relations
        )

    def _check(self, argument: str) -> str:
        if not argument:
            raise SessionError("usage: check ID")
        result = self.workspace.check_candidate(
            self._candidate_id(argument)
        )
        if result.status in (
            OperationStatus.VERIFIED,
            OperationStatus.CONDITIONAL,
        ):
            assert result.result is not None
            self._register(result.result, self._choose_label(None))
            return self._success_line(result)
        return self._report(result)

    def _decide(self, argument: str) -> str:
        """Decide one visible candidate without publishing it.

        The workspace raises `ValueError` when a candidate is unknown, hidden
        or has no evidence (for example after `edit`, which creates an
        unchecked record).  The frontend must translate that refusal into a
        `SessionError`; otherwise it escapes the REPL, which only reports
        `FrontendError` values, and terminates the session.  Manual evidence
        entry is not implemented: an edited candidate stays unchecked until an
        operation supplies a new certificate.
        """
        if not argument:
            raise SessionError("usage: decide ID")
        identifier = self._candidate_id(argument)
        try:
            verdict = self.workspace.decide_candidate(identifier)
        except ValueError as error:
            raise SessionError(str(error)) from error
        return self._verdict_line(verdict)

    def _verdict_line(self, verdict: Verdict) -> str:
        """Render one three-valued decision without claiming publication."""
        if isinstance(verdict, VerdictYes):
            yes_receipt = verdict.receipt
            return (
                "yes: "
                + to_str(
                    yes_receipt.proposition.term, self._runtime.signature
                )
                + f" | checker: {yes_receipt.checker_id}@"
                + yes_receipt.checker_version
            )
        if isinstance(verdict, VerdictNo):
            no_receipt = verdict.receipt
            return (
                "no: "
                + to_str(
                    no_receipt.proposition.term, self._runtime.signature
                )
                + f" | detail: {no_receipt.detail}"
                + f" | witnesses: {len(no_receipt.witnesses)}"
            )
        if isinstance(verdict, VerdictUnknown):
            return "\n".join(
                self._blocker_line(blocker)
                for blocker in verdict.blockers
            )
        raise TypeError("unknown verdict variant")

    def _blocker_line(self, blocker: Blocker) -> str:
        text = f"unknown: {blocker.reason.value} {blocker.detail}"
        if blocker.missing:
            text += " | missing: " + ", ".join(sorted(blocker.missing))
        if blocker.conditions:
            text += " | conditions: " + ", ".join(
                to_str(condition.term, self._runtime.signature)
                for condition in blocker.conditions
            )
        return text

    def _edit(self, argument: str) -> str:
        if "=" not in argument:
            raise SessionError("usage: edit ID = EXPR")
        identifier, source = argument.split("=", 1)
        outcome = self.workspace.edit_candidate(
            self._candidate_id(identifier), self.parse(source)
        )
        if outcome.candidate is None:
            return f"{outcome.status.value}: {outcome.detail}"
        return (
            f"edited C{outcome.candidate.id}: "
            f"{to_str(outcome.candidate.term, self._runtime.signature)} "
            "[unchecked]"
        )

    def _specialize(self, argument: str) -> str:
        runtime = self._runtime
        if not runtime.request.parameters:
            return "unsupported: this runtime has no formal parameters"
        parts = argument.split()
        source: Expression | None
        if parts and parts[0].startswith("@"):
            source = self.object(parts[0][1:])
            parts = parts[1:]
        else:
            source = self.focus
        if source is None:
            raise SessionError(
                "there is no focused expression; enter one or name it with "
                "@LABEL"
            )
        if not parts:
            raise SessionError("usage: specialize [@LABEL] NAME=VALUE ...")

        parameters = set(runtime.request.parameters)
        values: dict[SymbolId, Fraction] = {}
        for token in parts:
            name, separator, text = token.partition("=")
            if not separator or not name or not text:
                raise SessionError(f"expected NAME=VALUE, got {token!r}")
            symbol_id = runtime.table.lookup(name)
            if symbol_id is None or symbol_id not in parameters:
                raise SessionError(
                    f"{name!r} is not a parameter of this runtime"
                )
            if symbol_id in values:
                raise SessionError(f"parameter {name!r} is assigned twice")
            term = self.parse(text)
            if isinstance(term, T.IntLit):
                values[symbol_id] = Fraction(term.value)
            elif isinstance(term, T.RatLit):
                values[symbol_id] = term.value
            else:
                raise SessionError(
                    "a parameter value must be an exact rational literal"
                )
        missing = [
            runtime.table.name_of(symbol_id)
            for symbol_id in runtime.request.parameters
            if symbol_id not in values
        ]
        if missing:
            raise SessionError(
                "missing parameter values: " + ", ".join(missing)
            )

        result = self.workspace.specialize(source, values)
        if result.status in (
            OperationStatus.VERIFIED,
            OperationStatus.CONDITIONAL,
        ):
            assert result.result is not None
            self._register(result.result, self._choose_label(None))
            return self._success_line(result)
        return self._report(result)

    def _resolve(self, argument: str, command: str) -> Expression:
        if argument:
            if not argument.startswith("@"):
                raise SessionError(f"usage: {command} [@LABEL]")
            return self.object(argument[1:])
        focus = self.focus
        if focus is None:
            raise SessionError(
                "there is no focused expression; enter one or name it with "
                "@LABEL"
            )
        return focus

    def _list(self) -> str:
        expressions = self.workspace.expressions()
        if not expressions:
            return "no expressions"
        focus = self.focus
        lines = []
        for expression in expressions:
            label = self._display_name(expression.version)
            marker = (
                ">"
                if focus is not None
                and expression.version == focus.version
                else " "
            )
            lines.append(f"{marker} @{label}: {self._render(expression)}")
        return "\n".join(lines)

    def _history(self) -> str:
        lines = self.history()
        return "no history" if not lines else "\n".join(lines)

    def _history_line(self, event: Event) -> str:
        inputs = ", ".join(
            self._object_name(version) for version in event.inputs
        )
        parameters = ", ".join(
            f"{name}={value!r}" for name, value in event.parameters
        )
        source = (
            "none"
            if event.input_revision is None
            else f"R{event.input_revision}"
        )
        output = (
            "none"
            if event.output_revision is None
            else f"R{event.output_revision}"
        )
        report = (
            "none"
            if event.execution_report is None
            else event.execution_report.value
        )
        frame = "none" if event.frame is None else f"F{event.frame}"
        frame_digest = (
            "none"
            if not event.frame_digest
            else event.frame_digest[:12]
        )
        world = self.workspace.revision.world
        world_text = "none" if world is None else f"W{world}"
        focus = (
            "none"
            if event.output_revision is None
            else self._focus_text(
                self.workspace.revision_at(event.output_revision).focus
            )
        )
        operation = event.operation
        if event.operation_version:
            operation += "@" + event.operation_version
        return (
            f"{source} {operation} actor={event.actor_kind.value} "
            f"frame={frame} digest={frame_digest} world={world_text} "
            f"focus={focus} inputs=[{inputs}] parameters=[{parameters}] "
            f"status={report} -> {output}"
        )

    def _revision_name(self, version: ObjectVersionId) -> str | None:
        for named_version, name in self.workspace.revision.object_names:
            if named_version == version:
                return name
        return None

    def _object_name(self, version: ObjectVersionId) -> str:
        label = self._labels.get(version)
        if label is not None:
            return f"@{label}"
        return self._revision_name(version) or f"v{version}"

    def _display_name(self, version: ObjectVersionId) -> str:
        """A session label, a revision name, or a stable fallback."""
        label = self._labels.get(version)
        if label is not None:
            return label
        return self._revision_name(version) or f"v{version}"

    def _focus_text(self, focus: Focus | None) -> str:
        if focus is None:
            return "none"
        if isinstance(focus, ObjectFocus):
            return "object:" + self._object_name(focus.version)
        if isinstance(focus, TaskFocus):
            return f"task:t{focus.task}"
        if isinstance(focus, CandidateFocus):
            return f"candidate:c{focus.candidate}"
        if isinstance(focus, OccurrenceFocus):
            path = ".".join(str(index) for index in focus.occurrence.path)
            return (
                "occurrence:"
                + self._object_name(focus.version)
                + "/"
                + path
            )
        raise TypeError("unknown focus variant")

    def _history_view(self) -> str:
        expression = self.focus
        if expression is not None:
            label = self._object_name(expression.version)
        else:
            focus = self.workspace.revision.focus
            label = (
                "empty view" if focus is None else self._focus_text(focus)
            )
        return f"{label} ({self.workspace.revision.label})"

    def _success_line(self, result: OperationResult) -> str:
        """Render a verified or conditional result with its conditions.

        A conditional result without a result region may still carry open
        kernel obligations.  It is never rendered as a plain `verified` line:
        either its region is shown, or the refusal/condition path is used.
        """
        assert result.result is not None
        if result.status is OperationStatus.VERIFIED:
            return "verified " + self._line(result.result)
        if result.status is not OperationStatus.CONDITIONAL:
            raise TypeError("a success line needs a verified result")
        if result.region is None:
            return self._report(result)
        return (
            "verified on "
            + to_str(result.region.term, self._runtime.signature)
            + " "
            + self._line(result.result)
            + self._condition_suffix(result)
        )

    def _condition_suffix(self, result: OperationResult) -> str:
        conditions = tuple(
            dict.fromkeys(
                condition
                for link in result.verifications
                for condition in (
                    (() if link.condition is None else (link.condition,))
                    + link.obligations
                )
            )
        )
        if not conditions:
            return ""
        return " | condition: " + ", ".join(
            to_str(condition.term, self._runtime.signature)
            for condition in conditions
        )

    def _report(self, result: OperationResult) -> str:
        """Render a refusal without discarding its structured blocker."""
        if result.blocker is None:
            text = result.status.value
            if result.detail:
                text += ": " + result.detail
            return text + self._condition_suffix(result)
        blocker = result.blocker
        text = f"{result.status.value}: {blocker.detail}"
        if blocker.target is not None:
            text += " | target: " + to_str(
                blocker.target.term, self._runtime.signature
            )
        if blocker.missing:
            text += " | missing: " + ", ".join(sorted(blocker.missing))
        if blocker.conditions:
            text += " | conditions: " + ", ".join(
                to_str(condition.term, self._runtime.signature)
                for condition in blocker.conditions
            )
        if blocker.attempted:
            text += " | attempted: " + ", ".join(blocker.attempted)
        if blocker.budget is not None:
            limits: list[str] = []
            if blocker.budget.max_nodes is not None:
                limits.append(f"max_nodes={blocker.budget.max_nodes}")
            if blocker.budget.max_depth is not None:
                limits.append(f"max_depth={blocker.budget.max_depth}")
            if limits:
                text += " | budget: " + ", ".join(limits)
        return text + self._condition_suffix(result)

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
