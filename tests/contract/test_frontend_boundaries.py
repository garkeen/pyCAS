"""Static contracts for explicit frontend and runtime boundaries."""

import ast
from collections.abc import Iterator
from pathlib import Path

import pytest

from cas.frontend.repl import REPL
from cas.frontend.session import Session
from cas.runtime import Runtime


_ROOT = next(path for path in Path(__file__).resolve().parents if (path / "cas").is_dir())
_CAS = _ROOT / "cas"
_CORE_DIRECTORIES = (
    _CAS / "kernel",
    _CAS / "workflow",
    _CAS / "runtime",
    _CAS / "frontend",
)


def _tree(path: Path) -> ast.Module:
    return ast.parse(path.read_text(encoding="utf-8"))


def _functions(tree: ast.Module, name: str) -> tuple[ast.FunctionDef, ...]:
    return tuple(
        node
        for node in ast.walk(tree)
        if isinstance(node, ast.FunctionDef) and node.name == name
    )


def _parameters(node: ast.FunctionDef) -> tuple[ast.arg, ...]:
    return (*node.args.posonlyargs, *node.args.args)


def _annotation_nodes(annotation: ast.expr) -> Iterator[ast.expr]:
    """Yield annotation nodes without treating a subscripted container as bare."""
    if isinstance(annotation, ast.Subscript):
        yield from _annotation_nodes(annotation.slice)
        return
    yield annotation
    for child in ast.iter_child_nodes(annotation):
        if isinstance(child, ast.expr):
            yield from _annotation_nodes(child)


def _assert_first_parameter(path: Path, function_name: str, expected: str) -> None:
    functions = _functions(_tree(path), function_name)
    assert functions, f"{path.name} has no {function_name} function"
    for function in functions:
        parameters = _parameters(function)
        assert parameters and parameters[0].arg == expected, (
            f"{path.name}.{function_name} must receive {expected} explicitly"
        )


def test_no_process_runtime_or_module_dispatch_in_production() -> None:
    runtime_name = "get_" + "runtime"
    dispatch_module = "cas.runtime" + ".dispatch"
    offenders: list[str] = []
    for path in sorted(_CAS.rglob("*.py")):
        tree = _tree(path)
        for node in ast.walk(tree):
            if isinstance(node, ast.Name) and node.id == runtime_name:
                offenders.append(f"{path.relative_to(_ROOT)}:{node.lineno}:{runtime_name}")
            elif isinstance(node, ast.Attribute) and node.attr == runtime_name:
                offenders.append(f"{path.relative_to(_ROOT)}:{node.lineno}:{runtime_name}")
            elif isinstance(node, ast.FunctionDef) and node.name == "__getattr__":
                offenders.append(f"{path.relative_to(_ROOT)}:{node.lineno}:__getattr__")
            elif isinstance(node, ast.ImportFrom) and node.module == dispatch_module:
                offenders.append(f"{path.relative_to(_ROOT)}:{node.lineno}:{dispatch_module}")
            elif isinstance(node, ast.Import):
                for alias in node.names:
                    if alias.name == dispatch_module:
                        offenders.append(f"{path.relative_to(_ROOT)}:{node.lineno}:{alias.name}")
    assert not offenders, "removed runtime entry points returned:\n" + "\n".join(offenders)


def test_production_has_no_dynamic_attribute_access() -> None:
    forbidden = {"getattr", "hasattr", "setattr"}
    offenders: list[str] = []
    for path in sorted(_CAS.rglob("*.py")):
        tree = _tree(path)
        for node in ast.walk(tree):
            if isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
                if node.func.id in forbidden:
                    offenders.append(f"{path.relative_to(_ROOT)}:{node.lineno}:{node.func.id}")
    assert not offenders, "dynamic attribute access remains:\n" + "\n".join(offenders)


def test_frontend_public_entry_points_require_runtime() -> None:
    _assert_first_parameter(_CAS / "frontend" / "parser.py", "parse", "runtime")
    _assert_first_parameter(_CAS / "frontend" / "pprint.py", "to_str", "runtime")
    _assert_first_parameter(_CAS / "frontend" / "pprint.py", "pat_to_str", "runtime")
    for name in (
        "back_substitute",
        "guard_report",
        "solve_linear",
        "solve_linear_with_condition",
        "solve_piecewise",
        "differentiate",
        "differentiate_piecewise",
        "integrate_term",
        "definite_integrate",
        "domain_normal_form",
        "declared_ruleset",
    ):
        _assert_first_parameter(_CAS / "api.py", name, "runtime")

    repl_init = _functions(_tree(_CAS / "frontend" / "repl.py"), "__init__")
    assert repl_init
    repl_parameters = _parameters(repl_init[0])
    assert len(repl_parameters) >= 2 and repl_parameters[1].arg == "runtime"

    session_init = _functions(_tree(_CAS / "frontend" / "session.py"), "__init__")
    assert session_init
    session_parameters = _parameters(session_init[0])
    assert len(session_parameters) >= 3
    assert session_parameters[1].arg == "runtime"
    assert session_parameters[2].arg == "handlers"


def test_core_annotations_have_no_unbounded_containers() -> None:
    forbidden = {"Any", "object", "dict", "list", "set", "tuple"}
    offenders: list[str] = []
    for directory in _CORE_DIRECTORIES:
        for path in sorted(directory.rglob("*.py")):
            tree = _tree(path)
            for node in ast.walk(tree):
                annotations: list[ast.expr] = []
                if isinstance(node, ast.arg):
                    annotations.append(node.annotation)
                elif isinstance(node, ast.AnnAssign):
                    annotations.append(node.annotation)
                elif isinstance(node, ast.FunctionDef):
                    annotations.append(node.returns)
                allowed_evidence_boundary = (
                    path == _CAS / "kernel" / "evidence.py"
                    and isinstance(node, ast.AnnAssign)
                    and isinstance(node.target, ast.Name)
                    and node.target.id == "EvidencePayload"
                )
                for annotation in annotations:
                    if annotation is None:
                        continue
                    for child in _annotation_nodes(annotation):
                        if not isinstance(child, ast.Name) or child.id not in forbidden:
                            continue
                        if allowed_evidence_boundary and child.id == "object":
                            continue
                        offenders.append(
                            f"{path.relative_to(_ROOT)}:{child.lineno}:{child.id}"
                        )
    assert not offenders, "unbounded core annotation found:\n" + "\n".join(offenders)


def test_session_bootstraps_every_command_handler(runtime: Runtime) -> None:
    repl = REPL(runtime)
    assert repl.session.commands
    assert all(callable(command.handler) for command in repl.session.commands.values())


def test_session_rejects_a_missing_command_handler(runtime: Runtime) -> None:
    def ignore(_session: Session, _text: str) -> None:
        return None

    handlers = {name: ignore for name in runtime.commands}
    missing = next(iter(runtime.commands))
    del handlers[missing]
    with pytest.raises(ValueError, match="missing=" + missing):
        Session(runtime, handlers)
