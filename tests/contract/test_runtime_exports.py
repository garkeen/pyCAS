"""Runtime query and explicit-assembly contracts."""

import ast
from pathlib import Path

from cas.runtime import Runtime


def test_runtime_query_surface(runtime: Runtime) -> None:
    declaration = runtime.const_by_name("gamma")
    assert declaration is not None
    assert declaration.print_name == "γ"
    assert declaration.real is True
    assert runtime.const_by_name("__nope__") is None
    assert runtime.is_const_name("pi") is True
    assert runtime.is_const_name("e") is True
    assert runtime.is_const_name("Sin") is False
    assert runtime.print_name("gamma") == "γ"
    assert runtime.print_name("pi") == "π"
    assert runtime.print_name("Sin") == "sin"
    assert runtime.print_name("__nope__") is None


def test_const_literals_live_in_runtime_not_kernel() -> None:
    import cas.syntax.parse as syntax_parse

    assert not hasattr(syntax_parse, "_CONSTS")
    assert set(syntax_parse._SYNTAX_ATOMS) == {"infinity", "true", "false"}


def test_domain_condition_single_registration_channel() -> None:
    import cas.math.domcond as domain_conditions

    assert not hasattr(domain_conditions, "DOM_HOOKS")


def test_runtime_dispatch_module_is_removed() -> None:
    assert not Path("cas/runtime/dispatch.py").exists()


def test_production_has_no_module_getattr() -> None:
    root = Path("cas")
    offenders: list[str] = []
    for path in root.rglob("*.py"):
        tree = ast.parse(path.read_text(encoding="utf-8"))
        for node in ast.walk(tree):
            if isinstance(node, ast.FunctionDef) and node.name == "__getattr__":
                offenders.append(str(path))
    assert not offenders


def test_semantics_complete_after_bootstrap(runtime: Runtime) -> None:
    stats = runtime.stats()
    assert stats.constants == 4 and stats.functions == 11
    assert stats.domain_conditions == 2
    assert stats.decision_stages == 1 and stats.domains == 3
