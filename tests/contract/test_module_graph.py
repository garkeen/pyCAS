# -*- coding: utf-8 -*-
"""Module graph: every module imports standalone.

Nail: traversal helpers used to be re-exported lazily from the term module,
which blurred the syntax-term/termpath boundary and allowed stale imports.
Traversal utilities now live only in ``cas.syntax.termpath`` and must be
imported explicitly.

Since 2026-09-10 the tree is split into subpackages (syntax/kernel/workflow/math/
frontend), and the inventory walks each subpackage directory instead of a fixed list,
so a new module that is not tested shows up as a missing entry.
"""

import subprocess
import sys
from pathlib import Path

# Walk up to the directory that contains `cas/`: this test may live at any depth
# under tests/, so a fixed parent.parent would break on a future reclassification.
_ROOT = next(p for p in Path(__file__).resolve().parents if (p / "cas").is_dir())
_DIRS = (
    ("cas", "cas"),
    ("cas/syntax", "cas.syntax"),
    ("cas/kernel", "cas.kernel"),
    ("cas/workflow", "cas.workflow"),
    ("cas/math", "cas.math"),
    ("cas/math/domains", "cas.math.domains"),
    ("cas/frontend", "cas.frontend"),
    ("cas/runtime", "cas.runtime"),
)
_MODULES = []
for rel, prefix in _DIRS:
    for p in sorted((_ROOT / rel).glob("*.py")):
        if p.stem == "__init__":
            continue
        _MODULES.append(f"{prefix}.{p.stem}")


def test_module_list_not_empty():
    assert len(_MODULES) >= 30, f"only found {len(_MODULES)} modules; the path is probably wrong"


def test_every_module_imports_standalone():
    """Import each one in a clean process: any module must succeed as the entry."""
    failed = []
    for m in _MODULES:
        r = subprocess.run([sys.executable, "-c", f"import {m}"],
                           capture_output=True, text=True, cwd=str(_ROOT))
        if r.returncode != 0:
            failed.append(f"{m}: {r.stderr.strip().splitlines()[-1]}")
    assert not failed, "these modules cannot be imported standalone:\n" + "\n".join(failed)


def test_termpath_imports_standalone():
    """The former baseline crash point, pinned on its own."""
    r = subprocess.run([sys.executable, "-c", "import cas.syntax.termpath"],
                       capture_output=True, text=True, cwd=str(_ROOT))
    assert r.returncode == 0, r.stderr


def test_term_surface_excludes_termpath_helpers():
    """The term layer exposes terms only, not traversal utilities."""
    from cas.syntax import pattern as P
    from cas.syntax import term as T
    from cas.syntax import termpath

    for name in ("subst", "free_vars", "term_at", "replace_at", "all_paths"):
        assert not hasattr(T, name), f"termpath helper leaked to term: {name}"
        assert callable(getattr(termpath, name))
    assert callable(P.instantiate)


def test_lazy_reexport_does_not_swallow_unknown():
    import cas.syntax.term as T
    try:
        T.__totally_missing__
    except AttributeError:
        pass
    else:
        raise AssertionError("__getattr__ silently swallowed an unknown attribute")


def test_tree_traversal_single_implementation():
    """_postorder once existed as an isomorphic copy in both pprint and simplify."""
    import cas.frontend.pprint as P
    import cas.math.simplify as Sm
    from cas.syntax.termpath import postorder
    assert not hasattr(P, "_postorder")
    assert not hasattr(Sm, "_postorder")
    assert callable(postorder)
