# -*- coding: utf-8 -*-
"""Domain registry: centralized assembly, single responsibility.

Nails (the state before convergence):
* registration was scattered across four places (q.py / z.py self-registering,
  poly.py lazily registering by variable set at runtime, project.py registering Q(i)
  on behalf of them), so the registry content depended on which module happened to be
  imported;
* `lookup()` / `domain_scope()` had zero call sites in the whole project: the registry
  was written but never read;
* K(x) was never registered, unlike K[x], and poly's lazy registration let the table
  grow without bound.
"""

import subprocess
import sys

from cas.math.domains.base import _DOMAINS, lookup
from cas.syntax.term import S


def _ring():
    """The coefficient ring K of K[x] / K(x): assembly provides it explicitly, so a
    caller never falls back to a module default."""
    from cas.runtime import get_runtime
    return get_runtime().math.coeff_ring


def test_domain_packages_are_declaration_only():
    """Importing cas.math.domains must write nothing into the registry."""
    code = ("from cas.math.domains.base import _DOMAINS; "
            "import cas.math.domains; print(len(_DOMAINS))")
    out = subprocess.run([sys.executable, "-c", code], capture_output=True,
                         text=True, cwd=".")
    assert out.returncode == 0, out.stderr
    assert out.stdout.strip() == "0"


def test_import_does_not_assemble_bootstrap_does():
    """No import-time mutation of global state: the registry is empty after importing
    the math modules."""
    code = ("from cas.math.domains.base import _DOMAINS; "
            "import cas.math.project, cas.math.decide; "
            "print(len(_DOMAINS))")
    out = subprocess.run([sys.executable, "-c", code], capture_output=True,
                         text=True, cwd=".")
    assert out.returncode == 0, out.stderr
    assert out.stdout.strip() == "0", "import time must register no domain"


def test_bootstrap_registers_three_base_domains():
    code = ("from cas.runtime import bootstrap; bootstrap(); "
            "from cas.math.domains.base import _DOMAINS; "
            "print(','.join(sorted(_DOMAINS)))")
    out = subprocess.run([sys.executable, "-c", code], capture_output=True,
                         text=True, cwd=".")
    assert out.returncode == 0, out.stderr
    assert out.stdout.strip().split(",") == ["Q", "Q(i)", "Z"]


def test_parametric_domains_not_in_registry():
    """K[x]/K(x) are instances parameterized by variable set: they belong to the factory
    caches and never enter the registry."""
    before = set(_DOMAINS)
    from cas.math.domains.poly import poly_domain
    from cas.math.domains.ratfunc import ratfunc_domain
    ring = _ring()
    for v in ("x", "y", "zzz_unique"):
        poly_domain(S(v), ring=ring)
        ratfunc_domain(S(v), ring=ring)
    assert set(_DOMAINS) == before, "parameterized instances flooded the registry"


def test_registry_consumed_by_projection():
    import cas.math.project  # noqa: F401  trigger assembly
    for name, cls in [("Z", "ZDomain"), ("Q", "QDomain"), ("Q(i)", "QIDomain")]:
        d = lookup(name)
        assert d is not None, f"{name} is not registered"
        assert type(d).__name__ == cls


def test_factory_cache_reuses_same_var_set():
    from cas.math.domains.poly import poly_domain
    from cas.math.domains.ratfunc import ratfunc_domain
    ring = _ring()
    assert poly_domain(S("x"), ring=ring) is poly_domain(S("x"), ring=ring)
    assert ratfunc_domain(S("x"), ring=ring) is ratfunc_domain(S("x"), ring=ring)
    assert poly_domain(S("x"), ring=ring) is not poly_domain(S("y"), ring=ring)


def test_register_has_single_call_site():
    """Registration has one responsibility: the whole project calls register() in
    exactly one place, cas/math/project.py.

    Pin the file but not the line number -- line numbers drift with ordinary edits, so
    pinning them only invites churn.
    """
    import pathlib
    hits = []
    for p in pathlib.Path("cas").rglob("*.py"):
        for i, line in enumerate(p.read_text(encoding="utf-8").splitlines(), 1):
            s = line.strip()
            if s.startswith("register(") and "def register(" not in s:
                hits.append(f"{p.as_posix()}:{i}")
    assert len(hits) == 1, f"registration is not single-sited: {hits}"
    assert hits[0].startswith("cas/math/project.py:"), f"assembly point moved: {hits[0]}"


def test_scoped_registration_available_for_algebraic_extension():
    """An algebraic extension must be confined to the scope of a single computation."""
    from cas.math.domains.base import Domain, domain_scope, register

    class _Tmp(Domain):
        name = "Tmp-scope-test"
        scoped = True

        def normalize(self, t):
            return t

        def equal(self, a, b):
            return a is b

    d = _Tmp()
    with domain_scope(d):
        assert lookup("Tmp-scope-test") is d
    assert lookup("Tmp-scope-test") is None      # unregistered on exit

    try:
        register(d)                              # a scoped domain may not be registered resident
    except ValueError:
        pass
    else:
        raise AssertionError("a scoped domain was allowed resident registration")
