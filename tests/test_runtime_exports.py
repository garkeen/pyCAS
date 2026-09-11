# -*- coding: utf-8 -*-
"""Runtime query exits: mathematical semantics have a single home and **must be
explicitly assembled**.

Nail: constants once carried a print_name in their declaration but had no query exit,
so the kernel had to keep a hardcoded table in both pprint and parser. After the exit
was added, the kernel must hold no copy.

Since stage 6 there is one more rule: the semantics must come from an **explicit
bootstrap**, not from an import side effect.
"""

from cas.runtime import dispatch


def test_const_by_name_returns_declaration():
    d = dispatch.const_by_name("gamma")
    assert d is not None
    assert d.print_name == "γ"
    assert d.real is True


def test_const_by_name_missing_returns_none():
    assert dispatch.const_by_name("__nope__") is None


def test_is_const_name_distinguishes_const_and_function():
    assert dispatch.is_const_name("pi") is True
    assert dispatch.is_const_name("e") is True
    assert dispatch.is_const_name("Sin") is False      # a function head is not a constant


def test_print_name_covers_constants_and_functions():
    assert dispatch.print_name("gamma") == "γ"
    assert dispatch.print_name("pi") == "π"
    assert dispatch.print_name("Sin") == "sin"          # functions use the same exit
    assert dispatch.print_name("__nope__") is None


def test_const_literals_live_in_runtime_not_kernel():
    """The kernel must hold no name-to-constant-atom copy table."""
    import cas.frontend.parser as P
    assert not hasattr(P, "_CONSTS")                   # the old hardcoded table is gone
    assert set(P._SYNTAX_ATOMS) == {"infinity", "true", "false"}


def test_domain_condition_single_registration_channel():
    import cas.math.domcond as DC
    assert not hasattr(DC, "DOM_HOOKS")                # the empty-shell channel is gone


def test_importing_math_has_no_registration_side_effect():
    """No import-time mutation of global state.

    In a clean process, import only the math modules: the constant table, function
    table, domain ladder, and identity stages must all be empty.
    """
    import subprocess
    import sys
    code = ("import cas.math.decide, cas.math.diff, cas.math.domcond, "
            "cas.math.rules, cas.math.project; "
            "from cas.math.decide import _EQ_STAGES; "
            "from cas.math.domains.base import _DOMAINS; "
            "import cas.math.decide as D; "
            "print(len(_EQ_STAGES), len(_DOMAINS), D._DECLS is None)")
    r = subprocess.run([sys.executable, "-c", code], capture_output=True,
                       text=True, cwd=".")
    assert r.returncode == 0, r.stderr
    assert r.stdout.strip() == "0 0 True", r.stdout


def test_semantics_complete_after_bootstrap():
    rt = dispatch.get_runtime()
    s = rt.stats()
    assert s["constants"] == 4 and s["functions"] == 11
    assert s["domain_conds"] == 2 and s["eq_stages"] == 1 and s["domains"] == 3
