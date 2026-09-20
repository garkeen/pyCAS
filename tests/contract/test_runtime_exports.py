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
    import cas.syntax.parse as P
    assert not hasattr(P, "_CONSTS")                   # the old hardcoded table is gone
    assert set(P._SYNTAX_ATOMS) == {"infinity", "true", "false"}


def test_domain_condition_single_registration_channel():
    import cas.math.domcond as DC
    assert not hasattr(DC, "DOM_HOOKS")                # the empty-shell channel is gone


def test_importing_math_has_no_registration_side_effect():
    """No import-time mutation of global state, and no declaration handle either.

    In a clean process, import only the math modules: the domain ladder stays empty
    and a freshly built context is empty, so nothing was registered behind the
    reader's back. The handles declarations used to travel through (`_DECLS`,
    `_EQ_STAGES`) must be gone rather than merely unwritten: a second channel would
    leave a reader unable to tell which one is in effect.
    """
    import subprocess
    import sys
    code = ("import cas.math.decide, cas.math.diff, cas.math.domcond, "
            "cas.math.rules, cas.math.project; "
            "import cas.math.decide as D; "
            "from cas.math.domains.base import _DOMAINS; "
            "from cas.math.context import MathContext; "
            "c = MathContext(); "
            "print(len(_DOMAINS), len(c.consts), len(c.funcs), len(c.eq_stages), "
            "hasattr(D, '_DECLS'), hasattr(D, '_EQ_STAGES'), "
            "hasattr(D, 'bind_runtime'))")
    r = subprocess.run([sys.executable, "-c", code], capture_output=True,
                       text=True, cwd=".")
    assert r.returncode == 0, r.stderr
    assert r.stdout.strip() == "0 0 0 0 False False False", r.stdout


def test_reading_semantics_before_assembly_raises():
    """Reading the semantics before the application assembled them is a wiring error.

    The query exit names the fix instead of assembling a runtime on the first
    attribute read: a module that assembles itself hides an application-level
    decision inside a read.
    """
    import subprocess
    import sys
    code = ("import cas.runtime.dispatch as disp\n"
            "try:\n"
            "    disp.get_runtime()\n"
            "except RuntimeError as e:\n"
            "    print('refused' if 'install(bootstrap())' in str(e) else 'wrong message')\n"
            "else:\n"
            "    print('assembled silently')\n")
    r = subprocess.run([sys.executable, "-c", code], capture_output=True,
                       text=True, cwd=".")
    assert r.returncode == 0, r.stderr
    assert r.stdout.strip() == "refused", r.stdout


def test_semantics_complete_after_bootstrap():
    rt = dispatch.get_runtime()
    s = rt.stats()
    assert s["constants"] == 4 and s["functions"] == 11
    assert s["domain_conds"] == 2 and s["eq_stages"] == 1 and s["domains"] == 3
