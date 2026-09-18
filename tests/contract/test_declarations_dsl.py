# -*- coding: utf-8 -*-
"""Admission gates for the declaration DSL.

Mathematical semantics must be expressed as **DSL text** that can be checked
mechanically: this file asserts against the text rather than reviewing Python
registration statements. That is what turns "admit only unconditional identities" and
"a branch-breaking template is left empty with the reason recorded" into mechanisms
instead of something a human has to notice in code.
"""

from pathlib import Path

from cas.math.loader import load_declarations, parse_declarations, parse_rule_line
from cas.math.piecewise import is_piecewise

# Walk up to the directory that contains `cas/`: this test may live at any depth
# under tests/, so a fixed parents[1] would break on a future reclassification.
_ROOT = next(p for p in Path(__file__).resolve().parents if (p / "cas").is_dir())
_DSL = _ROOT / "cas" / "math" / "elementary" / "declarations.dsl"


def _text():
    return _DSL.read_text(encoding="utf-8")


def test_elementary_module_has_no_python_declarations():
    """The elementary module may no longer hardcode head names: all semantics come from
    the DSL file."""
    src = (_ROOT / "cas" / "math" / "elementary" / "module.py").read_text(
        encoding="utf-8")
    for head in ('"Sin"', '"Cos"', '"Tan"', '"Exp"', '"Log"', '"Sqrt"',
                 '"Abs"', '"Atan"'):
        assert head not in src, f"module.py hardcodes the head name {head}"
    # the parser must not hardcode surface notation either (sqrt/ln are declared aliases)
    psrc = (_ROOT / "cas" / "frontend" / "parser.py").read_text(encoding="utf-8")
    assert '"sqrt"' not in psrc and '"ln"' not in psrc, \
        "the parser still hardcodes surface notation (it should use the declared alias table)"


def test_surface_aliases_are_declared():
    """The surface notation ln/sqrt comes from the DSL declaration and is visible in the
    runtime after assembly."""
    from cas.runtime import dispatch
    d = load_declarations(str(_DSL))
    amap = dict(d.aliases)
    assert amap.get("ln") == "Log" and amap.get("sqrt") == "Sqrt"
    assert dispatch.alias_head("sqrt") == "Sqrt"
    assert dispatch.alias_head("ln") == "Log"


def test_algorithm_roles_are_declared():
    """The canonical function an algorithm refers to (the logarithm) comes from a DSL
    role declaration rather than being hardcoded in the algorithm."""
    from cas.runtime import dispatch
    d = load_declarations(str(_DSL))
    rmap = dict(d.roles)
    assert rmap.get("logarithm") == "Log"
    assert dispatch.role_head("logarithm") == "Log"


def test_dsl_is_the_only_declaration_source():
    """The DSL file exists and covers every constant and function; what assembly
    registers matches it entry for entry."""
    from cas.runtime import dispatch
    d = load_declarations(str(_DSL))
    assert {c["name"] for c in d.constants} == {"pi", "e", "i", "gamma"}
    assert {f["name"] for f in d.functions} == {
        "Sin", "Cos", "Tan", "Sinh", "Cosh", "Tanh", "Exp", "Log", "Sqrt",
        "Abs", "Atan",
    }
    rt = dispatch.get_runtime()
    assert rt.stats()["constants"] == len(d.constants)
    assert rt.stats()["functions"] == len(d.functions)
    assert rt.stats()["rules"] == len(d.rules)


def test_admission_auto_rules_have_no_guard():
    """An auto rule may only be unconditional: a branch-breaking rewrite must not land
    silently (the text side of the invariant)."""
    d = parse_declarations(_text())
    auto = [parse_rule_line(l) for l in d.rules]
    auto = [r for r in auto if r.auto]
    assert auto, "the DSL has no auto rule, so the admission check has nothing to test"
    for r in auto:
        assert r.guard is None, f"an auto rule carries a guard: {r.id}"


def test_admission_branch_breaking_derivs_are_honest():
    """A branch-breaking derivative must be written honestly as a Piecewise, with the
    reason recorded in the DSL text.

    The only such function in the system today is Abs (no branch at u=0, hence not
    differentiable there). The assertion is that it is not smuggled through as an
    "unconditional" formula but declared as a Piecewise container with a note.
    """
    d = parse_declarations(_text())
    pw = [f for f in d.functions
          if f.get("deriv") is not None and is_piecewise(f["deriv"])]
    assert [f["name"] for f in pw] == ["Abs"], \
        f"the branch-breaking derivative set changed, re-check admission: {[f['name'] for f in pw]}"
    for f in d.functions:
        if f["name"] in ("Tan", "Log", "Sqrt", "Exp") :
            assert f.get("note"), f"{f['name']} does not record the reason for its branch-breaking rewrite"


def test_dsl_templates_parse_with_debruijn_placeholder():
    """Templates parse through the de Bruijn placeholder and literals are already folded
    (-2 is Int(-2), not Times(-1,2))."""
    from cas.syntax import term as T
    from cas.syntax.term import Int
    d = parse_declarations(_text())
    by = {f["name"]: f for f in d.functions}
    # the Cos template is -Sin(@0): after folding, Times(Int(-1), Sin(DB0))
    tpl = by["Cos"]["deriv"]
    assert isinstance(tpl, T.Expr) and tpl.head.name == "Times"
    assert any(isinstance(a, Int) and a.v == -1 for a in tpl.args)
    # the Tan template is Cos(@0)^(-2): the exponent is Int(-2)
    t = by["Tan"]["deriv"]
    assert t.head.name == "Power" and isinstance(t.args[1], Int) \
        and t.args[1].v == -2
    # the Abs template is Piecewise(...), whose conditions contain DB(0)
    from cas.syntax.termpath import postorder
    tpl_abs = by["Abs"]["deriv"]
    assert is_piecewise(tpl_abs)
    assert any(isinstance(u, T.DB) and u.i == 0 for u in postorder(tpl_abs))
