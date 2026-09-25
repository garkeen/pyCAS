# -*- coding: utf-8 -*-
"""Admission gates for the declaration DSL.

Mathematical semantics must be expressed as **DSL text** that can be checked
mechanically: this file asserts against the text rather than reviewing Python
registration statements. That turns the admission disciplines -- unconditional
derivative templates, complete rule guards, declared lifting policies, and honest
Piecewise handling of branch breaking -- into mechanisms instead of review notes.
"""

from pathlib import Path

import pytest

from cas.math.decls import LiftPolicy
from cas.math.loader import load_declarations, parse_declarations
from cas.math.piecewise import is_piecewise
from cas.runtime import Runtime

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


def test_surface_aliases_are_declared(runtime: Runtime):
    """The surface notation ln/sqrt comes from the DSL declaration and is visible in the
    runtime after assembly."""
    d = load_declarations(str(_DSL))
    amap = {record.surface: record.head for record in d.aliases}
    assert amap.get("ln") == "Log" and amap.get("sqrt") == "Sqrt"
    assert runtime.alias_head("sqrt") == "Sqrt"
    assert runtime.alias_head("ln") == "Log"


def test_algorithm_roles_are_declared(runtime: Runtime):
    """The canonical function an algorithm refers to (the logarithm) comes from a DSL
    role declaration rather than being hardcoded in the algorithm."""
    d = load_declarations(str(_DSL))
    rmap = {record.role: record.head for record in d.roles}
    assert rmap.get("logarithm") == "Log"
    assert runtime.role_head("logarithm") == "Log"


def test_lift_policies_are_declared_for_mathematical_heads():
    """Every head that admits lifting -- function or binder -- declares its policy.

    A head without a declaration defaults to forbidden, so this declaration set
    is the complete admission list: a new head entering the lifting channel must
    be declared here first.
    """
    d = parse_declarations(_text())
    policies = {record.head: record.policy for record in d.lifts}
    declared_heads = {function.name for function in d.functions} | {
        binder.head for binder in d.binders
    }
    assert {function.name for function in d.functions} <= set(policies)
    assert set(policies) <= declared_heads
    assert {policy.value for policy in policies.values()} <= {
        "congruent", "conditional", "forbidden"}
    assert "lift Sin = congruent" in _text()
    # a binder body absorbs equality only conditionally, and says so in the DSL
    assert policies.get("Integrate") is LiftPolicy.CONDITIONAL
    assert policies.get("DefIntegrate") is LiftPolicy.CONDITIONAL


def test_binder_display_symbols_are_declared(runtime: Runtime):
    """Binder display symbols come from declarations and survive explicit assembly."""
    d = load_declarations(str(_DSL))
    prints = {record.head: record.print_name for record in d.binders}
    assert prints == {
        "Integrate": "∫",
        "Sum": "Σ",
        "Product": "Π",
        "Limit": "lim",
        "DefIntegrate": "∫",
    }
    for head, symbol in prints.items():
        assert runtime.binder_print(head) == symbol


def test_binder_statement_rejects_malformed_print_clause():
    """A malformed display declaration is a declaration defect, not ignored data."""
    from cas.errors import ParseError

    with pytest.raises(ParseError):
        parse_declarations("binder Foo print")
    with pytest.raises(ParseError):
        parse_declarations("binder Foo print bar")


def test_lift_parser_rejects_unknown_policy():
    from cas.errors import ParseError

    with pytest.raises(ParseError):
        parse_declarations("lift Sin = sometimes")


def test_dsl_is_the_only_declaration_source(runtime: Runtime):
    """The DSL file exists and covers every constant and function; what assembly
    registers matches it entry for entry."""
    d = load_declarations(str(_DSL))
    assert {constant.name for constant in d.constants} == {"pi", "e", "i", "gamma"}
    assert {function.name for function in d.functions} == {
        "Sin", "Cos", "Tan", "Sinh", "Cosh", "Tanh", "Exp", "Log", "Sqrt",
        "Abs", "Atan",
    }
    stats = runtime.stats()
    assert stats.constants == len(d.constants)
    assert stats.functions == len(d.functions)
    assert stats.binders == len(d.binders)
    assert stats.rules == len(d.rules)


def test_binder_heads_are_declared(runtime: Runtime):
    """The bound heads come from the DSL `binder` statement and are visible in the
    runtime, so the parser holds no binder table of its own. The surface word that
    reaches a binder head is an ordinary alias declaration."""
    d = load_declarations(str(_DSL))
    binder_heads = {record.head for record in d.binders}
    assert binder_heads == {"Integrate", "Sum", "Product", "Limit", "DefIntegrate"}
    for head in binder_heads:
        assert runtime.is_binder(head) is True, head
    assert runtime.is_binder("Sin") is False
    aliases = {record.surface: record.head for record in d.aliases}
    for word, head in (("integrate", "Integrate"), ("sum", "Sum"),
                       ("product", "Product"), ("limit", "Limit"),
                       ("int", "DefIntegrate")):
        assert aliases.get(word) == head, word


def test_statement_dispatch_rejects_everything_it_does_not_know():
    """A declaration statement the DSL does not admit is a declaration defect and
    raises, and a malformed binder statement does not slip through as data."""
    from cas.errors import ParseError
    with pytest.raises(ParseError):
        parse_declarations("bind Integrate")
    with pytest.raises(ParseError):
        parse_declarations("binder")
    with pytest.raises(ParseError):
        parse_declarations("binder Foo Bar")


def test_admission_auto_rules_have_no_guard():
    """An auto rule may only be unconditional: a branch-breaking rewrite must not land
    silently (the text side of the invariant)."""
    d = parse_declarations(_text())
    auto = [rule for rule in d.rules if rule.auto]
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
    pw = [function for function in d.functions
          if function.deriv is not None and is_piecewise(function.deriv)]
    assert [function.name for function in pw] == ["Abs"], \
        f"the branch-breaking derivative set changed: {[f.name for f in pw]}"
    for function in d.functions:
        if function.name in ("Tan", "Log", "Sqrt", "Exp"):
            assert function.note, f"{function.name} does not record its branch-breaking reason"


def test_dsl_templates_parse_with_debruijn_placeholder():
    """Templates parse through the de Bruijn placeholder and literals are already folded
    (-2 is Int(-2), not Times(-1,2))."""
    from cas.syntax import term as T
    from cas.syntax.term import Int
    d = parse_declarations(_text())
    by = {function.name: function for function in d.functions}
    # the Cos template is -Sin(@0): after folding, Times(Int(-1), Sin(DB0))
    template = by["Cos"].deriv
    assert isinstance(template, T.Expr) and template.head.name == "Times"
    assert any(isinstance(argument, Int) and argument.v == -1 for argument in template.args)
    tan_template = by["Tan"].deriv
    assert tan_template.head.name == "Power" and isinstance(tan_template.args[1], Int) \
        and tan_template.args[1].v == -2
    from cas.syntax.termpath import postorder
    absolute_template = by["Abs"].deriv
    assert is_piecewise(absolute_template)
    assert any(isinstance(node, T.DB) and node.i == 0 for node in postorder(absolute_template))

