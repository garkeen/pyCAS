# -*- coding: utf-8 -*-
"""Architecture invariant gates.

Everything mechanically checkable is asserted here. A property not yet migrated keeps
an xfail with the gap written into the reason, so CI shows a visible spectrum rather
than claims scattered through documentation.

The invariants pinned here:

* Term carries no guard/context/proof field
* Pattern is not a Term
* a checker does not import its own search algorithm
* an unverified candidate takes part in no trusted derivation
* automatic simplification applies no unproved conditional rule
"""

import inspect
from pathlib import Path

import pytest

from cas.runtime import new_workflow
from cas.syntax import term as T
from cas.syntax import pattern as P

# Walk up to the directory that contains `cas/`: this test may live at any depth
# under tests/, so a fixed parents[N] would break on a future reclassification.
_ROOT = next(p for p in Path(__file__).resolve().parents if (p / "cas").is_dir())


# ---------------------------------------------------------------------------
# Dependency direction: a pointer or an import may only point at a lower layer.
# ---------------------------------------------------------------------------

def _cas_imports(path):
    """Statically collect the cas.* / library module names a file imports, including
    imports inside functions."""
    import ast
    tree = ast.parse(path.read_text(encoding="utf-8"))
    found = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.ImportFrom) and node.module:
            if node.module.startswith(("cas.", "library")):
                found.add(node.module)
        elif isinstance(node, ast.Import):
            for a in node.names:
                if a.name.startswith(("cas.", "library")):
                    found.add(a.name)
    return found


def _pkg_modules(*parts):
    return sorted((_ROOT / "cas").joinpath(*parts).glob("*.py"))


def test_dependency_frontend_only_api_workflow_runtime():
    """The frontend may depend only on `api` / `workflow` / `runtime`.

    Concrete math modules and the kernel may not be imported directly: computation and
    decision facilities leave through `cas/api.py` (the REPL previously imported seven
    math modules plus `kernel.verdict` directly, bypassing the rule).

    syntax and the top-level `cas.errors` are outside this gate: parser and pprint are
    frontend work built on the syntax layer, and a literal reading of the rule would
    move parsing and printing out of frontend, a larger structural change that remains
    an open question.
    """
    bad = []
    for p in sorted((_ROOT / "cas" / "frontend").rglob("*.py")):
        for m in _cas_imports(p):
            if m.startswith(("cas.math", "cas.kernel")):
                bad.append(f"{p.relative_to(_ROOT)} -> {m}")
    assert not bad, "frontend imports math/kernel directly:\n" + "\n".join(bad)


def test_dependency_syntax_not_upward():
    """syntax may depend only on the standard library and cas.errors."""
    bad = []
    for p in _pkg_modules("syntax"):
        for m in _cas_imports(p):
            if not m.startswith("cas.syntax") and m != "cas.errors":
                bad.append(f"cas/syntax/{p.name} -> {m}")
    assert not bad, "syntax depends on an upper layer:\n" + "\n".join(bad)


def test_dependency_kernel_not_math_or_workflow():
    """kernel may depend only on syntax, never on math / workflow / frontend / library."""
    bad = []
    for p in _pkg_modules("kernel"):
        for m in _cas_imports(p):
            if m.startswith(("cas.math", "cas.workflow", "cas.frontend", "library")):
                bad.append(f"cas/kernel/{p.name} -> {m}")
    assert not bad, "kernel depends on an upper layer:\n" + "\n".join(bad)


def test_dependency_math_not_runtime():
    """The direction is runtime -> math (bootstrap pulls every math module), so the
    reverse is forbidden.

    A math module must therefore receive the declaration surface by **injection** at
    assembly time (bind_runtime) rather than importing runtime, which would put the
    import chain back in a cycle.
    """
    bad = []
    for p in sorted((_ROOT / "cas" / "math").rglob("*.py")):
        for m in _cas_imports(p):
            if m.startswith("cas.runtime"):
                bad.append(f"{p.relative_to(_ROOT)} -> {m}")
    assert not bad, "math depends on runtime: " + ", ".join(bad)


def test_dependency_math_not_frontend():
    """A math module may not import the frontend: the dependency table lists syntax
    / kernel / workflow / math.domains only. The declaration DSL parses through the
    syntax layer (cas.syntax.parse), not the frontend parser, so the trusted
    admission channel does not rest on a UI-layer module."""
    bad = []
    for p in sorted((_ROOT / "cas" / "math").rglob("*.py")):
        for m in _cas_imports(p):
            if m.startswith("cas.frontend"):
                bad.append(f"{p.relative_to(_ROOT)} -> {m}")
    assert not bad, "a math module imports the frontend:\n" + "\n".join(bad)


def test_dependency_domains_syntax_only():
    """math/domains may depend only on syntax (plus itself and cas.errors). A
    domain never knows the kernel, workflow, frontend, runtime, or a non-domain
    math module; qarith lives inside the package as the domains' literal-arithmetic
    substrate, so the documented rule "math/domains depends on syntax" is now a
    mechanical fact rather than a convention."""
    bad = []
    for p in _pkg_modules("math", "domains"):
        for m in _cas_imports(p):
            if m == "cas.errors" or m == "cas.syntax" or m.startswith("cas.syntax.") \
                    or m == "cas.math.domains" or m.startswith("cas.math.domains."):
                continue
            bad.append(f"cas/math/domains/{p.name} -> {m}")
    assert not bad, "a domain module depends on an upper layer:\n" + "\n".join(bad)


def test_dependency_workflow_not_concrete_math():
    """workflow depends only on syntax plus kernel.

    Checkers live in `math/*/checkers.py`, so the workflow no longer holds verification
    logic; this gate is therefore green.
    """
    bad = [f"cas/workflow/{p.name} -> {m}"
           for p in _pkg_modules("workflow")
           for m in _cas_imports(p) if m.startswith("cas.math")]
    assert not bad, "workflow depends on concrete math modules:\n" + "\n".join(bad)


def test_reference_direction_kernel_ignores_workflow_concepts():
    """The kernel side may not contain workflow-concept names such as Artifact/Task/Event.

    Names are collected via AST rather than string matching, so comments and docstrings
    explaining the direction are unaffected, and the rule also closes the
    "bypass through an object field or duck typing" route: the kernel may not even
    mention these names.
    """
    import ast
    forbidden = {"ArtifactId", "TaskId", "EventId", "RevisionId",
                 "Artifact", "Task", "TaskCandidate", "Constraint",
                 "Event", "Revision", "BranchGroup", "BranchCase", "Focus"}
    bad = []
    for p in _pkg_modules("kernel"):
        tree = ast.parse(p.read_text(encoding="utf-8"))
        for node in ast.walk(tree):
            if isinstance(node, ast.Name) and node.id in forbidden:
                bad.append(f"cas/kernel/{p.name}:{node.lineno} {node.id}")
            elif isinstance(node, ast.Attribute) and node.attr in forbidden:
                bad.append(f"cas/kernel/{p.name}:{node.lineno} .{node.attr}")
            elif isinstance(node, (ast.ClassDef, ast.FunctionDef)) \
                    and node.name in forbidden:
                bad.append(f"cas/kernel/{p.name}:{node.lineno} def {node.name}")
    assert not bad, "the kernel mentions workflow concepts:\n" + "\n".join(bad)


def _term_variants():
    out = []
    for obj in vars(T).values():
        if inspect.isclass(obj) and issubclass(obj, T.Term) and obj is not T.Term:
            out.append(obj)
    return out


def test_invariant1_term_has_no_guard_or_proof_fields():
    """A Term answers only "what does it look like": it may not carry guard/context/
    proof/history fields."""
    forbidden = {"guard", "guards", "context", "proof", "history", "domain",
                 "integration_constant", "substitution_variable", "ode_solution"}
    variants = _term_variants()
    assert variants, "no Term variant found: the variant collection logic is broken"
    for cls in variants:
        slots = set(getattr(cls, "__slots__", ()))
        bad = slots & forbidden
        assert not bad, f"{cls.__name__} carries an illegal field: {sorted(bad)}"


def test_invariant2_pattern_is_not_term():
    """PatternVar/PatternSeq/PatternCall are outside the Term hierarchy."""
    for cls in (P.PatternVar, P.PatternSeq, P.PatternCall):
        assert not issubclass(cls, T.Term), f"{cls.__name__} is still a Term subclass"
    # the term layer must not expose pattern-variable constructors
    assert not hasattr(T, "PatVar"), "the term layer still exposes PatVar"
    assert not hasattr(T, "PatSeq"), "the term layer still exposes PatSeq"
    assert not hasattr(T, "PV") and not hasattr(T, "PS"), "the term layer still exposes PV/PS"
    # the variant inventory must not contain pattern variables
    names = {c.__name__ for c in _term_variants()}
    assert not (names & {"PatVar", "PatSeq"}), f"term variants include pattern variables: {names}"


def test_invariant2_no_pattern_var_inside_term():
    """The pattern channel produces a Pattern and the normal channel rejects ?x, so a
    hole cannot enter a Term."""
    from cas.frontend.parser import parse
    from cas.errors import ParseError

    pat = parse("exp(?a)*exp(?b)", pattern=True)
    assert isinstance(pat, P.PatternCall)
    assert not isinstance(pat, T.Term)
    # normal channel: ?x is pattern notation, not an expression
    with pytest.raises(ParseError):
        parse("exp(?a)")
    with pytest.raises(ParseError):
        parse("f(??xs)")


def test_invariant2_instantiation_yields_term():
    """Template instantiation must land in the Term layer, and an unbound hole must
    raise explicitly rather than leak."""
    from cas.frontend.parser import parse
    from cas.syntax.match import matches
    from cas.errors import ParseError

    tpl = parse("exp(?a + ?b)", pattern=True)
    tgt = parse("exp(x)*exp(y)")
    subs = list(matches(parse("exp(?a)*exp(?b)", pattern=True), tgt))
    assert subs, "the rule pattern did not match the target"
    inst = P.instantiate(tpl, subs[0])
    assert isinstance(inst, T.Term) and not isinstance(inst, P.Pattern)
    with pytest.raises(ParseError):
        P.instantiate(tpl, {"a": T.S("x")})   # ?b unbound: a rule defect, raise explicitly


def test_rule_no_hardcoded_math_semantics_head():
    """A mathematical-semantics head (an elementary function) may not appear as a literal
    in any Python module.

    The mechanical criterion is: would changing the function name require changing this
    code? If yes, it is hardcoding. **Signature heads** (Plus/Times/Power/Eq/Lt/And/Or/
    Not/Quote/Piecewise) are outside the gate: they are the term language's own structure
    (an equality decider must know Eq and a differentiator must know Plus). Declaration
    files are `.dsl` and outside this scan.
    """
    import ast
    heads = {"Sin", "Cos", "Tan", "Atan", "Sinh", "Cosh", "Tanh", "Exp",
             "Log", "Sqrt", "Abs"}
    bad = []
    for p in sorted((_ROOT / "cas").rglob("*.py")):
        tree = ast.parse(p.read_text(encoding="utf-8"))
        for node in ast.walk(tree):
            if isinstance(node, ast.Constant) and isinstance(node.value, str) \
                    and node.value in heads:
                bad.append(f"{p.relative_to(_ROOT)}:{node.lineno} {node.value!r}")
    assert not bad, "a mathematical-semantics head is hardcoded:\n" + "\n".join(bad)


def test_invariant18_auto_simplify_skips_unproved_conditional_rules():
    """An auto rule may only be unconditional; a guarded one is never auto, so a
    branch-breaking rewrite cannot land silently."""
    from cas.math.rules import declared_ruleset
    rs = declared_ruleset()
    bad = [r.id for r in rs.rules.values() if r.auto and r.guard is not None]
    assert not bad, f"an auto rule carries a guard: {bad}"


def test_invariant14_checker_does_not_import_own_search():
    """A checker only verifies a given instance: it imports no searcher and walks no paths.

    The proponent of a rule rewrite supplies the instance (rule + path + substitution)
    and the checker re-checks that instance; "find where and which rule applies" is the
    proponent's search and does not enter the checker.
    """
    import importlib
    mods = ("cas.math.base.checkers",
            "cas.math.calculus.differentiation.checkers",
            "cas.math.calculus.integration.checkers",
            "cas.math.solving.equations.checkers",
            "cas.kernel.services")
    bad = []
    for mod in mods:
        m = importlib.import_module(mod)
        for name in dir(m):
            obj = getattr(m, name)
            if inspect.isclass(obj) and name.endswith("Checker"):
                names = obj.check.__code__.co_names
                for forbidden in ("apply_rule", "all_paths"):
                    if forbidden in names:
                        bad.append(f"{mod}.{name}.{forbidden}")
    assert not bad, f"a checker depends on a search algorithm: {bad}"


_CHECKER_OF_SOLVER = {
    # checker file -> (forbidden modules, forbidden (module, name) pairs)
    "cas/math/calculus/integration/checkers.py": ({"cas.math.integrate"}, set()),
    "cas/math/calculus/integration/verify.py": ({"cas.math.integrate"}, set()),
    "cas/math/calculus/differentiation/checkers.py": ({"cas.math.diff"}, set()),
    "cas/math/solving/equations/checkers.py": ({"cas.math.tactics"}, set()),
    # the rule data declared_ruleset is available; the searcher apply_rule is not
    "cas/math/base/checkers.py": (set(), {("cas.math.rules", "apply_rule")}),
}


def _static_imports(path):
    """Every import in a file as (module name, name), including imports inside
    functions."""
    import ast
    tree = ast.parse(path.read_text(encoding="utf-8"))
    out = []
    for node in ast.walk(tree):
        if isinstance(node, ast.ImportFrom) and node.module:
            for a in node.names:
                out.append((node.module, a.name))
        elif isinstance(node, ast.Import):
            for a in node.names:
                out.append((a.name, None))
    return out


def test_invariant14_checker_does_not_import_solver_module():
    """A checker may not import the search algorithm it verifies.

    The previous check only looked at two names inside `check.__code__.co_names`, a weak
    proxy: renaming the solver, or importing another function from the solver module,
    would slip through. This one verifies the **import surface** statically, including
    imports inside functions, so the solver/verifier split is a structural fact rather
    than a naming convention.
    """
    bad = []
    for rel, (mods, syms) in _CHECKER_OF_SOLVER.items():
        for mod, name in _static_imports(_ROOT / rel):
            if mod in mods or (mod, name) in syms:
                bad.append(f"{rel} -> {mod}" + (f".{name}" if name else ""))
    assert not bad, "a checker imports the solving algorithm:\n" + "\n".join(bad)


def test_solver_module_does_not_contain_verifier():
    """The solver module may not carry a verifier of its own (the same split pinned from
    the other side)."""
    src = (_ROOT / "cas/math/integrate.py").read_text(encoding="utf-8")
    assert "def verify_antideriv" not in src, "the verifier moved back into the solver module"
    assert "def _judge_zero_diff" not in src, "zero re-checking moved back into the solver module"


def test_rule_instance_checker_only_accepts_given_instance():
    """A substitution/path that does not match the instance is refused; one that matches
    passes (no search of other paths or matches)."""
    from cas.frontend.parser import parse
    from cas.workflow.command import Claim, Rewrite

    wf = new_workflow()
    wf.add(parse("exp(x)*exp(y)"), Claim())
    X, Y = parse("x"), parse("y")
    good = wf.add(parse("exp(x + y)"),
                  Rewrite(pred=0, rule="exp_add", path=(),
                          substitution={"a": X, "b": Y}))
    assert good.status == "committed", good.note
    assert good.judgment is not None
    # the substitution is not a valid match at that position (?a and ?b both bound to x), so refuse
    wrong = wf.add(parse("exp(x + y)"),
                   Rewrite(pred=0, rule="exp_add", path=(),
                           substitution={"a": X, "b": X}))
    assert wrong.status == "refused", wrong.note
    assert wrong.judgment is None
    # a path out of bounds is refused
    oob = wf.add(parse("exp(x + y)"),
                 Rewrite(pred=0, rule="exp_add", path=(5,),
                         substitution={"a": X, "b": Y}))
    assert oob.status == "refused", oob.note


def test_invariant16_unverified_candidate_not_trusted():
    """A candidate the checker leaves undecided may not enter the ledger in a
    dependable state: unverified is not open."""
    from cas.frontend.parser import parse
    from cas.syntax.term import S, N
    from cas.workflow.command import Claim, Solve

    wf = new_workflow()
    wf.add(parse("sin(x) == 1/2"), Claim())
    before = dict(wf.store.stats())
    # the back-substitution judge is honestly undecided outside the projection
    # (transcendental function), so the checker returns UnknownResult
    step = wf.add(parse("x == 1"), Solve(pred=0, var=S("x"), solution=N(1)))
    assert step.status == "undecided", \
        f"an undecided candidate should be unverified, got {step.status}"
    assert step.judgment is None, "an undecided candidate may not hold a dependable conclusion"
    assert dict(wf.store.stats()) == before, "an undecided candidate must write nothing to the ledger"


# ---------------------------------------------------------------------------
# The persistent Scope tree takes over the mutable context
# ---------------------------------------------------------------------------

def test_phase5_old_mutable_context_removed():
    """The old mutable context (mutable entries plus marks/rollback) must not come back."""
    from cas.kernel import context as C
    for name in ("Context", "Entry", "Branch"):
        assert not hasattr(C, name), f"the old mutable context survives: {name}"
    assert hasattr(C, "TrackedContext"), "the checker read channel is missing"


def test_assumptions_immutable_and_extend_creates_new():
    """The assumption set is a read-only projection of Scope: `extended` does not write
    in place, so no clone or undo is needed."""
    from cas.kernel.scope import Assumptions, ScopeStore
    base = Assumptions()
    ext = base.extended(T.S("p"))
    assert base.items == () and ext.items == (T.S("p"),)
    assert base is not ext
    assert len(base) == 0 and list(ext) == [T.S("p")]

    # Scope is the authoritative source; Assumptions.of is its projection in the decision layer
    from cas.kernel.model import Assumption
    st = ScopeStore()
    root = st.create()
    child = st.child(root, assumptions=(Assumption(T.S("q")),))
    assert Assumptions.of(st, child.id).items == (T.S("q"),)
    assert Assumptions.of(st, root.id).items == ()


# ---------------------------------------------------------------------------
# Language policy: English code and comments, and no design-document citations
# ---------------------------------------------------------------------------

_CJK_RANGES = ((0x3000, 0x303F), (0x4E00, 0x9FFF), (0xFF00, 0xFFEF))
# `tests/` covers tests/random/ too; the old top-level stress/ dir is gone.
_SOURCE_DIRS = ("cas", "tests")


def _source_files():
    for d in _SOURCE_DIRS:
        for p in sorted((_ROOT / d).rglob("*")):
            if p.suffix in (".py", ".dsl"):
                yield p


def _cjk_count(text):
    return sum(1 for ch in text
               if any(lo <= ord(ch) <= hi for lo, hi in _CJK_RANGES))


def test_source_is_english_only():
    """Every source file is written in English, so a non-ASCII CJK character in code or
    comments is a regression."""
    bad = []
    for p in _source_files():
        n = _cjk_count(p.read_text(encoding="utf-8"))
        if n:
            bad.append(f"{p.relative_to(_ROOT)}: {n}")
    assert not bad, "non-English source text:\n" + "\n".join(bad)


# Assembled from pieces so this file does not contain the strings it forbids.
_DOC_CITATIONS = (
    "cas_v" + "3_arch.md",
    "cas_v" + "4_arch.md",
    "AGENTS" + ".md",
    "v4 " + "\u00a7",
    "v3 " + "\u00a7",
)


def test_source_cites_no_design_document():
    """Code never cites a design document: a rationale is stated plainly instead of
    pointing the reader at a document to chase."""
    bad = []
    for p in _source_files():
        text = p.read_text(encoding="utf-8")
        for needle in _DOC_CITATIONS:
            if needle in text:
                bad.append(f"{p.relative_to(_ROOT)}: {needle}")
    assert not bad, "source cites a design document:\n" + "\n".join(bad)
