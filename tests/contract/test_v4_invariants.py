# -*- coding: utf-8 -*-
"""Architecture invariant gates.

Everything mechanically checkable is asserted here. Each gate names the
architectural invariant it protects; a property that is not yet mechanically
checkable is documented as missing rather than represented by a placeholder test.

The invariants pinned here:

* Term carries no guard/context/proof field (1)
* Pattern is not a Term (2)
* only commit creates a Judgment (3) and writes the ledger (13)
* an Artifact cannot be a mathematical premise (4)
* an open requirement never enters Scope.assumptions (5)
* checker conditions are recorded by the kernel (6)
* premises must predate the step that uses them, so the dependency graph is acyclic (11)
* a checker does not import its own search algorithm (14)
* an unverified candidate takes part in no trusted derivation (16)
* automatic simplification applies no unproved conditional rule (18)

plus the bounded-cache discipline: the math layer may hold a module-level cache
only when it is registered in this file and the code shows a cap constant with an
eviction call, and the hash-consing tables must not pin their entries.
"""

import ast
import inspect
from pathlib import Path

import pytest

from cas.runtime import Runtime, new_workflow
from cas.syntax import pattern as P
from cas.syntax import term as T

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


def test_invariant2_no_pattern_var_inside_term(runtime: Runtime):
    """The pattern channel produces a Pattern and the normal channel rejects ?x, so a
    hole cannot enter a Term."""
    from cas.errors import ParseError
    from cas.frontend.parser import parse

    pat = parse(runtime, "exp(?a)*exp(?b)", pattern=True)
    assert isinstance(pat, P.PatternCall)
    assert not isinstance(pat, T.Term)
    with pytest.raises(ParseError):
        parse(runtime, "exp(?a)")
    with pytest.raises(ParseError):
        parse(runtime, "f(??xs)")


def test_invariant2_instantiation_yields_term(runtime: Runtime):
    """Template instantiation must land in the Term layer, and an unbound hole must
    raise explicitly rather than leak."""
    from cas.errors import ParseError
    from cas.frontend.parser import parse
    from cas.syntax.match import matches

    tpl = parse(runtime, "exp(?a + ?b)", pattern=True)
    tgt = parse(runtime, "exp(x)*exp(y)")
    subs = list(matches(parse(runtime, "exp(?a)*exp(?b)", pattern=True), tgt))
    assert subs, "the rule pattern did not match the target"
    inst = P.instantiate(tpl, subs[0])
    assert isinstance(inst, T.Term) and not isinstance(inst, P.Pattern)
    with pytest.raises(ParseError):
        P.instantiate(tpl, {"a": T.S("x")})   # ?b unbound: a rule defect, raise explicitly


def _declared_math_heads():
    """Mathematical-semantics heads, read from the declaration DSL.

    Deriving the list from the DSL text instead of copying it here means a newly
    declared function or binder enters the gate without editing this test.
    """
    from cas.math.loader import parse_declarations

    dsl = (_ROOT / "cas" / "math" / "elementary" / "declarations.dsl").read_text(
        encoding="utf-8")
    declarations = parse_declarations(dsl)
    heads = {function.name for function in declarations.functions}
    heads |= {binder.head for binder in declarations.binders}
    heads |= {role.head for role in declarations.roles}
    return heads


def test_rule_no_hardcoded_math_semantics_head():
    """A mathematical-semantics head may not appear as a literal in any Python module.

    The mechanical criterion is: would changing the declared name require changing this
    code? If yes, it is hardcoding. **Signature heads** (Plus/Times/Power/Eq/Lt/And/Or/
    Not/Quote/Piecewise) are outside the gate: they are the term language's own structure
    (an equality decider must know Eq and a differentiator must know Plus). Declaration
    files are `.dsl` and outside this scan; the head list itself comes from that DSL.
    """
    heads = _declared_math_heads()
    bad = []
    for p in sorted((_ROOT / "cas").rglob("*.py")):
        tree = ast.parse(p.read_text(encoding="utf-8"))
        for node in ast.walk(tree):
            if isinstance(node, ast.Constant) and isinstance(node.value, str) \
                    and node.value in heads:
                bad.append(f"{p.relative_to(_ROOT)}:{node.lineno} {node.value!r}")
    assert not bad, "a mathematical-semantics head is hardcoded:\n" + "\n".join(bad)


def test_invariant18_auto_simplify_skips_unproved_conditional_rules(runtime: Runtime):
    """An auto rule may only be unconditional; a guarded one is never auto, so a
    branch-breaking rewrite cannot land silently."""
    from cas.math.rules import declared_ruleset
    rs = declared_ruleset(runtime.math)
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


def test_rule_instance_checker_only_accepts_given_instance(runtime: Runtime):
    """A substitution/path that does not match the instance is refused; one that matches
    passes (no search of other paths or matches)."""
    from cas.frontend.parser import parse
    from cas.workflow.command import Claim, Rewrite

    wf = new_workflow(runtime)
    wf.add(parse(runtime, "exp(x)*exp(y)"), Claim())
    X, Y = parse(runtime, "x"), parse(runtime, "y")
    good = wf.add(parse(runtime, "exp(x + y)"),
                  Rewrite(pred=0, rule="exp_add", path=(),
                          substitution={"a": X, "b": Y}))
    assert good.status == "committed", good.note
    assert good.judgment is not None
    wrong = wf.add(parse(runtime, "exp(x + y)"),
                   Rewrite(pred=0, rule="exp_add", path=(),
                           substitution={"a": X, "b": X}))
    assert wrong.status == "refused", wrong.note
    assert wrong.judgment is None
    oob = wf.add(parse(runtime, "exp(x + y)"),
                 Rewrite(pred=0, rule="exp_add", path=(5,),
                         substitution={"a": X, "b": Y}))
    assert oob.status == "refused", oob.note


def test_invariant16_unverified_candidate_not_trusted(runtime: Runtime):
    """A candidate the checker leaves undecided may not enter the ledger in a
    dependable state: unverified is not open."""
    from cas.frontend.parser import parse
    from cas.syntax.term import N, S
    from cas.workflow.command import Claim, Solve

    wf = new_workflow(runtime)
    wf.add(parse(runtime, "sin(x) == 1/2"), Claim())
    before = dict(wf.store.stats())
    step = wf.add(parse(runtime, "x == 1"), Solve(pred=0, var=S("x"), solution=N(1)))
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


# ---------------------------------------------------------------------------
# C3: the declaration surface and the assembly configuration are explicit
# ---------------------------------------------------------------------------

_REMOVED_ASSEMBLY_HANDLES = {
    "decide.py": ("_DECLS", "_EQ_STAGES", "bind_runtime", "bind_eq_stages"),
    "rules.py": ("_DECLS", "bind_runtime"),
    "diff.py": ("_DECLS", "bind_runtime"),
    "domcond.py": ("_DECLS", "bind_runtime"),
    "project.py": ("_STAGES", "register_stage", "clear_stages", "bind_domains"),
    "domains/base.py": ("_DEFAULT_COEFF_RING", "default_coeff_ring"),
    "domains/poly.py": ("default_coeff_ring",),
    "domains/ratfunc.py": ("default_coeff_ring",),
}


def test_c3_no_module_level_assembly_state_in_math():
    """No module in the math layer keeps assembly state in a module handle.

    A `global` statement there means a handle that assembly fills in behind the
    reader's back. The declaration surface and the assembly configuration travel
    as explicit arguments instead, so an algorithm cannot read semantics it was
    never given.
    """
    bad = []
    for p in sorted((_ROOT / "cas" / "math").rglob("*.py")):
        tree = ast.parse(p.read_text(encoding="utf-8"))
        for node in ast.walk(tree):
            if isinstance(node, ast.Global):
                bad.append(f"{p.relative_to(_ROOT)}:{node.lineno} -> "
                           + ", ".join(node.names))
    assert not bad, "math layer holds module-level state:\n" + "\n".join(bad)


def test_c3_removed_declaration_handles_stay_removed():
    """The handles assembly used to write into are gone, not merely unused.

    Each name was a second way to reach the declarations, and keeping one around
    leaves a reader unable to tell which channel is in effect.
    """
    math_dir = _ROOT / "cas" / "math"
    bad = []
    for name, needles in _REMOVED_ASSEMBLY_HANDLES.items():
        text = (math_dir / name).read_text(encoding="utf-8")
        for needle in needles:
            if needle in text:
                bad.append(f"cas/math/{name}: {needle}")
    assert not bad, "a removed assembly handle is back:\n" + "\n".join(bad)


# ---------------------------------------------------------------------------
# The remaining mechanically checkable ledger invariants: 3 / 4 / 5 / 6 / 11 / 13
# ---------------------------------------------------------------------------

def _call_sites(name):
    """The cas/ files that call `name`, as a bare or attribute call."""
    found = set()
    for p in sorted((_ROOT / "cas").rglob("*.py")):
        tree = ast.parse(p.read_text(encoding="utf-8"))
        for node in ast.walk(tree):
            if not isinstance(node, ast.Call):
                continue
            func = node.func
            if isinstance(func, ast.Name) and func.id == name:
                found.add(p.relative_to(_ROOT).as_posix())
            elif isinstance(func, ast.Attribute) and func.attr == name:
                found.add(p.relative_to(_ROOT).as_posix())
    return found


def test_invariant3_only_commit_creates_judgments():
    """Only `kernel.commit` may construct a Judgment.

    A Judgment is the ledger's record of a re-checked conclusion; if any other
    module could build one, "candidates become conclusions only at the boundary"
    would be a convention rather than a structural fact.
    """
    sites = _call_sites("Judgment") | _call_sites("put_judgment")
    assert sites == {"cas/kernel/commit.py"}, (
        "a Judgment is created outside commit: " + ", ".join(sorted(sites)))


def test_invariant13_ledger_writes_stay_inside_commit():
    """No module other than commit writes the ledger (step / judgment /
    requirement / discharge / refutation) directly."""
    writers = set()
    for name in ("put_requirement", "put_step", "put_judgment",
                 "add_discharge", "add_refutation",
                 "new_requirement_id", "new_judgment_id", "new_step_id"):
        writers |= _call_sites(name)
    outside = writers - {"cas/kernel/commit.py"}
    assert not outside, "the ledger is written outside commit: " + ", ".join(sorted(outside))


def test_invariant4_artifact_cannot_be_a_mathematical_premise():
    """The premise channel is typed and has no slot an Artifact could enter.

    `Step.premises` is a tuple of JudgmentId, the proposal records carry exactly
    the fields below (no artifact slot), and the kernel does not know the workflow
    id types at all (the reference-direction gate covers the names).
    """
    import dataclasses

    from cas.kernel.commit import ResolvedProposal, StepProposal
    from cas.kernel.model import Step

    assert [f.name for f in dataclasses.fields(StepProposal)] == [
        "scope", "evidence", "premises", "conclusions", "guard_policy"]
    assert [f.name for f in dataclasses.fields(ResolvedProposal)] == [
        "scope", "evidence", "premises", "conclusions", "guard_policy",
        "premise_propositions"]
    premises = next(f for f in dataclasses.fields(Step) if f.name == "premises")
    assert "JudgmentId" in str(premises.type)
    assert "Artifact" not in str(premises.type)


def test_invariant5_open_requirements_do_not_become_scope_assumptions(runtime: Runtime):
    """An open guard stays a Requirement; only the Claim itself becomes an assumption."""
    from cas.frontend.parser import parse
    from cas.workflow.command import Claim

    work = new_workflow(runtime)
    claim = parse(runtime, "1/x")
    step = work.add(claim, Claim())
    assert step.judgment is not None

    open_guards = {
        work.store.get_requirement(rid).proposition
        for rid in work.store.requirements_of(step.judgment)
        if not work.store.is_discharged(rid, work.scope)
    }
    definedness = parse(runtime, "x != 0")
    assert definedness in open_guards

    scope_assumptions = {
        assumption.proposition for assumption in work.store.scopes.assumptions(work.scope)
    }
    assert claim in scope_assumptions, "a committed explicit Claim is an assumption"
    assert not open_guards.intersection(scope_assumptions), (
        "an open Requirement was promoted into Scope.assumptions"
    )


def test_invariant6_checker_conditions_are_recorded_by_the_kernel(runtime: Runtime):
    """Conditions a checker reports land in the ledger as Requirements on the
    committed Judgment, not only in the workflow's presentation record."""
    from cas.frontend.parser import parse
    from cas.workflow.command import Claim

    work = new_workflow(runtime)
    step = work.add(parse(runtime, "1/x"), Claim())
    assert step.judgment is not None
    requirement_ids = work.store.requirements_of(step.judgment)
    assert requirement_ids, "the reported definedness condition was not recorded"
    propositions = {
        work.store.get_requirement(rid).proposition for rid in requirement_ids
    }
    assert any(str(proposition) in ("Ne(x, 0)", "(x != 0)") for proposition in propositions)


def test_budget_exhaustion_leaves_commit_as_undecided():
    """Resource exhaustion is an honest Unknown, not a refutation or exception."""
    from cas.errors import BudgetExceeded
    from cas.kernel.commit import StepProposal, Undecided, commit
    from cas.kernel.evidence import Evidence
    from cas.kernel.store import KernelStore
    from cas.kernel.verdict import Reason

    class BudgetChecker:
        def check(self, proposal, context, services):
            raise BudgetExceeded(message="checker search exhausted")

    store = KernelStore()
    store.checkers.register("budget.exhausted", BudgetChecker())
    root = store.scopes.create()
    before = store.stats()
    result = commit(
        store,
        StepProposal(
            scope=root.id,
            evidence=Evidence("budget.exhausted"),
            conclusions=(T.S("x"),),
        ),
    )

    assert isinstance(result, Undecided)
    assert result.reason is Reason.BUDGET
    assert store.stats() == before


def test_invariant11_premises_must_be_committed_before_use():
    """A dependency edge may only point from an already committed judgment.

    Together with the single ledger write site, this is the structural reason the
    mathematical dependency graph cannot contain a future premise or a cycle.  Two
    negative cases distinguish that guarantee from the behaviour of a normal chain:
    an arbitrary unknown id, and an id already issued by the store but whose
    judgment has not been committed.
    """
    from cas.kernel.commit import Refused, StepProposal, commit
    from cas.kernel.evidence import Evidence
    from cas.kernel.ids import JudgmentId
    from cas.kernel.store import KernelStore
    from cas.kernel.verdict import Reason

    store = KernelStore()
    root = store.scopes.create()
    unissued = JudgmentId(10_000)
    issued_but_uncommitted = store.new_judgment_id()

    for premise in (unissued, issued_but_uncommitted):
        before = store.stats()
        result = commit(
            store,
            StepProposal(
                scope=root.id,
                evidence=Evidence("checker.never.reached"),
                premises=(premise,),
                conclusions=(T.S("x"),),
            ),
        )

        assert isinstance(result, Refused)
        assert result.reason is Reason.FRAGMENT
        assert store.stats() == before


# ---------------------------------------------------------------------------
# C3 addition: a module-level cache reaches the same effect as a `global`
# statement without the keyword, so it needs its own registration and a bound.
# ---------------------------------------------------------------------------

_BOUNDED_CACHES = {
    "cas/math/simplify.py": {"_MEMO": "_MEMO_CAP"},
    "cas/math/domains/poly.py": {"_domain_cache": "_DOMAIN_CACHE_CAP"},
    "cas/math/domains/ratfunc.py": {"_domain_cache": "_DOMAIN_CACHE_CAP"},
}


def _module_level_caches(path):
    """Module-level mutable containers the same file also writes to inside a
    function: a static lookup table is read-only and therefore not a cache."""
    tree = ast.parse(path.read_text(encoding="utf-8"))
    containers = set()
    for node in tree.body:
        if isinstance(node, ast.AnnAssign):
            targets = [node.target]
            value = node.value
        elif isinstance(node, ast.Assign):
            targets = node.targets
            value = node.value
        else:
            continue
        if value is None:
            continue
        literal = isinstance(value, (ast.Dict, ast.List, ast.Set,
                                     ast.DictComp, ast.ListComp, ast.SetComp))
        factory = (
            isinstance(value, ast.Call) and isinstance(value.func, ast.Name)
            and value.func.id in ("dict", "list", "set")
        )
        if not (literal or factory):
            continue
        for target in targets:
            if isinstance(target, ast.Name):
                containers.add(target.id)
    written = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.Assign):
            for target in node.targets:
                if isinstance(target, ast.Subscript) and isinstance(target.value, ast.Name):
                    written.add(target.value.id)
        if isinstance(node, ast.AugAssign) and isinstance(node.target, ast.Name):
            written.add(node.target.id)
        if (
            isinstance(node, ast.Call)
            and isinstance(node.func, ast.Attribute)
            and isinstance(node.func.value, ast.Name)
            and node.func.attr
            in ("append", "add", "update", "setdefault", "pop", "popitem", "clear")
        ):
            written.add(node.func.value.id)
    return containers & written


def test_c3_module_level_caches_are_registered():
    """Every module-level cache in the math layer is explicitly registered."""
    found = {}
    for p in sorted((_ROOT / "cas" / "math").rglob("*.py")):
        names = _module_level_caches(p)
        if names:
            found[p.relative_to(_ROOT).as_posix()] = names
    registered = {path: set(caches) for path, caches in _BOUNDED_CACHES.items()}
    assert found == registered, (
        "the math-layer cache inventory changed; register the new cache and give it "
        f"a bound:\nfound={found}\nregistered={registered}"
    )


def _cache_has_bound_and_eviction(tree: ast.Module, cache: str, cap: str) -> bool:
    """Whether insertion into `cache` is guarded by `len(cache) >= cap` and clear."""
    for node in ast.walk(tree):
        if not isinstance(node, ast.If) or not isinstance(node.test, ast.Compare):
            continue
        comparison = node.test
        if len(comparison.ops) != 1 or not isinstance(comparison.ops[0], ast.GtE):
            continue
        left = comparison.left
        if not (
            isinstance(left, ast.Call)
            and isinstance(left.func, ast.Name)
            and left.func.id == "len"
            and len(left.args) == 1
            and isinstance(left.args[0], ast.Name)
            and left.args[0].id == cache
        ):
            continue
        if len(comparison.comparators) != 1:
            continue
        limit = comparison.comparators[0]
        if not isinstance(limit, ast.Name) or limit.id != cap:
            continue
        if any(
            isinstance(statement, ast.Expr)
            and isinstance(statement.value, ast.Call)
            and isinstance(statement.value.func, ast.Attribute)
            and isinstance(statement.value.func.value, ast.Name)
            and statement.value.func.value.id == cache
            and statement.value.func.attr == "clear"
            for statement in node.body
        ):
            return True
    return False


def test_c3_registered_caches_have_a_bound_and_evict():
    """Each registered cache is actually guarded by its declared cap and evicts."""
    for path, caches in _BOUNDED_CACHES.items():
        source = (_ROOT / path).read_text(encoding="utf-8")
        tree = ast.parse(source)
        for cache, cap in caches.items():
            assert _cache_has_bound_and_eviction(tree, cache, cap), (
                f"{path}: {cache} is not bounded by {cap} with an eviction"
            )


def test_interned_tables_are_bounded():
    """Hash-consing tables must not pin their entries: the term tables are weak
    and every pattern table has its own capacity guard and eviction path."""
    import weakref

    from cas.syntax import term as term_module

    for name in ("_SYMS", "_CONSTS", "_NUMS", "_SPECIALS", "_EXPRS", "_BOUNDS", "_DBS"):
        table = getattr(term_module, name)
        assert isinstance(table, weakref.WeakValueDictionary), (
            f"cas/syntax/term.py:{name} pins its entries")

    pattern_path = _ROOT / "cas" / "syntax" / "pattern.py"
    pattern_tree = ast.parse(pattern_path.read_text(encoding="utf-8"))
    for cache in ("_VARS", "_SEQS", "_CALLS"):
        assert _cache_has_bound_and_eviction(
            pattern_tree, cache, "_PATTERN_INTERN_CAP"
        ), (
            f"cas/syntax/pattern.py:{cache} is not bounded by "
            "_PATTERN_INTERN_CAP with an eviction"
        )
