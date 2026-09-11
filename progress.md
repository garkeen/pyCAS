# Progress

Current implementation state and next steps. The design authority is
`cas_v4_arch.md`; the engineering discipline is `AGENTS.md`. `cas_v3_arch.md` is
superseded and kept for history only.

## Repository layout

| Path | Contents |
|---|---|
| `cas/syntax/` | `term` (interned terms), `pattern` (pattern metalanguage), `match`, `termpath`, `abstract` |
| `cas/kernel/` | `verdict`, `model`, `evidence`, `scope`, `context`, `commit`, `store`, `services`, `ids`, `mode` |
| `cas/workflow/` | `workflow`, `command`, `artifact`, `task`, `event`, `constraint`, `branch`, `ids` |
| `cas/math/domains/` | `base`, `z`, `q`, `qi`, `poly`, `ratfunc`, `polytools`, `linalg`, `module` |
| `cas/math/` | `project`, `qarith`, `decide`, `diff`, `integrate`, `cad`, `realroot`, `tactics`, `piecewise`, `domcond`, `rules`, `simplify`, `judge`, `constraints`, `loader`, plus `base/`, `elementary/`, `calculus/`, `solving/` |
| `cas/runtime/` | `registry` (RuntimeBuilder), `runtime` (Runtime, new_workflow), `bootstrap`, `dispatch`, `algorithms`, `services` |
| `cas/frontend/` | `parser`, `pprint`, `repl`; the root `repl.py` is the entry shell |
| `cas/api.py`, `cas/errors.py` | frontend computation facade; shared exceptions |

## Dependency direction

Enforced mechanically in `tests/test_v4_invariants.py`:

- `syntax` depends only on the standard library and `cas.errors`.
- `kernel` depends only on `syntax`; it imports no concrete math, workflow or
  frontend module, and contains no workflow concept names.
- `workflow` depends only on `syntax` + `kernel`; checkers, decision services and
  algorithms are injected by the runtime, so no `cas.math` import exists in it.
- `math/domains` depends on `syntax`; other math modules may use `syntax`,
  `kernel`, `workflow` and `math/domains`. Math never imports `runtime`.
- The runtime is the assembler: `bootstrap()` installs every math module and
  binds the read-only surfaces. There is no import-time global mutation.
- The frontend reaches computation only through `cas/api.py` and
  `cas/runtime/dispatch.py`; it imports no `cas.math` or `cas.kernel`.

## v4 migration status

| Stage | Content | Status |
|---|---|---|
| 1 | syntax split; pattern metalanguage (PatternVar/PatternSeq are not Terms) | done |
| 2 | kernel model: Scope / Judgment / Requirement / Evidence / StepProposal / commit / CheckerRegistry | done |
| 3 | derivation ADT removed; commands generate proposals; checkers verify instances rather than re-searching | done |
| 4 | Artifact / Task / Event separation | partial: the three graphs and constraints exist with real consumers, but history truncation and the applicability cache are not built |
| 5 | persistent scope tree replacing the mutable context | done |
| 6 | math modules under `cas/math`, explicit `install(builder)` assembly | done |

Invariants 1 / 2 / 14 / 16 / 18 are green, plus four dependency/reference
direction gates; there are no xfail entries. The red-first policy now applies
only where a genuine cross-stage migration is pending.

## Implementation discipline

`AGENTS.md` carries six hard rules: no hardcoding, no special-casing
(case-driven or simplified implementations), strict capability-based domain
dispatch, automatic algorithms restricted to decidable content, single
responsibility, and names that match semantics.

Work landed against them:

- Mathematical-semantics heads (elementary functions and constants) are declared
  in `math/elementary/declarations.dsl` and installed through the builder. The
  file also carries parse-level aliases (`ln -> Log`, `sqrt -> Sqrt`) and
  algorithm roles (`logarithm -> Log`), so neither the parser nor the
  differentiator hardcodes a function name. Admission is checked mechanically
  against the DSL text.
- Surface heads (Plus/Times/Power, the comparisons, And/Or/Not, Quote/Piecewise)
  remain dispatchable in algorithms: they are the structure of the term language.
- Concrete domain singletons were replaced by capability queries
  (`find_domain`): CAD takes the unique ordered field, the Diophantine fragment
  takes the unique Euclidean integral domain, and the projection base field is
  chosen the same way. The default coefficient ring of K[x]/K(x) is injected at
  assembly time instead of being bootstrapped inside the domain package.
- The projection ladder is registered (`ProjectionStage`) rather than a hardcoded
  if-chain.
- The integration verifier lives in `math/calculus/integration/verify.py`, apart
  from the solver; a strengthened gate rejects any checker that imports its own
  solver module.
- The workflow step record is named `WorkflowStep`, distinct from the kernel
  `Step`.
- `cas/runtime/dispatch.py` forwards attributes to the assembled runtime through
  module `__getattr__` instead of hand-writing one forwarding function per
  Runtime method.

## Implemented foundation

- Interned term layer with AC canonical forms; pattern metalanguage separate from
  the term layer; binder abstraction/instantiation on de Bruijn indices.
- Exact rational literal arithmetic; domain system Z, Q, Q(i), K[x], K(x) with
  capability fields and a projection ladder.
- Decision pipeline returning the `Verdict` ADT with the four `Reason` values,
  honest undecided outside the fragment.
- Kernel: append-only ledger, scope tree with visibility and escape checks,
  condition lifecycle with discharge and refutation, ten-step commit with a
  provable four-step specialization.
- Rule engine driven by declared rules; auto rules are guard-free and terminate
  by strict cost decrease.
- One-dimensional CAD (real root isolation via Sturm), piecewise container with
  ordered first-match semantics, cautious piecewise differentiation, piecewise
  equation solving, polynomial-fragment integration with a three-valued
  independent verifier, linear algebra (echelon, rank, nullspace, solving,
  Bareiss determinant), resultants and Yun squarefree decomposition, linear
  Diophantine fragments and integer roots, constraint solving over terms,
  branch split/merge, declarations/definitions with hygiene checks.
- REPL covering claim/norm/solve/subst/split/diff/rules/apply/integrate/check/
  steps/undo, routed through the frontend facade.

Verification: `tests/` 160 passed; `stress/` 10 scripts passing (41 self-proving
properties).

## Not implemented (next work)

- Interactive channel: workflow serialization and replay; real undo/redo beyond
  moving the revision pointer; versioned context folding; consuming split
  branches in later solving.
- Tactics: quadratic solving with discriminant branches; cyclic equation solving;
  general Diophantine refusal wired to UNDECIDABLE; multivariable and
  binder-internal differentiation.
- Number fields before Risch: Q(i) coefficient absorption in poly/ratfunc;
  Gaussian integers; generic algebraic extensions; parametric fraction fields;
  multivariate gcd.
- Order and root comparison: interval arithmetic layer; declared order lemmas;
  transcendental root objects; conditional answer containers.
- Shared algorithm machine: Zassenhaus factorization; partial fractions and
  Hermite reduction; subresultant chains; differential towers.
- Trigonometric/exponential expansion and like-term collection. This is the
  capability gap that keeps the cyclic exp/sin integral at "undecided": the
  differentiation layer can verify it, but the vanishing channel cannot yet
  expand the difference to zero.
- Open design decision: branch merge cannot independently re-check "each branch
  answered P" without commit supporting implication introduction
  (Gamma, C proves P implies Gamma proves C -> P), which is a new kernel rule not
  yet taken.

## Language and reference policy

Code and comments are English-only, and source never cites a design document: a
rationale is stated plainly rather than pointing the reader at a document. Both
rules are mechanical gates in `tests/test_v4_invariants.py`
(`test_source_is_english_only`, `test_source_cites_no_design_document`), covering
every `.py` and `.dsl` file under `cas/`, `tests/` and `stress/`.
