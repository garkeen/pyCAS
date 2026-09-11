# -*- coding: utf-8 -*-
"""Piecewise container: Piecewise is a syntax container, not a new numeric domain.

Structure: `Piecewise(v1, c1, v2, c2, ...)` -- value/condition pairs, interned.

Evaluation semantics (single, consistent across the module): **ordered
first-match** (if / elif / else, the standard Piecewise). The value at a point is
the value of the first branch whose condition holds in declaration order; a
condition of TRUE is the "else" branch and applies only where no earlier branch
holds. Because every point falls on at most one branch, evaluation is intrinsically
unique -- no semantic conflict at the evaluation level exists or is permitted. Three
consequences:

* A branch body need not share a host structure: each branch projects
  independently (`project_pw`), the domain is branch-local, and failing to find a
  common host is not an error.
* A condition may be any proposition: it goes to the decision pipeline, which yields
  a truth value when it can and propagates GUARDED otherwise (`select` for values,
  `coverage` for coverage).
* `conflicts` is an **order-independence lint** (not an evaluation gate): if two
  branches overlap and their values differ there, the value at that point depends on
  declaration order, so the author is told to tighten the guards into a mutually
  exclusive form. An undecided question stays Unknown and is never reported as
  well-defined. Coverage completeness is the user's declaration, decided when
  decidable and never filled in unasked.

Operation lifting (`lift`): a piecewise function participates in an operation
pointwise, `(f+g)(x) = f(x)+g(x)`, by Cartesian expansion per branch with the
conditions conjoined. Note that **differentiation and integration of a piecewise
function must separately check continuity and one-sided limits at the breakpoints**
and are not per-branch composable: the cautious channel is
`differentiate_piecewise` in the differentiation module (breakpoints explicitly
unverified), and piecewise definite integration refuses gaps and point holes.
"""

from cas.syntax import term as T
from cas.syntax.term import S, Expr
from cas.math.project import project
from cas.kernel.verdict import YES, NO, unknown, Reason


# ---------------------------------------------------------------------------
# Construction and decomposition
# ---------------------------------------------------------------------------

_HEAD = "Piecewise"


def is_piecewise(t) -> bool:
    return isinstance(t, Expr) and t.head.name == _HEAD \
        and len(t.args) % 2 == 0


def piecewise(pairs) -> object:
    """(value, condition) sequence -> interned Piecewise.

    Syntactic normalization (no semantic decision): drop branches whose condition is
    FALSE, truncate after a condition of TRUE (first-match decides, later branches
    are unreachable), collapse an empty container to Undefined, and collapse a single
    true branch to its value.
    """
    kept = []
    for v, c in pairs:
        if c is T.FALSE:
            continue
        kept.append((v, c))
        if c is T.TRUE:
            break                        # branches after TRUE are never reached
    if not kept:
        return T.SP("Undefined")
    if len(kept) == 1 and kept[0][1] is T.TRUE:
        return kept[0][0]
    flat = []
    for v, c in kept:
        flat.append(v)
        flat.append(c)
    return T.mk(S(_HEAD), tuple(flat))


def branches(t):
    """Interned Piecewise -> [(value, condition)]. A non-piecewise term maps to
    [(t, TRUE)], the trivial cover."""
    if not is_piecewise(t):
        return [(t, T.TRUE)]
    a = t.args
    return [(a[i], a[i + 1]) for i in range(0, len(a), 2)]


def conditions(t):
    return [c for _v, c in branches(t)]


# ---------------------------------------------------------------------------
# Independent per-branch projection (no shared host)
# ---------------------------------------------------------------------------

def project_pw(t):
    """Project each branch into its own host domain, independently.

    Returns [(value, condition, Projected|None)]. A Projected of None means the
    branch lies outside the current projection ladder (not a member of Q / K[x] /
    K(x)), which the caller handles honestly."""
    return [(v, c, project(v)) for v, c in branches(t)]


# ---------------------------------------------------------------------------
# Condition semantics: consumed by the decision pipeline
# ---------------------------------------------------------------------------

def select(t, assumptions):
    """Evaluate a piecewise function under `assumptions` by ordered first-match
    (if/elif/else): the first condition provably true.

    Scan top down: a branch provably false is skipped; a branch provably true
    determines the value if no earlier branch survives that could shadow it. At most
    one branch per point, so the value is unique and there is no evaluation-level
    conflict. A condition of TRUE is the "else" branch.

    Returns (status, payload):
    * ("value", v)           unique hit; or v = Undefined when every branch is
                             provably false
    * ("residual", (pw, r))  an earlier branch condition is undecided, so the
                             shadowing relation is open; pw is the residual suffix and
                             r the reason for that undecidedness
    """
    bs = branches(t)
    survivors = []              # later candidates to keep until the first match is decided
    first_unknown = None
    for v, c in bs:
        if c is T.TRUE:
            if not survivors:                   # else branch with all earlier ones false: hit
                return ("value", v)
            survivors.append((v, c))            # an earlier branch is undecided, so shadowing is open
            break
        verdict = decide(c, assumptions)
        if verdict is NO:
            continue                            # branch does not hold, try the next
        if verdict is YES:
            if not survivors:                   # first true branch with all earlier false: hit
                return ("value", v)
            survivors.append((v, c))
            continue
        if first_unknown is None:               # undecided branch: it may hold and shadow the rest
            first_unknown = verdict.reason
        survivors.append((v, c))
    if not survivors:
        return ("value", T.SP("Undefined"))     # every branch provably false: undefined here
    return ("residual", (piecewise(survivors),
                         first_unknown or Reason.FRAGMENT))


def coverage(t, assumptions):
    """Whether the disjunction of branch conditions covers the whole space (completeness
    is the user's declaration, decided here when decidable).

    YES means full coverage; NO means there is a provable gap (undefined where every
    condition is false); Unknown(GUARDED) means some condition is undecided and
    coverage is undecided with it."""
    conds = conditions(t)
    guarded = False
    for c in conds:
        if c is T.TRUE:
            return YES
        v = decide(c, assumptions)
        if v is YES:
            return YES
        if v is NO:
            continue
        guarded = True
    return unknown(Reason.GUARDED) if guarded else NO


def collapse(t, assumptions):
    """Point collapse: replace every Piecewise subterm by its selected value under
    `assumptions`.

    The common channel for numeric-point back-substitution: when the conditions are
    decidable under `assumptions`, each piecewise collapses to a single branch value
    by ordered first-match, and after outward propagation the whole term is an
    ordinary term that can go through domain zeroing or evaluation. If any branch
    selection is undecided (a condition resists decision), the whole result is None
    (honestly undecided, never guessed).

    A piecewise may occur at any depth of an operation (such as `pw(...) + 2`); a
    piecewise in condition position is a malformed structure that fold_nested already
    refuses, so it is never seen here."""
    if is_piecewise(t):
        status, load = select(t, assumptions)
        if status != "value":
            return None                        # branch selection undecided: shadowing cannot be settled
        return collapse(load, assumptions)             # keep collapsing if the branch value is still piecewise
    if not isinstance(t, Expr) or not t.args:
        return t
    new_args = []
    changed = False
    for a in t.args:
        na = collapse(a, assumptions)
        if na is None:
            return None
        changed = changed or (na is not a)
        new_args.append(na)
    return T.mk(t.head, tuple(new_args)) if changed else t


def conflicts(t, assumptions):
    """Order-independence lint (not an evaluation gate): values differing on an
    overlap mean the value there depends on declaration order.

    Evaluation uses `select` with ordered first-match and is never ambiguous. This
    function is an **authoring check**: if two branch regions can hold simultaneously
    (`ci and cj` satisfiable) while their values differ, swapping the declaration order
    changes the result there, so the author is told to write mutually exclusive guards.
    Returns [(i, j, Verdict)], where the Verdict states whether the overlap is
    well-defined (order independent):
    * YES  empty overlap, or identical values on the overlap
    * NO   the overlap is satisfiable and the two values differ: order sensitive, the
           author should tighten the guards
    * Unknown  beyond the pipeline's decision power (GUARDED/FRAGMENT/UNDECIDABLE/BUDGET)

    An undecided case is never disguised as agreement."""
    from cas.math.decide import satisfiable
    bs = branches(t)
    out = []
    n = len(bs)
    for i in range(n):
        vi, ci = bs[i]
        for j in range(i + 1, n):
            vj, cj = bs[j]
            sat = satisfiable([ci, cj], assumptions)      # is the overlap satisfiable
            if sat is NO:
                out.append((i, j, YES))            # empty overlap: order independent by construction
                continue
            out.append((i, j, _agree(vi, vj, (ci, cj), assumptions)))
    return out


def _agree(vi, vj, conds, assumptions):
    """Whether two values are equal under the overlap conditions: decide after
    **extending** the assumption set.

    The assumption set is immutable, so this uses `extended` (producing a new object)
    rather than writing in place: overlap analysis must not pollute the caller's
    assumptions.
    """
    if vi is vj:
        return YES
    tmp = assumptions.extended(*[c for c in conds if c is not T.TRUE])
    from cas.math.decide import equivalent
    return equivalent(vi, vj, tmp)


# ---------------------------------------------------------------------------
# Per-branch operation lifting
# ---------------------------------------------------------------------------

def lift(op, *terms):
    """Lift an n-ary operation op over Piecewise arguments per branch (Cartesian
    expansion).

    Semantics: a piecewise function participates in an operation pointwise,
    `(f+g)(x) = f(x)+g(x)`. Each combination of (p-branch, q-branch, ...) produces a
    new branch whose value is op of the branch values and whose condition is the
    conjunction of the branch conditions; a combination whose conjunction is provably
    false (the two branches cannot hold together) has an empty overlap and is dropped.
    op takes interned terms and returns an interned term (such as T.plus / T.times). A
    non-Piecewise argument counts as a single always-true branch. The result is
    normalized by `piecewise`."""
    if not any(is_piecewise(x) for x in terms):
        return op(*terms)
    exps = [branches(x) for x in terms]
    combos = [[]]
    for ex in exps:
        combos = [c + [b] for c in combos for b in ex]
    pairs = []
    for combo in combos:
        vals = [v for v, _c in combo]
        conds = [c for _v, c in combo]
        conj = _and_all(conds)
        if conj is T.FALSE:                 # empty combination: conditions cannot hold together
            continue
        pairs.append((op(*vals), conj))
    return piecewise(pairs)


def _and_all(conds):
    keep = []
    for c in conds:
        if c is T.FALSE:
            return T.FALSE
        if c is T.TRUE:
            continue
        if isinstance(c, Expr) and c.head.name == "And":
            keep.extend(c.args)
        else:
            keep.append(c)
    if not keep:
        return T.TRUE
    return T.and_(*keep)


# ---------------------------------------------------------------------------
# Nested flattening + domain extraction (consumes the CAD cells; prerequisite for
# piecewise differentiation, integration, and equation solving)
# ---------------------------------------------------------------------------

from dataclasses import dataclass          # noqa: E402
from cas.errors import PiecewiseError       # noqa: E402
from cas.math.decide import decide          # noqa: E402
from cas.math.cad import resolve_partition       # noqa: E402

_UNDEF = T.SP("Undefined")


def _conj(a, b):
    if a is T.FALSE or b is T.FALSE:
        return T.FALSE
    if a is T.TRUE:
        return b
    if b is T.TRUE:
        return a
    return T.and_(a, b)


def fold_nested(t):
    """Flatten nested piecewise into a single layer: a piecewise value distributes
    into the outer condition by conjunction.

    `pw(pw(a,ca,b,cb), c) -> pw(a, ca and c, b, cb and c)`. A structural rewrite, not
    a special case; after flattening every algorithm faces a single-layer partition. A
    piecewise in condition position is malformed and is refused."""
    if not is_piecewise(t):
        return t
    pairs = []
    for v, c in branches(t):
        if is_piecewise(c):
            raise PiecewiseError("a piecewise value is not allowed in condition position")
        fv = fold_nested(v)
        if is_piecewise(fv):
            for iv, ic in branches(fv):
                pairs.append((iv, _conj(ic, c)))
        else:
            pairs.append((fv, c))
    return piecewise(pairs)


def domain_cells(t, x):
    """Decompose the domain of a piecewise function in x into cells.

    Returns [(Cell, value|Undefined)]: on each cell the value is that of the first
    branch holding by ordered first-match, and Undefined when no condition holds (the
    cell is outside the domain). A condition containing transcendentals or a
    multivariate partition passes through cad.CadError (UNDECIDABLE / FRAGMENT)."""
    t = fold_nested(t)
    bs = branches(t)
    conds = [c for _v, c in bs]
    out = []
    for cell, labels in resolve_partition(conds, x):
        val = _UNDEF
        for (v, _c), holds in zip(bs, labels):
            if holds:
                val = v
                break
        out.append((cell, val))
    return out


@dataclass(frozen=True, slots=True)
class Component:
    """One connected component of the domain.

    cells: the (Cell, value) sequence inside the component;
    lo / hi: isolating intervals of the lower/upper bound roots, None when unbounded;
    lo_closed / hi_closed: whether the corresponding endpoint is included (an open
    interval excludes its endpoints, a point cell includes them)."""
    cells: tuple
    lo: object
    lo_closed: bool
    hi: object
    hi_closed: bool


def _mk_component(run):
    first_cell = run[0][0]
    last_cell = run[-1][0]
    if first_cell.kind == "point":
        lo, lo_closed = first_cell.iso, True
    else:
        lo, lo_closed = first_cell.lo, False      # an open cell excludes its left end; None is -inf
    if last_cell.kind == "point":
        hi, hi_closed = last_cell.iso, True
    else:
        hi, hi_closed = last_cell.hi, False       # an open cell excludes its right end; None is +inf
    return Component(tuple(run), lo, lo_closed, hi, hi_closed)


def connected_components(domain):
    """Merge the defined cells of `domain_cells` into maximal connected components.

    An undefined cell breaks connectivity: independent constants of indefinite
    integration and the piecewise sum of definite integrals are both per connected
    component, and the two sides of a gap are never treated as one."""
    comps = []
    run = []
    for cell, val in domain:
        if val is _UNDEF:
            if run:
                comps.append(_mk_component(run))
                run = []
        else:
            run.append((cell, val))
    if run:
        comps.append(_mk_component(run))
    return comps
