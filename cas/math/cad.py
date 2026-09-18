"""One-dimensional cylindrical algebraic decomposition, the simplest CAD.

Decompose a set of univariate polynomial conditions in x into ordered, pairwise
disjoint cells (open intervals plus points) that cover the whole line, and decide
each condition's truth value on each cell. This is the shared foundation of
piecewise differentiation/integration and equation solving: every "where are the
breakpoints and in what order" question reduces to it.

Decision channels, all exact, no approximation:
· open cell: take a root-free rational sample point and sign the boundary
  polynomial exactly;
· point cell (a root): if the condition's boundary polynomial vanishes there
  (Sturm count >= 1) the value is 0; otherwise the sign is constant in a small
  neighbourhood and is read from the midpoint of the isolating interval, with no
  need for an algebraic extension.

Honest boundary: a condition that is not a univariate polynomial is refused --
multivariate partitioning is FRAGMENT, and transcendental structure
(comparing transcendental roots) is UNDECIDABLE.
"""

from dataclasses import dataclass
from fractions import Fraction as Fr

from cas.syntax import term as T
from cas.errors import CadError
from cas.kernel.verdict import Reason
from cas.math.domains.qarith import fold
from cas.math.domains.base import find_domain
from cas.math.domains.poly import from_term, p_mul
from cas.math.domains.polytools import p_deg
from cas.math.realroot import (real_roots_intervals, p_eval_at, coef_sign,
                          squarefree_part, sturm_sequence, count_roots_open)

_CMP = ("Lt", "Le", "Gt", "Ge", "Eq", "Ne")


def _coeff_ring():
    """The coefficient ring for CAD: an **ordered field**, because Sturm sign
    determination needs an order structure.

    Taken by capability rather than by hardcoding `Q_RING`. The system currently
    has exactly one ordered field, Q; if another is added, this query fails
    loudly on an ambiguous match rather than silently picking one, because an
    ambiguous domain is a decision that must be made explicitly.
    """
    hits = find_domain(lambda d: d.is_field and d.is_ordered
                       and d.ring is not None)
    if len(hits) != 1:
        raise CadError(
            f"CAD needs a unique ordered field coefficient ring, matched "
            f"{[d.name for d in hits]}",
            Reason.FRAGMENT)
    return hits[0].ring


@dataclass(frozen=True, slots=True)
class Cell:
    """One cell.

    kind == "open": an open interval, with a root-free rational sample point.
    kind == "point": a simple-root cell, with iso=(a, b) as the isolating
                     interval (a == b for an exact rational root).
    lo / hi: the isolating intervals of the lower/upper boundary roots; None
             means unbounded (-infinity / +infinity). For a point cell
             lo == hi == iso; for an open cell they are the adjacent root
             intervals."""
    kind: str
    sample: object = None     # Fr (open)
    iso: tuple = None         # (a, b) (point)
    lo: object = None         # lower root isolating interval or None (-infinity)
    hi: object = None         # upper root isolating interval or None (+infinity)


# ---------------------------------------------------------------------------
# Condition to boundary polynomial
# ---------------------------------------------------------------------------

def _refusal_reason(d, x):
    fv = T.free_vars(d)
    if any(s is not x for s in fv):
        return Reason.FRAGMENT          # multivariate partitioning: CAD projection not built
    return Reason.UNDECIDABLE           # univariate with transcendental structure: root comparison undecidable


def _boundary(cond, x):
    """The difference of the two sides of a comparison proposition, as a
    univariate polynomial; a non-polynomial partition is refused.

    The difference is folded over Q first: an unfolded negative power from
    parsing (such as (2^-1)*(-1) for -1/2) folds to a constant, and only a
    difference that is still non-polynomial after folding is a real refusal.
    """
    a, b = cond.args
    d = fold(T.plus(a, T.neg(b)))
    p = from_term(_coeff_ring(), d, (x,))
    if p is None:
        raise CadError(f"condition is not a univariate polynomial partition: {cond!r}",
                       _refusal_reason(d, x))
    return p


def extract_boundary_polys(cond, x):
    """Recursively collect the boundary polynomials of a condition, taking the
    difference of the two sides and dropping constants."""
    if cond is T.TRUE or cond is T.FALSE:
        return []
    if isinstance(cond, T.BVal):
        return []
    if isinstance(cond, T.Expr):
        h = cond.head.name
        if h in ("And", "Or"):
            out = []
            for a in cond.args:
                out.extend(extract_boundary_polys(a, x))
            return out
        if h == "Not":
            return extract_boundary_polys(cond.args[0], x)
        if h in _CMP:
            p = _boundary(cond, x)
            return [p] if p_deg(p, 0) > 0 else []
    raise CadError(f"not a propositional condition: {cond!r}", Reason.FRAGMENT)


# ---------------------------------------------------------------------------
# Cell construction
# ---------------------------------------------------------------------------

def cells(polys):
    """Produce ordered cells from a set of boundary polynomials. With no real
    root the result is the single open interval (-infinity, +infinity)."""
    if not polys:
        return [Cell("open", sample=Fr(0))]
    ring = _coeff_ring()
    P = polys[0]
    for q in polys[1:]:
        P = p_mul(ring, P, q)
    ivs = real_roots_intervals(ring, P)
    if not ivs:
        return [Cell("open", sample=Fr(0))]
    out = []
    a1, _b1 = ivs[0]
    out.append(Cell("open", sample=a1 - 1, hi=ivs[0]))       # (-infinity, r1)
    for i, (a, b) in enumerate(ivs):
        out.append(Cell("point", iso=(a, b), lo=(a, b), hi=(a, b)))
        if i + 1 < len(ivs):
            na, nb = ivs[i + 1]
            out.append(Cell("open", sample=(b + na) / 2,    # (r_i, r_{i+1})
                            lo=(a, b), hi=(na, nb)))
    _ak, bk = ivs[-1]
    out.append(Cell("open", sample=bk + 1, lo=ivs[-1]))      # (r_k, +infinity)
    return out


# ---------------------------------------------------------------------------
# Sign determination on a cell
# ---------------------------------------------------------------------------

def sign_at_cell(p, cell: Cell) -> int:
    """The sign (-1/0/1) of a boundary polynomial on a cell."""
    if p.is_zero():
        return 0
    if cell.kind == "open":
        return coef_sign(p_eval_at(p, cell.sample))
    a, b = cell.iso
    if a == b:                                # exact rational root
        return coef_sign(p_eval_at(p, a))
    # irrational root: p vanishes there iff p has a root in the isolating
    # interval (Sturm count)
    ring = _coeff_ring()
    sf = squarefree_part(ring, p)
    seq = sturm_sequence(ring, sf)
    if count_roots_open(seq, sf, a, b) >= 1:
        return 0
    return coef_sign(p_eval_at(p, (a + b) / 2))


def _apply_cmp(op: str, sgn: int) -> bool:
    if op == "Lt":
        return sgn < 0
    if op == "Le":
        return sgn <= 0
    if op == "Gt":
        return sgn > 0
    if op == "Ge":
        return sgn >= 0
    if op == "Eq":
        return sgn == 0
    return sgn != 0                           # Ne


def cond_holds(cond, cell: Cell, x) -> bool:
    """The truth value of a condition on a cell, where it is constant."""
    if cond is T.TRUE:
        return True
    if cond is T.FALSE:
        return False
    h = cond.head.name
    if h == "And":
        return all(cond_holds(a, cell, x) for a in cond.args)
    if h == "Or":
        return any(cond_holds(a, cell, x) for a in cond.args)
    if h == "Not":
        return not cond_holds(cond.args[0], cell, x)
    if h in _CMP:
        p = _boundary(cond, x)
        return _apply_cmp(h, sign_at_cell(p, cell))
    raise CadError(f"not a propositional condition: {cond!r}", Reason.FRAGMENT)


# ---------------------------------------------------------------------------
# Partition resolution (public entry point)
# ---------------------------------------------------------------------------

def resolve_partition(conds, x):
    """The cylindrical decomposition of `conds` with respect to x.

    Returns [(Cell, [bool, ...])] where the inner list aligns with conds and
    gives each condition's truth value on the cell. An empty condition list
    returns the single open interval covering the whole line. Any condition that
    is not a univariate polynomial partition raises CadError (see the module
    docstring for the reasons)."""
    polys = []
    for c in conds:
        polys.extend(extract_boundary_polys(c, x))
    cell_list = cells(polys)
    return [(cell, [cond_holds(c, cell, x) for c in conds])
            for cell in cell_list]
