# -*- coding: utf-8 -*-
"""Decision pipeline: proposition composition plus domain-specific decidable atoms.

The return value is the decision ADT (cas/verdict): Yes/No/Unknown(reason). The
reasons distinguish a fragment the pipeline does not cover (FRAGMENT), a fact
blocked by a condition (GUARDED), a genuinely undecidable question (UNDECIDABLE),
and an exhausted budget (BUDGET) -- four different consequences that must never be
folded into one "don't know".

Atom channels, in order: pointer/numeric -> direct ledger lookup -> ledger
equality closure -> projection zero test (domain normal form) -> interval
propagation -> order-chain inference -> derived rule layer -> declaration lemmas
(constant coarse bounds, function range bounds). Reasoning under assumptions
never rewrites with them: the closure orients every frame equation towards a
class representative, and the rule layer terminates through a visited-fact guard
rather than a search-depth cap, so a verdict never depends on how deep a query
entered the pipeline.

Every entry point takes the math context as its first parameter: the declaration
surface (constants, functions, domain conditions) and the identity-decision stages
travel there, so this module keeps no handle of its own and importing it has zero
side effects.
"""

from collections import deque
from collections.abc import Callable, Iterable, Sequence
from fractions import Fraction
from typing import Literal, TypeAlias, TypeGuard

from cas.kernel.scope import Assumptions
from cas.kernel.verdict import (
    YES,
    No,
    Reason,
    Refutation,
    RefutationChannel,
    Verdict,
    and3,
    contextualize,
    not3,
    or3,
    refute,
    unknown,
)
from cas.math.base.equality import closure_decide, is_closed
from cas.math.context import MathContext
from cas.math.domains.qarith import fold as _qfold
from cas.syntax import term as T
from cas.syntax.term import Const, Expr, S, Term

AssumptionFrame: TypeAlias = Assumptions | Iterable[Term] | None
Query: TypeAlias = Callable[[Term], Verdict]
Interval: TypeAlias = tuple[Fraction | None, Fraction | None, bool, bool]
ContextFreeRule: TypeAlias = Callable[[Expr, Assumptions, Query], Verdict | None]
ContextRule: TypeAlias = Callable[
    [MathContext, Expr, Assumptions, Query], Verdict | None
]
RuleApplies: TypeAlias = Callable[[Expr], bool]


def _comparison_no(
    channel: RefutationChannel,
    op: str,
    lhs: Term,
    rhs: Term,
    detail: str,
    *witnesses: Term,
) -> No:
    claim = T.mk(S(op), (lhs, rhs))
    return refute(channel, claim, lhs, rhs, *witnesses, detail=detail)


def _A(a: AssumptionFrame) -> Assumptions:
    """Normalize an optional assumption collection to an immutable frame."""
    if isinstance(a, Assumptions):
        return a
    if a is None:
        return Assumptions()
    return Assumptions(tuple(a))


_NEG = {
    "Gt": "Le",
    "Ge": "Lt",
    "Lt": "Ge",
    "Le": "Gt",
    "Eq": "Ne",
    "Ne": "Eq",
}


_ORD = ("Lt", "Le", "Gt", "Ge")


def _nonreal_constant(ctx: MathContext, t: Term) -> Const | None:
    """A constant declared not real that occurs in `t`, or None.

    An order comparison is read over an ordered domain. The declared constants
    are the only value-domain information the decision layer has (it reads the
    declaration context and the assumption ledger, never a kernel scope), so a
    constant whose declaration says "not real" is the evidence that the ordered
    reading does not apply: the sign rules for powers and sums are ordered-field
    facts, and `i * i >= 0` is not a proposition about an ordered field.
    """
    if isinstance(t, T.Const):
        return t if ctx.const_real(t) is False else None
    if isinstance(t, T.Expr):
        for a in t.args:
            bad = _nonreal_constant(ctx, a)
            if bad is not None:
                return bad
    return None


def _ordered_fact(ctx: MathContext, f: Term) -> bool:
    """Whether an assumption can be consumed as ordered information.

    The comparison gate in `decide` withholds answering an order comparison whose
    operands carry a constant declared not real. The assumption channels build
    order edges (`_chain_query`) and interval bounds (`_interval`) out of
    assumptions, so the same evidence must gate them: a fact carrying such a
    constant is not an ordered fact, and reading `x < i` together with `i < 3`
    as ordered facts would prove `x < 3` in a domain where no order reading
    applies. The real-valued path is untouched: `_nonreal_constant` returns None
    for every fact without a declared-not-real constant.
    """
    return _nonreal_constant(ctx, f) is None


def negate(ctx: MathContext, f: Term) -> Term:
    """Strong negation of a comparison predicate (not (a>b) == a<=b and so on);
    everything else goes through a syntactic Not.

    The strong form is an ordered-domain identity, so it is withheld when an
    operand carries a constant declared not real: such a comparison has no
    truth value to flip, and the decision layer must report undecided rather
    than answer the flipped predicate.
    """
    if isinstance(f, T.Expr) and f.head.name in _NEG:
        if f.head.name in _ORD and _nonreal_constant(ctx, f) is not None:
            return T.mk(S("Not"), (f,))
        return T.mk(S(_NEG[f.head.name]), f.args)
    if isinstance(f, T.Expr) and f.head.name == "Not":
        return f.args[0]
    return T.mk(S("Not"), (f,))


_CMP = ("Lt", "Le", "Gt", "Ge", "Eq", "Ne")
_CMP_INV = {"Lt": "Gt", "Gt": "Lt", "Le": "Ge", "Ge": "Le"}


def _cmp_numeric(op: str, a: Term, b: Term) -> Verdict | None:
    av = T.num_val(a) if T.is_num(a) else None
    bv = T.num_val(b) if T.is_num(b) else None
    if av is None or bv is None:
        return None
    if op == "Lt":
        r = av < bv
    elif op == "Le":
        r = av <= bv
    elif op == "Gt":
        r = av > bv
    elif op == "Ge":
        r = av >= bv
    elif op == "Eq":
        r = av == bv
    else:
        r = av != bv
    if r:
        return YES
    return _comparison_no(
        RefutationChannel.EXACT_COMPARISON, op, a, b,
        "exact rational comparison is false")


def _same(op: str, a: Term, b: Term) -> Verdict | None:
    if a is not b:
        return None
    if op in ("Eq", "Le", "Ge"):
        return YES
    return _comparison_no(
        RefutationChannel.EXACT_COMPARISON, op, a, a,
        "pointer-identical terms refute a strict or unequal comparison")


def _poly_eq_check(ctx: MathContext, a: Term, b: Term) -> Verdict | None:
    """Projection zero-test channel: when a-b falls inside Q/K[x]/K(x), the domain
    normal form decides it completely."""
    d = _qfold(T.plus(a, T.neg(b)))
    if d is T.ZERO:
        return YES
    from cas.math.project import zero_of
    r = zero_of(ctx, d)
    if r is True:
        return YES
    if r is False:
        return _comparison_no(
            RefutationChannel.NORMAL_FORM, "Eq", a, b,
            "the projected difference has a nonzero domain normal form", d)
    return None


def _facts_lookup(
    ctx: MathContext, fact: Expr, assumptions: Assumptions
) -> Verdict | None:
    for f in assumptions:
        if f is fact:
            return YES
        if f is negate(ctx, fact):
            return refute(
                RefutationChannel.ASSUMPTION_FACT, fact, fact, f,
                detail="the assumption frame contains the syntactic negation")
        if isinstance(f, T.Expr) and isinstance(fact, T.Expr):
            if f.head.name in _CMP_INV and fact.head.name in _CMP_INV:
                if (
                    f.head.name == _CMP_INV[fact.head.name]
                    and f.args[0] is fact.args[1]
                    and f.args[1] is fact.args[0]
                ):
                    return YES
    return None


def _chain_query(
    ctx: MathContext,
    op: str,
    a: Term,
    b: Term,
    assumptions: Assumptions,
) -> Verdict | None:
    """Order-chain BFS: ledger inequalities become edges and the transitive closure
    answers queries of the form a<b.

    A state is (node, whether the path contains a strict edge), and the best
    strictness per node is recorded. Numeric-bound inference and equality
    substitution belong to the interval channel; here only graph edges are walked.
    An order edge set is built explicitly below.
    (`_ordered_fact`) and is skipped: otherwise `x < i` and `i < 3` would chain
    to `x < 3` where the ordered reading does not apply.
    """
    adjacency: dict[Term, list[tuple[Term, bool]]] = {}
    strict = op in ("Lt", "Gt")
    want = (a, b)
    if op in ("Gt", "Ge"):
        want = (b, a)
    for f in assumptions:
        if isinstance(f, T.Expr) and f.head.name in ("Lt", "Le", "Gt", "Ge") \
                and _ordered_fact(ctx, f):
            opf = f.head.name
            u, v = f.args
            if opf in ("Gt", "Ge"):
                u, v = v, u
                opf = "Lt" if opf == "Gt" else "Le"
            adjacency.setdefault(u, []).append((v, opf == "Lt"))
    if a is b:
        if op in ("Le", "Ge", "Eq"):
            return YES
        return _comparison_no(
            RefutationChannel.DERIVATION, op, a, b,
            "pointer-identical terms refute the comparison")
    start, goal = want
    best: dict[int, bool] = {start._h: False}
    queue = deque([(start, False)])
    while queue:
        cur, evs = queue.popleft()
        if best.get(cur._h, False) != evs:
            continue                       # stale state: a better strictness was found
        for nxt, edge_strict in adjacency.get(cur, ()):
            next_strict = evs or edge_strict
            if nxt is goal and (not strict or next_strict):
                return YES
            previous = best.get(nxt._h)
            if previous is None or (next_strict and not previous):
                best[nxt._h] = next_strict
                queue.append((nxt, next_strict))
    return None


def _interval(
    ctx: MathContext,
    term: Term,
    assumptions: Assumptions,
    seen: set[int] | None = None,
    depth: int = 0,
) -> Interval | None:
    """Propagate numeric intervals from literals, declarations and assumptions."""
    if T.is_num(term):
        value = T.num_val(term)
        return value, value, False, False
    bounds = ctx.const_bounds(term) if isinstance(term, T.Const) else None
    if bounds is not None:
        return Fraction(bounds[0]), Fraction(bounds[1]), True, True
    if depth > 8:
        return None
    visited = set() if seen is None else seen
    if term._h in visited:
        return None
    visited.add(term._h)

    lower: Fraction | None = None
    upper: Fraction | None = None
    lower_strict = False
    upper_strict = False
    is_integer = False

    def tighten(
        new_lower: Fraction | None,
        new_lower_strict: bool,
        new_upper: Fraction | None,
        new_upper_strict: bool,
    ) -> None:
        nonlocal lower, upper, lower_strict, upper_strict
        if new_lower is not None and (
            lower is None
            or new_lower > lower
            or (new_lower == lower and new_lower_strict)
        ):
            lower, lower_strict = new_lower, new_lower_strict
        if new_upper is not None and (
            upper is None
            or new_upper < upper
            or (new_upper == upper and new_upper_strict)
        ):
            upper, upper_strict = new_upper, new_upper_strict

    for assumption in assumptions:
        if not isinstance(assumption, T.Expr):
            continue
        name = assumption.head.name
        if (
            name == "Attr"
            and assumption.args[0] is term
            and isinstance(assumption.args[1], T.Sym)
            and assumption.args[1].name == "integer"
        ):
            is_integer = True
            continue
        if not _ordered_fact(ctx, assumption):
            continue
        if name in ("Lt", "Le", "Gt", "Ge"):
            first, second = assumption.args
            if first is term and T.is_num(second):
                value = T.num_val(second)
                if name == "Lt":
                    tighten(None, False, value, True)
                elif name == "Le":
                    tighten(None, False, value, False)
                elif name == "Gt":
                    tighten(value, True, None, False)
                else:
                    tighten(value, False, None, False)
            elif second is term and T.is_num(first):
                value = T.num_val(first)
                if name == "Lt":
                    tighten(value, True, None, False)
                elif name == "Le":
                    tighten(value, False, None, False)
                elif name == "Gt":
                    tighten(None, False, value, True)
                else:
                    tighten(None, False, value, False)
        elif name == "Eq":
            first, second = assumption.args
            other = second if first is term else (first if second is term else None)
            if other is not None and other is not term:
                if T.is_num(other):
                    value = T.num_val(other)
                    tighten(value, False, value, False)
                else:
                    interval = _interval(ctx, other, assumptions, visited, depth + 1)
                    if interval is not None:
                        tighten(interval[0], interval[2], interval[1], interval[3])

    if is_integer:
        if lower is not None:
            candidate = (
                Fraction(lower.numerator // lower.denominator + 1)
                if lower_strict
                else Fraction(-((-lower.numerator) // lower.denominator))
            )
            if candidate > lower or lower_strict:
                lower, lower_strict = candidate, False
        if upper is not None:
            candidate = (
                Fraction(-((-upper.numerator) // upper.denominator) - 1)
                if upper_strict
                else Fraction(upper.numerator // upper.denominator)
            )
            if candidate < upper or upper_strict:
                upper, upper_strict = candidate, False

    if isinstance(term, T.Expr):
        name = term.head.name
        if name == "Plus":
            intervals: list[Interval] = []
            for argument in term.args:
                interval = _interval(
                    ctx, argument, assumptions, visited, depth + 1
                )
                if interval is None:
                    break
                intervals.append(interval)
            if len(intervals) == len(term.args):
                if all(interval[0] is not None for interval in intervals):
                    lower = sum(
                        (interval[0] for interval in intervals if interval[0] is not None),
                        Fraction(0),
                    )
                if all(interval[1] is not None for interval in intervals):
                    upper = sum(
                        (interval[1] for interval in intervals if interval[1] is not None),
                        Fraction(0),
                    )
                lower_strict = any(
                    interval[2] for interval in intervals
                )
                upper_strict = any(
                    interval[3] for interval in intervals
                )
        elif name == "Times":
            numeric = [argument for argument in term.args if T.is_num(argument)]
            symbolic = [argument for argument in term.args if not T.is_num(argument)]
            if numeric and len(symbolic) == 1:
                coefficient = Fraction(1)
                for argument in numeric:
                    coefficient *= T.num_val(argument)
                interval = _interval(
                    ctx, symbolic[0], assumptions, visited, depth + 1
                )
                if interval is not None:
                    if coefficient > 0:
                        tighten(
                            None if interval[0] is None else coefficient * interval[0],
                            interval[2],
                            None if interval[1] is None else coefficient * interval[1],
                            interval[3],
                        )
                    elif coefficient < 0:
                        tighten(
                            None if interval[1] is None else coefficient * interval[1],
                            interval[3],
                            None if interval[0] is None else coefficient * interval[0],
                            interval[2],
                        )
        elif name == "Power" and isinstance(term.args[1], T.Int) and term.args[1].v % 2 == 0:
            tighten(Fraction(0), False, None, False)
        else:
            function_bounds = _func_bound(ctx, name)
            if function_bounds is not None:
                tighten(function_bounds[0], False, function_bounds[1], False)

    if lower is None and upper is None:
        return None
    return lower, upper, lower_strict, upper_strict


def _cmp_interval(
    ctx: MathContext,
    op: str,
    a: Term,
    b: Term,
    assumptions: Assumptions,
) -> Verdict | None:
    """Reduce a comparison to an interval comparison against zero."""
    difference = _qfold(T.plus(a, T.neg(b)))

    def no(detail: str, *witnesses: Term) -> No:
        return _comparison_no(
            RefutationChannel.ORDER,
            op,
            a,
            b,
            detail,
            difference,
            *witnesses,
        )
    if op in ("Eq", "Ne"):
        if difference is T.ZERO:
            if op == "Eq":
                return YES
            return no("the exact difference is zero")
        interval = _interval(ctx, difference, assumptions)
        if interval is not None:
            lower, upper, _, _ = interval
            away = (lower is not None and lower > 0) or (
                upper is not None and upper < 0
            )
            if away:
                if op == "Eq":
                    return no("the difference interval is bounded away from zero")
                return YES
        return None
    if difference is T.ZERO:
        if op in ("Le", "Ge"):
            return YES
        return no("the exact difference is zero")
    interval = _interval(ctx, difference, assumptions)
    if interval is None:
        return None
    lower, upper, lower_strict, upper_strict = interval
    if lower is not None and upper is not None and lower == upper and not lower_strict and not upper_strict:
        if op == "Gt":
            return YES if lower > 0 else no("the exact interval value is not positive")
        if op == "Ge":
            return YES if lower >= 0 else no("the exact interval value is negative")
        if op == "Lt":
            return YES if lower < 0 else no("the exact interval value is not negative")
        return YES if lower <= 0 else no("the exact interval value is positive")
    if op == "Gt":
        if (lower is not None and lower > 0) or (lower == 0 and lower_strict):
            return YES
        if (upper is not None and upper < 0) or (upper == 0 and upper_strict):
            return no("the difference interval is non-positive")
    elif op == "Ge":
        if lower is not None and lower >= 0:
            return YES
        if (upper is not None and upper < 0) or (upper == 0 and upper_strict):
            return no("the difference interval is strictly negative")
    elif op == "Lt":
        if (upper is not None and upper < 0) or (upper == 0 and upper_strict):
            return YES
        if (lower is not None and lower > 0) or (lower == 0 and lower_strict):
            return no("the difference interval is non-negative")
    else:
        if upper is not None and upper <= 0:
            return YES
        if (lower is not None and lower > 0) or (lower == 0 and lower_strict):
            return no("the difference interval is strictly positive")
    return None


# ---------------------------------------------------------------------------
# Symbolic structure lemmas
# ---------------------------------------------------------------------------

def _func_bound(
    ctx: MathContext, name: str
) -> tuple[Fraction | None, Fraction | None] | None:
    """Return a declared function range bound."""
    declaration = ctx.lookup_function(name)
    if declaration is None or declaration.bound is None:
        return None
    lower, upper = declaration.bound
    return (
        Fraction(lower) if lower is not None else None,
        Fraction(upper) if upper is not None else None,
    )


def _nonneg_zero_arg(ctx: MathContext, t: Term) -> Term | None:
    """For t = g(u) where g is declared "nonnegative with lower bound 0 and
    g(u)=0 iff u=0" (absolute-value / norm family), return u.

    The decision rests on the declaration (zero_iff_arg_zero with a bound whose lower
    end is 0), never on the function name."""
    if not isinstance(t, T.Expr) or not isinstance(t.head, T.Sym) \
            or len(t.args) != 1:
        return None
    d = ctx.lookup_function(t.head.name)
    if d is None or not d.zero_iff_arg_zero:
        return None
    bd = d.bound
    if bd is None or bd[0] is None or bd[0] != 0:
        return None
    return t.args[0]


def _nneg(
    ctx: MathContext, t: Term, assumptions: Assumptions | None
) -> bool | None:
    """Nonnegativity structure decision: True/False/None (reads structure and ledger
    only, never calls back into decide)."""
    if T.is_num(t):
        return T.sign_num(t) >= 0
    if isinstance(t, T.Const) and ctx.const_positive(t) is True:
        return True
    if isinstance(t, T.Expr):
        name = t.head.name
        if name == "Power":
            b, e = t.args
            if isinstance(e, T.Int) and e.v % 2 == 0:
                return True
            if (
                isinstance(e, T.Rat)
                and e.f.denominator % 2 == 1
                and _pos(ctx, b, assumptions) is True
            ):
                return True
        bd = _func_bound(ctx, name)
        if bd is not None and bd[0] is not None and bd[0] >= 0:
            return True
    if assumptions is not None:
        for f in assumptions:
            if isinstance(f, T.Expr) and f.head.name in ("Gt", "Ge"):
                if f.args[0] is t and f.args[1] is T.ZERO:
                    return True
            if isinstance(f, T.Expr) and f.head.name in ("Lt", "Le"):
                if f.args[0] is t and f.args[1] is T.ZERO:
                    return False
    return None


def _pos(
    ctx: MathContext, t: Term, assumptions: Assumptions | None
) -> bool | None:
    """Positivity structure decision: True/False/None."""
    if T.is_num(t):
        return T.sign_num(t) > 0
    if isinstance(t, T.Const) and ctx.const_positive(t) is True:
        return True
    if assumptions is not None:
        for f in assumptions:
            if isinstance(f, T.Expr) and f.head.name == "Gt":
                if f.args[0] is t and f.args[1] is T.ZERO:
                    return True
            if isinstance(f, T.Expr) and f.head.name == "Le":
                if f.args[0] is t and f.args[1] is T.ZERO:
                    return False
    return None


# There is no search-depth cap. Termination comes from a cycle guard on visited
# facts (the derived-rule layer) and from the canonical orientation of the
# equality closure, so the verdict is a mathematical answer rather than a
# function of the entry depth.


def _is_cmp(f: Term) -> TypeGuard[Expr]:
    return isinstance(f, T.Expr) and f.head.name in _CMP


def _is_ord(f: Term) -> TypeGuard[Expr]:
    return isinstance(f, T.Expr) and f.head.name in ("Lt", "Le", "Gt", "Ge")


def _zero_cmp_of(
    ctx: MathContext,
    a: Term,
    assumptions: Assumptions | None,
    q: Query,
    op: str,
) -> Verdict | None:
    nneg = _nneg(ctx, a, assumptions)
    pos = _pos(ctx, a, assumptions)

    def no(detail: str) -> No:
        return _comparison_no(
            RefutationChannel.DERIVATION, op, a, T.ZERO, detail, a)

    if op == "Gt":
        if pos is True:
            return YES
        if nneg is False or (nneg is True and pos is False):
            return no("the operand is nonnegative and not positive")
        return None
    if op == "Ge":
        if nneg is True:
            return YES
        if nneg is False:
            return no("the operand is not nonnegative")
        return None
    if op == "Lt":
        if pos is True:
            return no("a positive operand is not less than zero")
        if nneg is False:
            return YES
        if nneg is True and pos is False:
            return no("a nonnegative operand is not less than zero")
        return None
    if op == "Le":
        if pos is True:
            return no("a positive operand is not at most zero")
        if nneg is False:
            return YES
        if nneg is True and pos is False:
            return YES
        return None
    return None


def _rule_ne_from_ord(
    f: Expr, assumptions: Assumptions, q: Query
) -> Verdict | None:
    a, b = f.args
    if q(T.mk(S("Gt"), (a, b))) is YES or q(T.mk(S("Lt"), (a, b))) is YES:
        return YES
    equality = T.mk(S("Eq"), (a, b))
    if q(equality) is YES:
        return refute(
            RefutationChannel.DERIVATION, f, f, equality,
            detail="the operands are equal, so they are not unequal")
    return None


def _rule_cmp_via_eq(
    f: Expr, assumptions: Assumptions, q: Query
) -> Verdict | None:
    a, b = f.args
    if T.is_num(b):
        for g in assumptions:
            if (
                isinstance(g, T.Expr)
                and g.head.name == "Eq"
                and g.args[0] is a
                and T.is_num(g.args[1])
            ):
                return _cmp_numeric(f.head.name, g.args[1], b)
    return None


def _sign_of_term(
    ctx: MathContext, t: Term, assumptions: Assumptions, q: Query
) -> int | None:
    if T.is_num(t):
        s = T.sign_num(t)
        if s > 0:
            return 1
        if s < 0:
            return -1
        return 0
    if isinstance(t, T.Const) and ctx.const_positive(t) is True:
        return 1
    r = q(T.mk(S("Gt"), (t, T.ZERO)))
    if r is YES:
        return 1
    r = q(T.mk(S("Lt"), (t, T.ZERO)))
    if r is YES:
        return -1
    r = q(T.mk(S("Eq"), (t, T.ZERO)))
    if r is YES:
        return 0
    r = q(T.mk(S("Ge"), (t, T.ZERO)))
    if r is YES:
        return 2
    return None

def _expr_arg(term: Term) -> Expr:
    """Require a structural child after a rule applicability check."""
    if not isinstance(term, T.Expr):
        raise TypeError("derived rule received a non-expression argument")
    return term


def _rule_sign_atom(
    ctx: MathContext, f: Expr, assumptions: Assumptions, q: Query
) -> Verdict | None:
    return _zero_cmp_of(ctx, f.args[0], assumptions, q, f.head.name)


def _rule_sign_times(
    ctx: MathContext, f: Expr, assumptions: Assumptions, q: Query
) -> Verdict | None:
    op = f.head.name
    a = _expr_arg(f.args[0])

    def no(detail: str) -> No:
        return _comparison_no(
            RefutationChannel.DERIVATION, op, a, T.ZERO, detail, a, *a.args)

    s_zero = False
    s_nn = False
    neg_count = 0
    for fac in a.args:
        sign = _sign_of_term(ctx, fac, assumptions, q)
        if sign is None:
            return None
        if sign == 0:
            s_zero = True
        elif sign == -1:
            neg_count += 1
        elif sign == 2:
            s_nn = True
    if s_zero:
        if op in ("Gt", "Lt"):
            return no("a zero factor makes the product exactly zero")
        return YES
    odd = neg_count % 2 == 1
    guarded = unknown(Reason.GUARDED) if s_nn else unknown()
    if op == "Gt":
        if odd:
            return no("the product has an odd number of negative factors")
        return guarded if s_nn else YES
    if op == "Ge":
        if odd and not s_nn:
            return no("the product is negative")
        return guarded if odd else YES
    if op == "Lt":
        if odd and not s_nn:
            return YES
        return no("the product is nonnegative") if not odd else guarded
    if odd:
        return YES
    return guarded if s_nn else no("the product is positive")


def _rule_sign_even_power(
    f: Expr, assumptions: Assumptions, q: Query
) -> Verdict | None:
    op = f.head.name
    base = _expr_arg(f.args[0]).args[0]

    def no(detail: str) -> No:
        return refute(
            RefutationChannel.DERIVATION,
            f,
            f,
            base,
            detail=f"even-power sign rule: {detail}",
        )

    if op == "Ge":
        return YES
    if op == "Lt":
        return no("an even power is nonnegative")
    if op == "Gt":
        if q(T.mk(S("Ne"), (base, T.ZERO))) is YES:
            return YES
        if q(T.mk(S("Eq"), (base, T.ZERO))) is YES:
            return no("the base is zero")
        return None
    if q(T.mk(S("Eq"), (base, T.ZERO))) is YES:
        return YES
    if q(T.mk(S("Ne"), (base, T.ZERO))) is YES:
        return no("a nonzero even power is positive")
    return None


def _rule_sign_nonneg_zero(
    ctx: MathContext, f: Expr, assumptions: Assumptions, q: Query
) -> Verdict | None:
    """Use the declared nonnegative-and-zero-only-on-zero function shape."""
    op = f.head.name
    u = _nonneg_zero_arg(ctx, f.args[0])
    if u is None:
        return None

    def no(detail: str) -> No:
        return refute(
            RefutationChannel.DERIVATION, f, f, u,
            detail=f"declared function shape: {detail}")

    if op == "Ge":
        return YES
    if op == "Lt":
        return no("the declared value is nonnegative")
    if op == "Gt":
        if q(T.mk(S("Ne"), (u, T.ZERO))) is YES:
            return YES
        if q(T.mk(S("Eq"), (u, T.ZERO))) is YES:
            return no("the argument is zero")
        return None
    if q(T.mk(S("Eq"), (u, T.ZERO))) is YES:
        return YES
    if q(T.mk(S("Ne"), (u, T.ZERO))) is YES:
        return no("the declared value is strictly positive")
    return None


def _rule_sign_odd_power(
    f: Expr, assumptions: Assumptions, q: Query
) -> Verdict | None:
    base = _expr_arg(f.args[0]).args[0]
    return q(T.mk(S(f.head.name), (base, T.ZERO)))


def _rule_sign_sum(
    f: Expr, assumptions: Assumptions, q: Query
) -> Verdict | None:
    op = f.head.name
    a = _expr_arg(f.args[0])

    def no(detail: str) -> No:
        return _comparison_no(
            RefutationChannel.DERIVATION, op, a, T.ZERO, detail, a, *a.args)

    if op in ("Gt", "Ge"):
        all_ge = True
        any_pos = False
        for term in a.args:
            if q(T.mk(S("Ge"), (term, T.ZERO))) is not YES:
                all_ge = False
                break
            if q(T.mk(S("Gt"), (term, T.ZERO))) is YES:
                any_pos = True
        if all_ge and any_pos:
            return YES
        all_le = True
        any_neg = False
        for term in a.args:
            if q(T.mk(S("Le"), (term, T.ZERO))) is not YES:
                all_le = False
                break
            if q(T.mk(S("Lt"), (term, T.ZERO))) is YES:
                any_neg = True
        if all_le and any_neg:
            return no("every summand is nonpositive and one is negative")
        return None
    all_le = True
    any_neg = False
    for term in a.args:
        if q(T.mk(S("Le"), (term, T.ZERO))) is not YES:
            all_le = False
            break
        if q(T.mk(S("Lt"), (term, T.ZERO))) is YES:
            any_neg = True
    if all_le and any_neg:
        return YES
    all_ge = True
    any_pos = False
    for term in a.args:
        if q(T.mk(S("Ge"), (term, T.ZERO))) is not YES:
            all_ge = False
            break
        if q(T.mk(S("Gt"), (term, T.ZERO))) is YES:
            any_pos = True
    if all_ge and any_pos:
        return no("every summand is nonnegative and one is positive")
    return None


def _rule_eq_times_zero(
    f: Expr, assumptions: Assumptions, q: Query
) -> Verdict | None:
    """Zero product over the integral domains currently supported."""
    product = _expr_arg(f.args[0])
    causes: list[Refutation] = []
    for factor in product.args:
        result = q(T.mk(S("Eq"), (factor, T.ZERO)))
        if result is YES:
            return YES
        if isinstance(result, No):
            causes.append(result.evidence)
            continue
        return unknown()
    return refute(
        RefutationChannel.DERIVATION,
        f,
        product,
        *product.args,
        detail="all factors are nonzero in an integral domain",
        causes=tuple(causes),
    )


def _rule_sign_num(
    f: Expr, assumptions: Assumptions, q: Query
) -> Verdict | None:
    sign = T.sign_num(f.args[0])
    op = f.head.name
    holds = {
        "Gt": sign > 0,
        "Ge": sign >= 0,
        "Lt": sign < 0,
        "Le": sign <= 0,
    }[op]
    if holds:
        return YES
    return refute(
        RefutationChannel.EXACT_COMPARISON, f, f,
        detail=f"exact numeric sign {sign} refutes {op}")


def _rule_eq_num(
    f: Expr, assumptions: Assumptions, q: Query
) -> Verdict | None:
    lhs, rhs = f.args
    equal = T.num_val(lhs) == T.num_val(rhs)
    holds = equal if f.head.name == "Eq" else not equal
    if holds:
        return YES
    return _comparison_no(
        RefutationChannel.EXACT_COMPARISON, f.head.name, lhs, rhs,
        "exact rational comparison")


def _rule_cmp_flip(
    f: Expr, assumptions: Assumptions, q: Query
) -> Verdict | None:
    op = f.head.name
    a, b = f.args
    if op in ("Eq", "Ne"):
        return q(T.mk(S(op), (b, a)))
    flip = {"Gt": "Lt", "Lt": "Gt", "Ge": "Le", "Le": "Ge"}
    return q(T.mk(S(flip[op]), (b, a)))


def _ctx_free(fn: ContextFreeRule) -> ContextRule:
    """Lift a context-free rule to the common rule-call protocol."""
    def wrapped(
        ctx: MathContext,
        f: Expr,
        assumptions: Assumptions,
        q: Query,
    ) -> Verdict | None:
        return fn(f, assumptions, q)

    return wrapped


# The derive rules are an explicit data table, not import-time self-registration:
# the (name, applies, fn) triples are listed once here, after the functions are
# defined, so the table is data rather than a side effect of decoration. The call
# protocol is `applies(f)` to select an entry and `fn(ctx, f, assumptions, q)` to
# derive a conclusion (None lets the next entry continue). This is the intra-module
# pipeline table; the cross-module eq_stages channel is the one that must be
# assembled explicitly by bootstrap (it carries plugins from other modules), and
# these two are deliberately different mechanisms.
_RULES: tuple[tuple[str, RuleApplies, ContextRule], ...] = (
    ("ne-from-ord", lambda f: f.head.name == "Ne", _ctx_free(_rule_ne_from_ord)),
    ("cmp-via-eq", lambda f: _is_ord(f), _ctx_free(_rule_cmp_via_eq)),
    ("sign-atom", lambda f: _is_ord(f) and f.args[1] is T.ZERO, _rule_sign_atom),
    ("sign-times", lambda f: _is_ord(f) and f.args[1] is T.ZERO and isinstance(f.args[0], T.Expr) and f.args[0].head.name == "Times", _rule_sign_times),
    ("sign-even-power", lambda f: _is_ord(f) and f.args[1] is T.ZERO and isinstance(f.args[0], T.Expr) and f.args[0].head.name == "Power" and isinstance(f.args[0].args[1], T.Int) and f.args[0].args[1].v % 2 == 0, _ctx_free(_rule_sign_even_power)),
    ("sign-nonneg-zero", lambda f: _is_ord(f) and f.args[1] is T.ZERO, _rule_sign_nonneg_zero),
    ("sign-power", lambda f: _is_ord(f) and f.args[1] is T.ZERO and isinstance(f.args[0], T.Expr) and f.args[0].head.name == "Power" and isinstance(f.args[0].args[1], T.Int) and f.args[0].args[1].v % 2 == 1, _ctx_free(_rule_sign_odd_power)),
    ("sign-sum", lambda f: _is_ord(f) and f.args[1] is T.ZERO and isinstance(f.args[0], T.Expr) and f.args[0].head.name == "Plus", _ctx_free(_rule_sign_sum)),
    ("eq-times-zero", lambda f: f.head.name == "Eq" and isinstance(f.args[0], T.Expr) and f.args[0].head.name == "Times", _ctx_free(_rule_eq_times_zero)),
    ("sign-num", lambda f: _is_ord(f) and f.args[1] is T.ZERO and T.is_num(f.args[0]), _ctx_free(_rule_sign_num)),
    ("eq-num", lambda f: f.head.name in ("Eq", "Ne") and T.is_num(f.args[0]) and T.is_num(f.args[1]), _ctx_free(_rule_eq_num)),
    ("cmp-flip", lambda f: _is_cmp(f) and f.args[0] is T.ZERO and f.args[1] is not T.ZERO, _ctx_free(_rule_cmp_flip)),
)
def _derive_layer(
    ctx: MathContext,
    fact: Expr,
    assumptions: Assumptions,
    seen: frozenset[int],
) -> Verdict | None:
    """Apply the derived-rule table under a **cycle guard**, not a depth cap: a
    fact already being derived in this chain is skipped. The reachable fact set
    is finite (every rule builds its facts out of the subterms of the original
    one and a fixed set of heads), so the guard establishes termination while
    keeping the verdict independent of how deep the query entered the layer."""
    if fact._h in seen:
        return None
    seen = seen | {fact._h}
    def q(fact: Term) -> Verdict:
        return decide(ctx, fact, assumptions, seen)
    for name, applies, fn in _RULES:
        if applies(fact):
            r = fn(ctx, fact, assumptions, q)
            if r is not None:
                return r
    return None


def _axiom_constants(
    ctx: MathContext, fact: Expr, assumptions: Assumptions
) -> Verdict | None:
    """Constant coarse-bound lemma (from the declaration's const_bounds data)."""
    if not (isinstance(fact, T.Expr) and fact.head.name in ("Gt", "Ge", "Lt", "Le")):
        return None
    a, b = fact.args
    bounds = ctx.const_bounds(a) if isinstance(a, T.Const) else None
    if bounds is None or not T.is_num(b):
        return None
    lo, hi = bounds
    bv = T.num_val(b)
    op = fact.head.name
    if op in ("Gt", "Ge"):
        if bv <= lo:
            return YES
        if bv >= hi:
            return refute(
                RefutationChannel.DERIVATION, fact, fact, b,
                detail="the comparison lies outside the declared constant range")
    else:
        if bv >= hi:
            return YES
        if bv <= lo:
            return refute(
                RefutationChannel.DERIVATION, fact, fact, b,
                detail="the comparison lies outside the declared constant range")
    return None


def _axiom_function_bounds(
    ctx: MathContext, fact: Expr, assumptions: Assumptions
) -> Verdict | None:
    """Function range-bound lemma (from the FunctionDecl.bound declaration).

    The |f|-style bounds are left to the interval channel; this handles the direct
    comparison f(u) op numeric. A bound endpoint may be None (unbounded on that
    side), and only the bounded side is endorsed."""
    if not (isinstance(fact, T.Expr) and fact.head.name in ("Gt", "Ge", "Lt", "Le")):
        return None
    a, b = fact.args
    if not (isinstance(a, T.Expr) and isinstance(a.head, T.Sym)) or not T.is_num(b):
        return None
    d = ctx.lookup_function(a.head.name)
    if d is None or d.bound is None:
        return None
    lo, hi = d.bound
    bv = T.num_val(b)
    op = fact.head.name
    # endpoints are attained (lo <= f(u) <= hi): strict and weak inequalities are
    # endorsed under different conditions
    if op == "Gt":
        if lo is not None and bv < lo:
            return YES
        if hi is not None and bv >= hi:
            return refute(
                RefutationChannel.DERIVATION, fact, fact, a, b,
                detail="the comparison lies above the declared function range")
    elif op == "Ge":
        if lo is not None and bv <= lo:
            return YES
        if hi is not None and bv > hi:
            return refute(
                RefutationChannel.DERIVATION, fact, fact, a, b,
                detail="the comparison lies above the declared function range")
    elif op == "Lt":
        if hi is not None and bv > hi:
            return YES
        if lo is not None and bv <= lo:
            return refute(
                RefutationChannel.DERIVATION, fact, fact, a, b,
                detail="the comparison lies below the declared function range")
    else:  # Le
        if hi is not None and bv >= hi:
            return YES
        if lo is not None and bv < lo:
            return refute(
                RefutationChannel.DERIVATION, fact, fact, a, b,
                detail="the comparison lies below the declared function range")
    return None


# Same as _RULES: explicit data, built after the functions are defined, not a
# decorator side effect. These are the declaration-bound fallback lemmas.
_AXIOM_CHECKS = (_axiom_constants, _axiom_function_bounds)
def _family_cmp(
    ctx: MathContext,
    fact: Expr,
    assumptions: Assumptions,
    seen: frozenset[int],
) -> Verdict:
    op = fact.head.name
    a, b = fact.args
    if op in ("Eq", "Ne"):
        r = _same(op, a, b)
        if r is not None:
            return r
        r = _cmp_numeric(op, a, b)
        if r is not None:
            return r
        r = _facts_lookup(ctx, fact, assumptions)
        if r is not None:
            return r
        if op == "Eq":
            # A No from the identity channel needs evidence: only when both sides
            # are closed is "not identically zero" a statement about values. With
            # open sides the query stays with the frame-relative channels (and is
            # honestly undecided when none of them answers) instead of being
            # refuted by a non-identity.
            r = _poly_eq_check(ctx, a, b)
            if r is not None and r.is_no() and not (is_closed(a) and is_closed(b)):
                r = None
            if r is not None:
                return r
        r = _cmp_interval(ctx, op, a, b, assumptions)
        if r is not None:
            return r
    else:
        r = _cmp_numeric(op, a, b)
        if r is not None:
            return r
        r = _same(op, a, b)
        if r is not None:
            return r
        r = _facts_lookup(ctx, fact, assumptions)
        if r is not None:
            return r
        r = _cmp_interval(ctx, op, a, b, assumptions)
        if r is not None:
            return r
        r = _chain_query(ctx, op, a, b, assumptions)
        if r is not None:
            return r
    r = _derive_layer(ctx, fact, assumptions, seen)
    if r is not None:
        return r
    # The axiom layer (declaration bound data) is a **fallback**, not dead code: it
    # consumes the same declarations as the interval channel (const_bounds and
    # FunctionDecl.bound), but the interval channel is more general because it can
    # bound a compound expression a-b as a whole, so the interval channel usually
    # decides first and this layer only gets a turn when every earlier channel yielded
    # (returned None). Deleting it would leave the declaration bound data with a
    # single consumption path. The relationship is pinned by
    # tests/test_decide_axioms.py.
    for ax in _AXIOM_CHECKS:
        r = ax(ctx, fact, assumptions)
        if r is not None:
            return r
    return unknown()


# The ledger-equality substitution that used to live here was removed. Using a
# frame's equations as a bidirectional rewrite system is not a decision
# procedure: it has no termination measure (it needed a hardcoded depth cap) and
# it rewrote values into variables, which produced false refutations and made the
# verdict depend on the entry depth. Deciding an equation relative to a frame now
# goes through `closure_decide` in cas/math/base/equality.py, which orients every
# equation towards a canonical class representative and never uses an assumption
# as an open-ended rewrite rule.


def decide(
    ctx: MathContext,
    fact: Term,
    assumptions: AssumptionFrame,
    _seen: frozenset[int] = frozenset(),
) -> Verdict:
    """Decide a proposition relative to an assumption frame.

    `_seen` is a **cycle guard** — the term ids on the current derivation chain
    — not a depth budget: a fact met twice on one chain is skipped. There is no
    search-depth cap, so a verdict cannot depend on the entry depth.
    """
    assumptions = _A(assumptions)
    if fact is T.TRUE:
        return YES
    if fact is T.FALSE:
        return refute(
            RefutationChannel.LOGICAL, fact, fact,
            detail="the false proposition was queried")
    if isinstance(fact, T.Expr):
        name = fact.head.name
        if name in _CMP:
            if name in _ORD:
                # An order comparison is read over an ordered domain; a constant
                # declared not real is evidence that no such reading applies.
                # Answering regardless is how `i^2 >= 0` came out YES: the sign
                # rules for powers and sums are ordered-field facts.
                if _nonreal_constant(ctx, fact) is not None:
                    return unknown(Reason.FRAGMENT)
            if name == "Eq":
                # Frame-relative reasoning about an equation goes through the
                # closure channel: it orients the frame's equalities towards
                # canonical class representatives instead of rewriting in both
                # directions. It answers Yes or nothing; a No with evidence is
                # left to the channels below.
                a_eq, b_eq = fact.args
                r = closure_decide(ctx, a_eq, b_eq, assumptions)
                if r is not None:
                    return r
            return _family_cmp(ctx, fact, assumptions, _seen)
        if name == "And":
            result: Verdict | None = None
            for arg in fact.args:
                child = decide(ctx, arg, assumptions, _seen)
                result = (
                    contextualize(child, fact, "a conjunct was refuted")
                    if result is None
                    else and3(result, child, fact)
                )
                if result.is_no():
                    return result
            return result if result is not None else YES
        if name == "Or":
            result = None
            for arg in fact.args:
                child = decide(ctx, arg, assumptions, _seen)
                result = child if result is None else or3(result, child, fact)
                if result is YES:
                    return result
            if result is None:
                return YES
            if isinstance(result, No) and result.evidence.proposition is not fact:
                return contextualize(result, fact, "every disjunct was refuted")
            return result
        if name == "Not":
            return not3(decide(ctx, fact.args[0], assumptions, _seen), fact)
    return unknown()


def satisfiable(
    ctx: MathContext,
    constraints: Sequence[Term],
    assumptions: AssumptionFrame,
) -> Verdict:
    if not constraints:
        return YES
    assumptions = _A(assumptions)
    claim = T.mk(S("And"), tuple(constraints))
    for i, constraint in enumerate(constraints):
        frame = assumptions.extended(
            *[other for j, other in enumerate(constraints) if j != i])
        direct = decide(ctx, constraint, frame)
        if isinstance(direct, No):
            return refute(
                RefutationChannel.BRANCH, claim, constraint,
                detail="one required constraint was refuted",
                causes=(direct.evidence,))
        opposite = negate(ctx, constraint)
        if decide(ctx, opposite, frame) is YES:
            return refute(
                RefutationChannel.LOGICAL, claim, constraint, opposite,
                detail="the negation of one required constraint was proved")
    return unknown()


def domain_ok(
    ctx: MathContext, fact: Term, assumptions: AssumptionFrame
) -> Verdict:
    from cas.math.domcond import dom_condition

    return satisfiable(ctx, dom_condition(ctx, fact), assumptions)


# Identity stages: pipeline dispatch is declaration data rather than hardcoding.
# The stages travel in the math context (declared by each module's `install(builder)`
# and assembled by bootstrap), so this module keeps no stage table of its own and
# importing it has zero side effects: without a context no decision can be started
# at all. Stage contract: run(ctx, r, a, b, assumptions) -> Verdict conclusion, or
# None to let the next stage continue. An exception inside a stage means the stage
# has a bug and propagates, since failure is part of the return value and must not
# be swallowed; a stage that genuinely has no conclusion returns None explicitly.
def equivalent(
    ctx: MathContext,
    a: Term,
    b: Term,
    assumptions: AssumptionFrame = None,
    budget: int = 100000,
) -> Verdict:
    """The unified identity pipeline: pointer -> numeric constants -> normal-form
    zero test -> registered stage sequence -> honest UNKNOWN.

    Domain normal-form zeroing goes through autosimplify plus the projection zero
    test; a tower normal form would attach later as a registered stage."""
    from cas.math.simplify import autosimplify

    if a is b:
        return YES
    if T.is_num(a) and T.is_num(b):
        return _comparison_no(
            RefutationChannel.EXACT_COMPARISON, "Eq", a, b,
            "exact rational values differ")
    a = _qfold(a)
    b = _qfold(b)
    if a is b:
        return YES
    if T.is_num(a) and T.is_num(b):
        return _comparison_no(
            RefutationChannel.EXACT_COMPARISON, "Eq", a, b,
            "exact rational values differ")
    r = autosimplify(ctx, T.plus(a, T.neg(b)), budget)
    if r is T.ZERO:
        return YES
    from cas.math.project import zero_of
    z = zero_of(ctx, r)
    if z is True:
        return YES
    if z is False:
        return _comparison_no(
            RefutationChannel.NORMAL_FORM, "Eq", a, b,
            "the projected difference is nonzero", r)
    assumptions = _A(assumptions)
    for stage in ctx.decision_stages:
        d = stage.run(ctx, r, a, b, assumptions)
        if d is not None and not d.is_unknown():
            return d
    return unknown()


# A trigonometric-basis zeroing stage has not been rebuilt; when the zero channel
# cannot cover an exp/sin combination, the decision must be **honestly undecided**
# rather than reported as refuted (see _judge_zero_diff in
# calculus/integration/verify.py). Such a stage would attach later through the same
# protocol as a new eq_stage without changing the decider.

# The numeric sampling stage was permanently removed. "Not found" and "does not
# exist" are two different conclusions, and sampling was never entitled to produce
# the latter.


# ---------------------------------------------------------------------------
# Decision operations on a context (moved out of kernel/context.py)
#
# These two operations must call this module's decider, so they can only live on the
# math side: `kernel -> concrete math module` is strictly forbidden. They reference
# the kernel Context/Branch, which is a legal math -> kernel dependency.
# ---------------------------------------------------------------------------

def extend_frame(
    ctx: MathContext, assumptions: AssumptionFrame, fact: Term
) -> tuple[Verdict, Assumptions | None]:
    """Return the frame with `fact` added, or `(Verdict, None)` when the fact is
    not even readable in the current declared domains.

    Adding a fact to a frame is **not** a consistency check. An inconsistent
    frame is the user's (or a branch's) hypothesis and the system reasons under
    it instead of policing it; the only refusal here is a domain violation, i.e.
    a fact whose own predicates cannot be read over the declared domains.
    """
    assumptions = _A(assumptions)
    domain_verdict = domain_ok(ctx, fact, assumptions)
    if domain_verdict.is_no():
        return domain_verdict, None
    return YES, assumptions.extended(fact)


def branch(
    ctx: MathContext, assumptions: AssumptionFrame, *conds: Term
) -> list[tuple[Term, Assumptions | None, Literal["open", "empty"]]]:
    """Split one branch per condition:
    `[(condition, that branch's assumption set | None, "open"|"empty")]`.

    The assumption set is immutable, so branching is a few `extended` calls on
    the same base point: no cloning and no undoing. A branch is "empty" only when
    its condition is not readable in the declared domains; **contradictory
    conditions stay open by design**, because the system has no global
    consistency notion to police.
    """
    assumptions = _A(assumptions)
    out: list[tuple[Term, Assumptions | None, Literal["open", "empty"]]] = []
    for condition in conds:
        status, extended = extend_frame(ctx, assumptions, condition)
        branch_status: Literal["open", "empty"] = (
            "empty" if status.is_no() else "open"
        )
        out.append((condition, extended, branch_status))
    return out
