# -*- coding: utf-8 -*-
"""Decision pipeline: proposition composition plus domain-specific decidable atoms.

The return value is the decision ADT (cas/verdict): Yes/No/Unknown(reason). The
reasons distinguish a fragment the pipeline does not cover (FRAGMENT), a fact
blocked by a condition (GUARDED), a genuinely undecidable question (UNDECIDABLE),
and an exhausted budget (BUDGET) -- four different consequences that must never be
folded into one "don't know".

Atom channels, in order: pointer/numeric -> direct ledger lookup -> projection zero
test (domain normal form) -> interval propagation -> order-chain inference -> derived
rule layer -> declaration lemmas (constant coarse bounds, function range bounds).

Every entry point takes the math context as its first parameter: the declaration
surface (constants, functions, domain conditions) and the identity-decision stages
travel there, so this module keeps no handle of its own and importing it has zero
side effects.
"""

from collections import deque

from cas.syntax import term as T
from cas.syntax.term import S
from cas.math.domains.qarith import fold as _qfold
from cas.kernel.verdict import (Verdict, Reason, YES, NO, unknown,
                          and3, or3, not3)
from cas.kernel.scope import Assumptions


def _A(a):
    """None is treated as the empty assumption set (older call sites pass None)."""
    return a if a is not None else Assumptions()


_NEG = {
    "Gt": "Le",
    "Ge": "Lt",
    "Lt": "Ge",
    "Le": "Gt",
    "Eq": "Ne",
    "Ne": "Eq",
}


_ORD = ("Lt", "Le", "Gt", "Ge")


def _nonreal_constant(ctx, t):
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


def _ordered_fact(ctx, f):
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


def negate(ctx, f):
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


def _cmp_numeric(op, a, b):
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
    return YES if r else NO


def _same(op, a, b):
    if a is not b:
        return None
    if op in ("Eq", "Le", "Ge"):
        return YES
    return NO


def _poly_eq_check(ctx, a, b):
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
        return NO
    return None


def _facts_lookup(ctx, fact, assumptions):
    for f in assumptions:
        if f is fact:
            return YES
        if f is negate(ctx, fact):
            return NO
        if isinstance(f, T.Expr) and isinstance(fact, T.Expr):
            if f.head.name in _CMP_INV and fact.head.name in _CMP_INV:
                if (
                    f.head.name == _CMP_INV[fact.head.name]
                    and f.args[0] is fact.args[1]
                    and f.args[1] is fact.args[0]
                ):
                    return YES
    return None


def _chain_query(ctx, op, a, b, assumptions):
    """Order-chain BFS: ledger inequalities become edges and the transitive closure
    answers queries of the form a<b.

    A state is (node, whether the path contains a strict edge), and the best
    strictness per node is recorded. Numeric-bound inference and equality
    substitution belong to the interval channel; here only graph edges are walked.
    An assumption carrying a constant declared not real is not an order edge
    (`_ordered_fact`) and is skipped: otherwise `x < i` and `i < 3` would chain
    to `x < 3` where the ordered reading does not apply.
    """
    adj = {}
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
            adj.setdefault(u, []).append((v, opf == "Lt"))
    if a is b:
        return YES if op in ("Le", "Ge", "Eq") else NO
    start, goal = want
    best = {start._h: False}
    queue = deque([(start, False)])
    while queue:
        cur, evs = queue.popleft()
        if best.get(cur._h, False) != evs:
            continue                       # stale state: a better strictness was found
        for nxt, st in adj.get(cur, ()):
            ns = evs or st
            if nxt is goal and (not strict or ns):
                return YES
            prev = best.get(nxt._h)
            if prev is None or (ns and not prev):
                best[nxt._h] = ns
                queue.append((nxt, ns))
    return None


def _interval(ctx, t, assumptions, seen=None, depth=0):
    """Numeric interval propagation: (lo, hi, lo_strict, hi_strict) with either
    endpoint possibly None (unbounded).

    Sources: numeric atoms / declared constant axiom bounds / direct ledger numeric
    bounds / ledger equality substitution (recursive) / Plus sums / numeric scalar
    Times scaling / even powers and Abs being nonnegative. An assumption carrying a
    constant declared not real is not an ordered bound (`_ordered_fact`), so it is
    skipped. It reads only the term and the ledger and never calls back into decide
    (to prevent cycles). Returns None when there is no information at all.
    """
    from fractions import Fraction as Fr

    if T.is_num(t):
        v = T.num_val(t)
        return (v, v, False, False)
    lb = ctx.const_bounds(t)
    if lb is not None:
        return (Fr(lb[0]), Fr(lb[1]), True, True)
    if depth > 8:
        return None
    if seen is None:
        seen = set()
    if t._h in seen:
        return None
    seen.add(t._h)
    lo = hi = None
    los = his = False
    is_int = False

    def tighten(nlo, nlos, nhi, nhis):
        nonlocal lo, hi, los, his
        if nlo is not None and (lo is None or nlo > lo or (nlo == lo and nlos)):
            lo, los = nlo, nlos
        if nhi is not None and (hi is None or nhi < hi or (nhi == hi and nhis)):
            hi, his = nhi, nhis

    for f in assumptions:
        if not isinstance(f, T.Expr):
            continue
        n = f.head.name
        if n == "Attr" and f.args[0] is t and f.args[1].name == "integer":
            is_int = True
            continue
        # Ordered information from an assumption carrying a constant declared not
        # real is not consumed (neither as a bound nor as an equality that would
        # bound through substitution): the ordered reading does not apply there.
        if not _ordered_fact(ctx, f):
            continue
        if n in ("Lt", "Le", "Gt", "Ge"):
            u, v = f.args
            if u is t and T.is_num(v):
                bv = T.num_val(v)
                if n == "Lt":
                    tighten(None, False, bv, True)
                elif n == "Le":
                    tighten(None, False, bv, False)
                elif n == "Gt":
                    tighten(bv, True, None, False)
                else:
                    tighten(bv, False, None, False)
            elif v is t and T.is_num(u):
                bv = T.num_val(u)
                if n == "Lt":
                    tighten(bv, True, None, False)
                elif n == "Le":
                    tighten(bv, False, None, False)
                elif n == "Gt":
                    tighten(None, False, bv, True)
                else:
                    tighten(None, False, bv, False)
        elif n == "Eq":
            u, v = f.args
            o = v if u is t else (u if v is t else None)
            if o is not None and o is not t:
                if T.is_num(o):
                    # constant equality x=c: x is exactly c with non-strict endpoints,
                    # so that x=5 does not imply x<5
                    bv = T.num_val(o)
                    tighten(bv, False, bv, False)
                else:
                    # variable equality x=y: x and y share a value, so interval and
                    # strictness pass through transparently
                    iv = _interval(ctx, o, assumptions, seen, depth + 1)
                    if iv is not None:
                        tighten(*iv)
    if is_int:
        # consume the integer attribute: tighten endpoints to the nearest integer
        # (x>2 and x in Z implies x>=3)
        if lo is not None:
            c = lo.numerator // lo.denominator + 1 if los else -((-lo.numerator) // lo.denominator)
            if c > lo or los:
                lo, los = c, False
        if hi is not None:
            c = -((-hi.numerator) // hi.denominator) - 1 if his else hi.numerator // hi.denominator
            if c < hi or his:
                hi, his = c, False
    if isinstance(t, T.Expr):
        n = t.head.name
        if n == "Plus":
            ivs = [_interval(ctx, a, assumptions, seen, depth + 1) for a in t.args]
            if all(iv is not None for iv in ivs):
                slo = sum(iv[0] for iv in ivs) if all(iv[0] is not None for iv in ivs) else None
                shi = sum(iv[1] for iv in ivs) if all(iv[1] is not None for iv in ivs) else None
                st = any(iv[2] for iv in ivs if iv[0] is not None)
                sht = any(iv[3] for iv in ivs if iv[1] is not None)
                tighten(slo, st, shi, sht)
        elif n == "Times":
            nums = [a for a in t.args if T.is_num(a)]
            rest = [a for a in t.args if not T.is_num(a)]
            if nums and len(rest) == 1:
                c = Fr(1)
                for nn in nums:
                    c *= T.num_val(nn)
                iv = _interval(ctx, rest[0], assumptions, seen, depth + 1)
                if iv is not None:
                    if c > 0:
                        tighten(
                            None if iv[0] is None else c * iv[0], iv[2],
                            None if iv[1] is None else c * iv[1], iv[3],
                        )
                    elif c < 0:
                        tighten(
                            None if iv[1] is None else c * iv[1], iv[3],
                            None if iv[0] is None else c * iv[0], iv[2],
                        )
        elif n == "Power" and isinstance(t.args[1], T.Int) and t.args[1].v % 2 == 0:
            tighten(Fr(0), False, None, False)
        else:
            # declared function range bound: endpoints are attained (lo <= f <= hi),
            # so strictness is false
            bd = _func_bound(ctx, n)
            if bd is not None:
                tighten(bd[0], False, bd[1], False)
    if lo is None and hi is None:
        return None
    return (lo, hi, los, his)


def _cmp_interval(ctx, op, a, b, assumptions):
    """Reduce a op b to an interval comparison of d = a - b against 0 (d first folded
    over Q literals)."""
    d = _qfold(T.plus(a, T.neg(b)))
    if op in ("Eq", "Ne"):
        if d is T.ZERO:
            return YES if op == "Eq" else NO
        iv = _interval(ctx, d, assumptions)
        if iv is not None:
            lo, hi, _, _ = iv
            away = (lo is not None and lo > 0) or (hi is not None and hi < 0)
            if away:
                return NO if op == "Eq" else YES
        return None
    if d is T.ZERO:
        return YES if op in ("Le", "Ge") else NO
    iv = _interval(ctx, d, assumptions)
    if iv is None:
        return None
    lo, hi, los, his = iv
    if lo is not None and hi is not None and lo == hi and not los and not his:
        # the closed interval degenerates to a point, i.e. an exact value: decide directly
        if op == "Gt":
            return YES if lo > 0 else NO
        if op == "Ge":
            return YES if lo >= 0 else NO
        if op == "Lt":
            return YES if lo < 0 else NO
        return YES if lo <= 0 else NO
    if op == "Gt":
        if (lo is not None and lo > 0) or (lo == 0 and los):
            return YES
        if (hi is not None and hi < 0) or (hi == 0 and his):
            return NO
    elif op == "Ge":
        if lo is not None and lo >= 0:
            return YES
        if (hi is not None and hi < 0) or (hi == 0 and his):
            return NO
    elif op == "Lt":
        if (hi is not None and hi < 0) or (hi == 0 and his):
            return YES
        if (lo is not None and lo > 0) or (lo == 0 and los):
            return NO
    else:  # Le
        if hi is not None and hi <= 0:
            return YES
        if (lo is not None and lo > 0) or (lo == 0 and los):
            return NO
    return None


# ---------------------------------------------------------------------------
# Symbolic structure lemmas
# ---------------------------------------------------------------------------

def _func_bound(ctx, name):
    """Declared function range bound: returns (lo|None, hi|None) or None."""
    d = ctx.lookup_function(name)
    return d.bound if d is not None else None


def _nonneg_zero_arg(ctx, t):
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


def _nneg(ctx, t, assumptions):
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


def _pos(ctx, t, assumptions):
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


_MAX_DEPTH = 6


def _is_cmp(f):
    return isinstance(f, T.Expr) and f.head.name in _CMP


def _is_ord(f):
    return isinstance(f, T.Expr) and f.head.name in ("Lt", "Le", "Gt", "Ge")


def _zero_cmp_of(ctx, a, assumptions, q, op):
    nneg = _nneg(ctx, a, assumptions)
    pos = _pos(ctx, a, assumptions)
    if op == "Gt":
        if pos is True:
            return YES
        if nneg is False or (nneg is True and pos is False):
            return NO
        return None
    if op == "Ge":
        if nneg is True:
            return YES
        if nneg is False:
            return NO
        return None
    if op == "Lt":
        if pos is True:
            return NO
        if nneg is False:
            return YES
        if nneg is True and pos is False:
            return NO
        return None
    if op == "Le":
        if pos is True:
            return NO
        if nneg is False:
            return YES
        if nneg is True and pos is False:
            return YES
        return None
    return None


def _rule_ne_from_ord(f, assumptions, q):
    a, b = f.args
    if q(T.mk(S("Gt"), (a, b))) is YES or q(T.mk(S("Lt"), (a, b))) is YES:
        return YES
    if q(T.mk(S("Eq"), (a, b))) is YES:
        return NO
    return None


def _rule_cmp_via_eq(f, assumptions, q):
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


def _sign_of_term(ctx, t, assumptions, q):
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


def _rule_sign_atom(ctx, f, assumptions, q):
    return _zero_cmp_of(ctx, f.args[0], assumptions, q, f.head.name)


def _rule_sign_times(ctx, f, assumptions, q):
    op = f.head.name
    a = f.args[0]
    s_zero = False
    s_nn = False
    neg_count = 0
    for fac in a.args:
        s = _sign_of_term(ctx, fac, assumptions, q)
        if s is None:
            return None
        if s == 0:
            s_zero = True
        elif s == -1:
            neg_count += 1
        elif s == 2:
            s_nn = True
    if s_zero:
        return NO if op in ("Gt", "Lt") else YES
    odd = neg_count % 2 == 1
    # an undecided nonnegative factor blocks the answer, which can flip once the
    # condition is discharged
    guarded = unknown(Reason.GUARDED) if s_nn else unknown()
    if op == "Gt":
        if odd:
            return NO
        return YES if not s_nn else guarded
    if op == "Ge":
        if odd and not s_nn:
            return NO
        return guarded if odd else YES
    if op == "Lt":
        if odd and not s_nn:
            return YES
        return guarded if odd else NO
    return YES if odd else (guarded if s_nn else NO)


def _rule_sign_even_power(f, assumptions, q):
    op = f.head.name
    b = f.args[0].args[0]
    if op in ("Ge",):
        return YES
    if op == "Lt":
        return NO
    if op == "Gt":
        r = q(T.mk(S("Ne"), (b, T.ZERO)))
        if r is YES:
            return YES
        r = q(T.mk(S("Eq"), (b, T.ZERO)))
        if r is YES:
            return NO
        return None
    r = q(T.mk(S("Eq"), (b, T.ZERO)))
    if r is YES:
        return YES
    r = q(T.mk(S("Ne"), (b, T.ZERO)))
    if r is YES:
        return NO
    return None


def _rule_sign_nonneg_zero(ctx, f, assumptions, q):
    """Sign of g(u) against 0 where g is declared nonnegative with g(u)=0 iff u=0
    (absolute-value / norm family): g>=0 always true and g<0 always false, while
    g>0 iff u!=0 and g<=0 iff u=0. The decision rests on the declaration, not the
    name. Returns None when the argument carries no declaration of that shape."""
    op = f.head.name
    u = _nonneg_zero_arg(ctx, f.args[0])
    if u is None:
        return None
    if op == "Ge":
        return YES
    if op == "Lt":
        return NO
    if op == "Gt":
        r = q(T.mk(S("Ne"), (u, T.ZERO)))
        if r is YES:
            return YES
        r = q(T.mk(S("Eq"), (u, T.ZERO)))
        if r is YES:
            return NO
        return None
    r = q(T.mk(S("Eq"), (u, T.ZERO)))
    if r is YES:
        return YES
    r = q(T.mk(S("Ne"), (u, T.ZERO)))
    if r is YES:
        return NO
    return None


def _rule_sign_odd_power(f, assumptions, q):
    b = f.args[0].args[0]
    return q(T.mk(S(f.head.name), (b, T.ZERO)))


def _rule_sign_sum(f, assumptions, q):
    op = f.head.name
    a = f.args[0]
    if op in ("Gt", "Ge"):
        all_ge = True
        any_pos = False
        for t_ in a.args:
            r = q(T.mk(S("Ge"), (t_, T.ZERO)))
            if r is not YES:
                all_ge = False
                break
            r2 = q(T.mk(S("Gt"), (t_, T.ZERO)))
            if r2 is YES:
                any_pos = True
        if all_ge and any_pos:
            return YES
        all_le = True
        any_neg = False
        for t_ in a.args:
            r = q(T.mk(S("Le"), (t_, T.ZERO)))
            if r is not YES:
                all_le = False
                break
            r2 = q(T.mk(S("Lt"), (t_, T.ZERO)))
            if r2 is YES:
                any_neg = True
        if all_le and any_neg:
            return NO
        return None
    all_le = True
    any_neg = False
    for t_ in a.args:
        r = q(T.mk(S("Le"), (t_, T.ZERO)))
        if r is not YES:
            all_le = False
            break
        r2 = q(T.mk(S("Lt"), (t_, T.ZERO)))
        if r2 is YES:
            any_neg = True
    if all_le and any_neg:
        return YES
    all_ge = True
    any_pos = False
    for t_ in a.args:
        r = q(T.mk(S("Ge"), (t_, T.ZERO)))
        if r is not YES:
            all_ge = False
            break
        r2 = q(T.mk(S("Gt"), (t_, T.ZERO)))
        if r2 is YES:
            any_pos = True
    if all_ge and any_pos:
        return NO
    return None


def _rule_eq_times_zero(f, assumptions, q):
    """Zero product. Premise: every coefficient structure this system builds (Q, K[x],
    K(x), algebraic and transcendental towers) is an integral domain, so ab=0 iff a=0
    or b=0. If a non-domain structure such as a matrix ring is ever introduced, this
    rule must be gated on the ambient domain."""
    a = f.args[0]
    any_zero = NO
    for fac in a.args:
        r = q(T.mk(S("Eq"), (fac, T.ZERO)))
        if r is YES:
            return YES
        if r is not NO:
            any_zero = unknown()
    return any_zero


def _rule_sign_num(f, assumptions, q):
    s = T.sign_num(f.args[0])
    op = f.head.name
    if op == "Gt":
        return YES if s > 0 else NO
    if op == "Ge":
        return YES if s >= 0 else NO
    if op == "Lt":
        return YES if s < 0 else NO
    return YES if s <= 0 else NO


def _rule_eq_num(f, assumptions, q):
    if f.head.name == "Eq":
        return YES if T.num_val(f.args[0]) == T.num_val(f.args[1]) else NO
    return YES if T.num_val(f.args[0]) != T.num_val(f.args[1]) else NO


def _rule_cmp_flip(f, assumptions, q):
    op = f.head.name
    a, b = f.args
    if op in ("Eq", "Ne"):
        return q(T.mk(S(op), (b, a)))
    flip = {"Gt": "Lt", "Lt": "Gt", "Ge": "Le", "Le": "Ge"}
    return q(T.mk(S(flip[op]), (b, a)))


def _ctx_free(fn):
    """Lift a derive rule that reads no declarations to the table's `fn(ctx, ...)`
    call protocol, so every `_RULES` entry has the same call shape. A rule that
    reads declarations takes the context itself as its first parameter and appears
    in the table unwrapped."""
    return lambda ctx, f, assumptions, q: fn(f, assumptions, q)


# The derive rules are an explicit data table, not import-time self-registration:
# the (name, applies, fn) triples are listed once here, after the functions are
# defined, so the table is data rather than a side effect of decoration. The call
# protocol is `applies(f)` to select an entry and `fn(ctx, f, assumptions, q)` to
# derive a conclusion (None lets the next entry continue). This is the intra-module
# pipeline table; the cross-module eq_stages channel is the one that must be
# assembled explicitly by bootstrap (it carries plugins from other modules), and
# these two are deliberately different mechanisms.
_RULES = (
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
def _derive_layer(ctx, fact, assumptions, depth):
    q = lambda f: decide(ctx, f, assumptions, depth + 1)
    for name, applies, fn in _RULES:
        if applies(fact):
            r = fn(ctx, fact, assumptions, q)
            if r is not None:
                return r
    return None


def _axiom_constants(ctx, fact, assumptions):
    """Constant coarse-bound lemma (from the declaration's const_bounds data)."""
    if not (isinstance(fact, T.Expr) and fact.head.name in ("Gt", "Ge", "Lt", "Le")):
        return None
    a, b = fact.args
    bounds = ctx.const_bounds(a)
    if bounds is None or not T.is_num(b):
        return None
    lo, hi = bounds
    bv = T.num_val(b)
    op = fact.head.name
    if op in ("Gt", "Ge"):
        if bv <= lo:
            return YES
        if bv >= hi:
            return NO
    else:
        if bv >= hi:
            return YES
        if bv <= lo:
            return NO
    return None


def _axiom_function_bounds(ctx, fact, assumptions):
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
            return NO
    elif op == "Ge":
        if lo is not None and bv <= lo:
            return YES
        if hi is not None and bv > hi:
            return NO
    elif op == "Lt":
        if hi is not None and bv > hi:
            return YES
        if lo is not None and bv <= lo:
            return NO
    else:  # Le
        if hi is not None and bv >= hi:
            return YES
        if lo is not None and bv < lo:
            return NO
    return None


# Same as _RULES: explicit data, built after the functions are defined, not a
# decorator side effect. These are the declaration-bound fallback lemmas.
_AXIOM_CHECKS = (_axiom_constants, _axiom_function_bounds)
def _family_cmp(ctx, fact, assumptions, depth):
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
            r = _poly_eq_check(ctx, a, b)
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
    r = _derive_layer(ctx, fact, assumptions, depth)
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


def _contains(t, pat):
    if t is pat:
        return True
    if isinstance(t, T.Expr):
        return any(_contains(a, pat) for a in t.args)
    return False


def _eq_subst(ctx, fact, assumptions, depth):
    """Ledger equality substitution: substitute each Eq(u,v) from the ledger into the
    queried fact in both directions and decide again.

    Not restricted to numeric sides: a symbolic equality (such as the substitution
    definition t = sin(x)) endorses a query just as well, since deciding relative to
    the ledger means "decide under the assumptions". _MAX_DEPTH guards against
    chained cycles.
    """
    a, b = fact.args
    for f in assumptions:
        if isinstance(f, T.Expr) and f.head.name == "Eq" and f is not fact:
            u, v = f.args
            if not (_contains(a, u) or _contains(a, v) or _contains(b, u) or _contains(b, v)):
                continue
            for pat, rep in ((u, v), (v, u)):
                na = T.subst(a, {pat: rep})
                nb = T.subst(b, {pat: rep})
                if na is a and nb is b:
                    continue
                r = decide(ctx, T.mk(S("Eq"), (na, nb)), assumptions, depth + 1)
                if not r.is_unknown():
                    return r
    return None


def decide(ctx, fact, assumptions, _depth=0) -> Verdict:
    assumptions = _A(assumptions)
    if _depth > _MAX_DEPTH:
        return unknown(Reason.BUDGET)
    if fact is T.TRUE:
        return YES
    if fact is T.FALSE:
        return NO
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
                r = _eq_subst(ctx, fact, assumptions, _depth)
                if r is not None:
                    return r
            return _family_cmp(ctx, fact, assumptions, _depth)
        if name == "And":
            r = YES
            for a in fact.args:
                r = and3(r, decide(ctx, a, assumptions, _depth))
                if r is NO:
                    return r
            return r
        if name == "Or":
            r = NO
            for a in fact.args:
                r = or3(r, decide(ctx, a, assumptions, _depth))
                if r is YES:
                    return r
            return r
        if name == "Not":
            return not3(decide(ctx, fact.args[0], assumptions, _depth))
    return unknown()


def satisfiable(ctx, constraints, assumptions) -> Verdict:
    assumptions = _A(assumptions)
    for i, c in enumerate(constraints):
        tmp = assumptions.extended(*[d for j, d in enumerate(constraints) if j != i])
        if decide(ctx, c, tmp) is NO or decide(ctx, negate(ctx, c), tmp) is YES:
            return NO
    return YES if not constraints else unknown()


def domain_ok(ctx, fact, assumptions) -> Verdict:
    from cas.math.domcond import dom_condition

    return satisfiable(ctx, dom_condition(ctx, fact), assumptions)


def contradicted(ctx, fact, assumptions) -> bool:
    return decide(ctx, fact, assumptions) is NO or decide(ctx, negate(ctx, fact), assumptions) is YES


# Identity stages: pipeline dispatch is declaration data rather than hardcoding.
# The stages travel in the math context (declared by each module's `install(builder)`
# and assembled by bootstrap), so this module keeps no stage table of its own and
# importing it has zero side effects: without a context no decision can be started
# at all. Stage contract: run(ctx, r, a, b, assumptions) -> Verdict conclusion, or
# None to let the next stage continue. An exception inside a stage means the stage
# has a bug and propagates, since failure is part of the return value and must not
# be swallowed; a stage that genuinely has no conclusion returns None explicitly.
def equivalent(ctx, a, b, assumptions=None, budget=100000) -> Verdict:
    """The unified identity pipeline: pointer -> numeric constants -> normal-form
    zero test -> registered stage sequence -> honest UNKNOWN.

    Domain normal-form zeroing goes through autosimplify plus the projection zero
    test; a tower normal form would attach later as a registered stage."""
    from cas.math.simplify import autosimplify

    if a is b:
        return YES
    if T.is_num(a) and T.is_num(b):
        return YES if T.num_val(a) == T.num_val(b) else NO
    a = _qfold(a)
    b = _qfold(b)
    if a is b:
        return YES
    if T.is_num(a) and T.is_num(b):
        return YES if T.num_val(a) == T.num_val(b) else NO
    r = autosimplify(ctx, T.plus(a, T.neg(b)), budget)
    if r is T.ZERO:
        return YES
    from cas.math.project import zero_of
    z = zero_of(ctx, r)
    if z is True:
        return YES
    if z is False:
        return NO
    assumptions = _A(assumptions)
    for _name, run in ctx.eq_stages:
        d = run(ctx, r, a, b, assumptions)
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

def extend_checked(ctx, assumptions, fact):
    """Return the **extended assumption set** after the domain check and the
    contradiction check both pass (immutable, the original object is not modified).

    Returns `(Verdict, Assumptions | None)`, with the second element None on failure.
    This replaces the old in-place mutable-context check-and-assume.
    """
    from cas.kernel.verdict import NO, YES
    assumptions = _A(assumptions)
    if domain_ok(ctx, fact, assumptions) is NO:
        return NO, None
    if contradicted(ctx, fact, assumptions):
        return NO, None
    return YES, assumptions.extended(fact)


def branch(ctx, assumptions, *conds):
    """Split one branch per condition:
    `[(condition, that branch's assumption set | None, "open"|"empty")]`.

    The assumption set is immutable, so branching is just a few `extended` calls on
    the same base point: no cloning and no undoing. The independent sub-scopes of the
    branch feature are expressed by the kernel ScopeStore, not here.
    """
    from cas.kernel.verdict import NO
    assumptions = _A(assumptions)
    out = []
    for c in conds:
        st, ext = extend_checked(ctx, assumptions, c)
        out.append((c, ext, "empty" if st is NO else "open"))
    return out
