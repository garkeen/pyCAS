"""Equality: domain normal form, three-valued identity, and the ledger closure.

**The domain normal form is the decision procedure for identities.** This is not
a simplifier guessing: equality of two expressions is decided by reducing to a
canonical form and comparing.

Two different questions live here and must never be conflated:

· *identity* — "are these two expressions the same function?" — is answered by
  `identity_verdict` through the domain normal form and the registered stages.
  A difference that is not identically zero is a legitimate No here.
· *entailment under assumptions* — "does the assumption frame entail this
  equation?" — is answered by `closure_decide`. The frame's equalities are an
  equivalence relation (union-find plus congruence over the interned terms), and
  only substituting class representatives into a genuine identity yields a Yes.
  A frame equation is never a rewrite rule: the closure orients every equality
  towards a canonical representative chosen by a well-founded order (smaller
  size first, then term id), so the two directions of an equation cannot loop
  and no depth cut-off is needed. No is only returned with evidence — closed
  sides that differ, or a matching `Ne` fact.

This is also where "equality comes first" is implemented: before any new
structure enters the system, this channel must work.
"""

from cas.syntax import term as T
from cas.syntax.termpath import postorder
from cas.kernel.verdict import Reason, YES, NO, unknown
from cas.math.project import project, normalize as proj_normalize


def normal_form(ctx, t):
    """The domain normal form of a term or equation: on a projection hit, the
    domain normal form; otherwise the input unchanged.

    An equation is normalized as "the difference of the two sides is zero":
    `Eq(l, r) -> Eq(nf(l - r), 0)`. Reducing both sides to one canonical form
    and reducing their difference to zero are the same thing, and the latter
    avoids maintaining a separate equation-specific canonical form.
    """
    if T.is_eq(t):
        lhs, rhs = t.args
        hit = project(ctx, T.plus(lhs, T.neg(rhs)))
        if hit is not None:
            return T.eq(proj_normalize(hit), T.ZERO)
        return t
    hit = project(ctx, t)
    if hit is not None:
        return proj_normalize(hit)
    return t


def is_closed(t) -> bool:
    """Whether the term has no free variable (so a numeric / normal-form answer
    is a statement about values, not about a function)."""
    return not T.free_vars(t)


def identity_verdict(ctx, a, b):
    """Three-valued identity decision.

    Delegates to the assembled identity pipeline (`equivalent`): pointer and
    numeric equality, the domain normal-form zero test, then the registered
    identity stages. A projection that does not cover the difference is honestly
    `Unknown(FRAGMENT)` — never folded into False, because "cannot re-check" is
    not "different" and a checker must report it as undecided.
    """
    from cas.math.decide import equivalent
    return equivalent(ctx, a, b)


# ---------------------------------------------------------------------------
# The ledger equality closure: deciding equations relative to an assumption frame
# ---------------------------------------------------------------------------

# A resource budget on the term universe the closure inspects. Exceeding it is
# reported as Unknown(BUDGET) — a resource limit with an honest reason, never a
# semantic cut-off (there is no depth argument in this procedure at all).
_CLOSURE_TERM_BUDGET = 4000


class _Union:
    """Union-find over interned terms.

    A class representative is its member minimal under (node count, term id).
    That order is well founded, so replacing a member by its representative
    strictly shrinks the term and repeated replacement reaches a fixed point;
    it is also what makes the closure's orientation canonical instead of
    "whichever direction of the equation happens to be tried first".
    """

    def __init__(self):
        self._up = {}
        self._size = {}

    def add(self, t) -> None:
        if t._h not in self._up:
            self._up[t._h] = t
            self._size[t._h] = len(postorder(t))

    def find(self, t):
        self.add(t)
        path = []
        cur = t
        while self._up[cur._h] is not cur:
            path.append(cur)
            cur = self._up[cur._h]
        for p in path:
            self._up[p._h] = cur
        return cur

    def union(self, a, b) -> bool:
        ra, rb = self.find(a), self.find(b)
        if ra is rb:
            return False
        if (self._size[rb._h], rb._h) < (self._size[ra._h], ra._h):
            ra, rb = rb, ra
        self._up[rb._h] = ra
        self._size[ra._h] += self._size[rb._h]
        return True


def _congruence(uf, terms) -> None:
    """Merge terms whose head and argument classes agree, to a fixed point.

    Merging is monotone over a finite term set, so the loop terminates. This is
    what lets a frame equality be used under a context: `f(a) = b` makes
    `f(a) + 1` and `b + 1` class-equal through the congruence step.
    """
    changed = True
    while changed:
        changed = False
        sig = {}
        for t in terms:
            if not isinstance(t, T.Expr):
                continue
            key = (t.head._h, tuple(uf.find(a)._h for a in t.args))
            prev = sig.get(key)
            if prev is None:
                sig[key] = t
            elif uf.union(t, prev):
                changed = True


def _representative_rewrite(uf, terms, t):
    """Rewrite every class member to its class representative, to a fixed point.

    Representatives are class-minimal, so the rewrite is well founded and needs
    no depth argument. The pass bound is a defensive resource guard only (the
    size argument proves convergence); were it ever hit, the current, partially
    rewritten term is returned, which can only lose rewrites, never add an
    unsound one.
    """
    universe, seen, stack = [], set(), list(terms) + [t]
    while stack:
        u = stack.pop()
        if u._h in seen:
            continue
        seen.add(u._h)
        universe.append(u)
        r = uf.find(u)
        if r is not u and r._h not in seen:
            stack.append(r)
        if isinstance(u, T.Expr):
            stack.extend(u.args)
    val = {u._h: u for u in universe}
    for _ in range(len(universe) + 2):
        changed = False
        for u in universe:
            r = uf.find(u)
            if r is not u:
                new = val[r._h]
            elif isinstance(u, T.Expr):
                args = tuple(val[a._h] for a in u.args)
                new = (T.mk(u.head, args)
                       if any(x is not y for x, y in zip(args, u.args)) else u)
            else:
                new = u
            if new is not val[u._h]:
                val[u._h] = new
                changed = True
        if not changed:
            break
    return val[t._h]


def closure_decide(ctx, a, b, assumptions):
    """Decide `Eq(a, b)` relative to the frame's equalities.

    Returns a verdict, or None when this channel has no opinion (the caller's
    remaining channels then continue). Termination: union-find merging plus a
    congruence fixed point over a finite term universe, then a fixed-point
    rewrite towards class-minimal representatives. Assumptions are never
    rewrite rules and there is no depth argument: an equation is oriented once
    towards its representative, so it cannot be applied in both directions.

    A Yes comes from class equality or from a genuine identity after the
    representatives are substituted. A No needs evidence: closed substituted
    sides whose normal forms differ, or a matching `Ne` fact. Anything else is
    honestly undecided.
    """
    facts = [f for f in assumptions
             if isinstance(f, T.Expr) and f.head.name == "Eq"]
    if not facts:
        return None
    terms, seen, stack = [], set(), [a, b] + list(facts)
    while stack:
        t = stack.pop()
        if t._h in seen:
            continue
        seen.add(t._h)
        terms.append(t)
        if isinstance(t, T.Expr):
            stack.extend(t.args)
    if len(terms) > _CLOSURE_TERM_BUDGET:
        return unknown(Reason.BUDGET)
    uf = _Union()
    for f in facts:
        uf.union(f.args[0], f.args[1])
    _congruence(uf, terms)
    if uf.find(a) is uf.find(b):
        return YES
    na = _representative_rewrite(uf, terms, a)
    nb = _representative_rewrite(uf, terms, b)
    if na is not a or nb is not b:
        v = identity_verdict(ctx, na, nb)
        if v.is_yes():
            return YES
        if v.is_no() and is_closed(na) and is_closed(nb):
            return NO
    for f in assumptions:
        if isinstance(f, T.Expr) and f.head.name == "Ne":
            u, v = f.args
            if ((uf.find(u) is uf.find(a) and uf.find(v) is uf.find(b))
                    or (uf.find(u) is uf.find(b) and uf.find(v) is uf.find(a))):
                return NO
    return None
