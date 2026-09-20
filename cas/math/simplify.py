from cas.syntax import term as T
from cas.syntax.term import Expr
from cas.errors import BudgetExceeded
from cas.syntax.termpath import postorder

# Memoization by term id: an interned term is immutable and content-addressed,
# so a rebuild result cached by _h stays valid forever. A long session would grow
# this without bound, so a cap is enforced: when the cache fills it is cleared
# wholesale (rebuild is deterministic and idempotent, so a cleared entry is
# rebuilt identically on the next miss). This is the eviction policy required of
# every computation cache; the term intern tables themselves are the hash-consing
# store and bounding them is a separate design question.
_MEMO = {}
_MEMO_CAP = 1 << 16


def cost(t):
    """Total node count (uniform cost, explicit-stack postorder). A well-founded
    natural number, used as the cost-decrease criterion."""
    n = 0
    for _u in postorder(t):
        n += 1
    return n


def rebuild(t, budget=100000):
    """Rebuild bottom-up, re-interning each level through the constructor `mk`.

    **This function does not simplify**, and its name says so: it only
    re-interns. `mk` performs representation normalization (AC flattening and
    sorting, idempotent dedupe, identity absorption) and no ring-level algebraic
    normal form, because a term is pure syntax and construction decides no
    semantics. For an already interned term, rebuilding and re-interning yields
    the same node, so this is the identity on ordinary input; its only purpose is
    to re-intern along the parent chain after a child was replaced. The budget
    counts nodes and raises BudgetExceeded when exceeded. Results are memoized by
    term id, which is permanent because terms are immutable.

    Real simplification is `autosimplify`, which iterates declared rules; the
    algebraic normal form belongs to the function-structure layer.
    """
    hit = _MEMO.get(t._h)
    if hit is not None:
        return hit
    spent = budget

    def rebuild_node(root):
        nonlocal spent
        val = {}
        for u in reversed(postorder(root)):
            spent -= 1
            if spent < 0:
                raise BudgetExceeded()
            if u in val:
                continue
            if isinstance(u, Expr):
                args = tuple(val[a] for a in u.args)
                val[u] = T.mk(u.head, args)
            elif isinstance(u, T.Bound):
                # Rebuilding an abstracted body must not call mk_bound again,
                # because _abstract would shift existing DB references.
                val[u] = T.mk_bound_canon(u.hint, val[u.body])
            else:
                val[u] = u
        return val[root]

    # Fixed-point iteration: the constructor is idempotent on already normalized
    # arguments, so this converges in at most two rounds. The loop condition is
    # the true fixed-point test, with no round-count magic.
    prev = t
    while True:
        nxt = rebuild_node(prev)
        if nxt is prev:
            if len(_MEMO) >= _MEMO_CAP:
                _MEMO.clear()
            _MEMO[t._h] = prev
            return prev
        prev = nxt


def autosimplify(ctx, t, budget=100000):
    """Automatic simplification: re-intern, then iterate the declared auto rules
    to a fixed point. The declared rules arrive through the explicit context.

    Discipline:
    · only auto rules with no guard are applied. Evaluating a guard would call
      back into the decision pipeline, which itself consumes this function, so a
      guarded auto rule would form a cycle; guarded rules go through the
      interactive channel instead.
    · every accepted step must strictly decrease the cost, so termination is
      guaranteed by well-foundedness rather than by a round limit.
    · at each path the candidate rules are narrowed by the subterm's root key:
      a rule that cannot match there is skipped without a match attempt, which
      changes the scan cost only.
    """
    from cas.math.rules import declared_ruleset, apply_rule

    rs = declared_ruleset(ctx)
    auto_ids = {r.id for r in rs.rules.values() if r.auto and r.guard is None}
    cur = rebuild(t, budget)
    # Termination: every accepted rule strictly decreases the cost, a
    # well-founded natural number, so a fixed point is reached with no round cap.
    while True:
        base = cost(cur)
        nxt = None
        for path in T.all_paths(cur):
            sub = T.term_at(cur, path)
            cands = [r for r in rs.candidates(sub) if r.id in auto_ids]
            for rule in sorted(cands, key=lambda r: r.priority):
                res = apply_rule(rule, cur, path, budget=budget)
                if res.ok and cost(res.term) < base:
                    nxt = res.term
                    break
            if nxt is not None:
                break
        if nxt is None:
            return cur
        cur = rebuild(nxt, budget)
