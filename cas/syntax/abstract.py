"""Subterm abstraction: replace *maximal* subterms satisfying a predicate with
fresh symbols, reducing a complex subexpression to an algebraically
independent atom:

    sin(x)^2 + sin(x)   --abstract(is_Sin)-->   _u0^2 + _u0

Equal subterms map to the same symbol (by interned pointer identity), which is
what makes polynomialization possible; `thaw` restores the original terms.

Uses: cyclic integration equations, treating `sin(x)` as an algebraic unknown,
treating `y'(x)` as an equation unknown, matrix expression equations, and
polynomializing special-function expressions.

This is syntax abstraction only. Whether treating a frozen term as an
algebraically independent atom is sound is decided by the mathematical
algorithm and checker that use it; this module makes no mathematical judgment.

Subterms inside a binder body are not abstracted: a de Bruijn index is only
meaningful inside its original binding scope, so freezing a body subterm out of
that scope would let `#i` escape. The walk therefore does not descend into a
Bound body, and a Bound as a whole never matches.
"""

from dataclasses import dataclass

from cas.syntax import term as T


@dataclass(frozen=True, slots=True)
class Abstraction:
    """Abstraction result: the new term plus a (symbol, original) table whose
    order is the environment `thaw` expects."""
    term: T.Term
    replacements: tuple

    def thaw(self, t=None):
        """Restore using this abstraction's environment (defaults to the
        abstraction result itself)."""
        return thaw(self.term if t is None else t, self.replacements)


def abstract_subterms(t, predicate, prefix="_u"):
    """Replace every maximal subterm satisfying `predicate` with a fresh symbol.

    · maximal: once a subterm matches, the walk does not descend into it, so
      when `sin(x)` matches, `x` is not abstracted separately;
    · shared: equal subterms (interned pointer identity) share one symbol;
    · fresh: new symbol names avoid every free variable of `t`.
    """
    used = {s.name for s in T.free_vars(t)}
    reps = []
    seen = {}
    counter = [0]

    def fresh():
        while True:
            name = f"{prefix}{counter[0]}"
            counter[0] += 1
            if name not in used:
                used.add(name)
                return T.S(name)

    def walk(u):
        if predicate(u):
            sym = seen.get(u)
            if sym is None:
                sym = fresh()
                seen[u] = sym
                reps.append((sym, u))
            return sym
        if isinstance(u, T.Expr):
            args = tuple(walk(a) for a in u.args)
            if all(a is b for a, b in zip(args, u.args)):
                return u
            return T.mk(u.head, args)
        return u

    return Abstraction(term=walk(t), replacements=tuple(reps))


def thaw(t, environment):
    """Replace abstraction symbols back with their original terms, the inverse
    of `abstract_subterms`.

    The environment is a tuple of (Symbol, Term) pairs. Substitution rebuilds
    through the AC-normalizing constructor, so `thaw(abstract(x)) is x` holds
    only when the original term was already canonical; for equality use the
    domain layer rather than pointer identity.
    """
    if not environment:
        return t
    return T.subst(t, dict(environment))
