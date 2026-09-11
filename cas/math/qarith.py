"""Rational literal arithmetic: the first foundation of the number-field system.

Scope: exact arithmetic on *all-literal rational subtrees* only. It does not
collect like terms, does not touch symbolic powers and performs no
branch-breaking rewrite. Collecting x+x or x*x belongs to the polynomial
machine, which this layer never touches.

This is an explicit-call layer, not construction-time magic: interning keeps the
syntax layer purely syntactic, and consumers (the decision pipeline, verification
back-substitution, tactics) call `fold` when they need arithmetic meaning.

- fold: bottom-up folding of literal subtrees. Plus/Times extract numeric
  factors and absorb identity elements (+0, *1, *0); integer powers are computed
  exactly. Division by zero and 0^0 / 0^negative stay interned: undefinedness is
  decided by the domain gate, not guessed here.
- eval_exact: exact evaluation at the ring level, with an environment. It is the
  only arithmetic channel for back-substitution checks and the stress judge.
"""

from fractions import Fraction as Fr

from cas.syntax.term import Expr, Int, Sym, S, N
from cas.syntax import term as T


class EvalNumError(Exception):
    pass


_MAX_EXP = 4096          # literal power safety bound, against 2^(10^9)-scale blowup


def _flat(head, args):
    """Flatten same-head nesting before collecting numbers: unwrapping a single
    factor during child folding lets nested literals float up through the
    syntactic constructor, so collection must happen after flattening."""
    out = []
    for a in args:
        if isinstance(a, Expr) and a.head.name == head:
            out.extend(_flat(head, a.args))
        else:
            out.append(a)
    return out


def fold(t):
    """Rational literal folding. Returns the interned form in which every
    all-numeric subtree has been replaced by its exact value.

    Rules (all rational semiring identities, none branch-breaking):
      · Plus: numeric terms are summed into one; when the sum is 0 and
        non-numeric terms remain, the constant is absorbed;
      · Times: if any numeric factor is 0 the whole product is 0; numeric
        factors are multiplied together, and a product of 1 is absorbed when
        non-numeric factors remain;
      · Power: a literal base with an integer literal exponent is computed
        exactly (a zero base only allows a positive exponent; a negative
        exponent requires a nonzero base).

    Division does not exist syntactically (a/b is Power(a, -1) or a Rat), so no
    special case is needed.
    """
    if not isinstance(t, Expr):
        return t
    head = t.head.name

    if head == "Plus":
        args = _flat("Plus", [fold(a) for a in t.args])
        c = Fr(0)
        rest = []
        for a in args:
            if T.is_num(a):
                c += T.num_val(a)
            else:
                rest.append(a)
        if not rest:
            return N(c)
        if c != 0:
            rest.append(N(c))
        return rest[0] if len(rest) == 1 else T.mk(S("Plus"), tuple(rest))

    if head == "Times":
        args = _flat("Times", [fold(a) for a in t.args])
        c = Fr(1)
        rest = []
        for a in args:
            if T.is_num(a):
                c *= T.num_val(a)
                if c == 0:
                    return N(0)
            else:
                rest.append(a)
        if not rest:
            return N(c)
        if c != 1:
            rest.append(N(c))
        return rest[0] if len(rest) == 1 else T.mk(S("Times"), tuple(rest))

    args = [fold(a) for a in t.args]
    if head == "Power":
        b, e = args
        if isinstance(e, Int) and abs(e.v) <= _MAX_EXP:
            if e.v == 1:
                return b                      # b^1 = b is a monoid identity, universal
            if e.v == 0:
                return T.mk(t.head, (b, e))   # u^0: 0^0 is contentious, left to the domain layer
            if T.is_num(b):
                bv = T.num_val(b)
                if bv != 0:
                    return N(bv ** e.v if e.v > 0 else Fr(1) / (bv ** -e.v))
                if e.v > 0:
                    return N(0)
                return T.mk(t.head, (b, e))   # 0^negative is undefined, stays interned
        return T.mk(t.head, (b, e))

    return T.mk(t.head, tuple(args))


def eval_exact(t, env):
    """Exact rational evaluation at the ring level.

    env: {Sym: Fraction}. Anything beyond the ring layer (transcendental heads,
    constants, non-integer powers) raises EvalNumError, so the caller concludes
    the fragment is not covered instead of silently approximating.
    """
    if T.is_num(t):
        return T.num_val(t)
    if isinstance(t, Sym):
        if t in env:
            return env[t]
        raise EvalNumError(f"unbound symbol {t.name}")
    if isinstance(t, Expr):
        n = t.head.name
        if n == "Plus":
            acc = Fr(0)
            for a in t.args:
                acc += eval_exact(a, env)
            return acc
        if n == "Times":
            acc = Fr(1)
            for a in t.args:
                acc *= eval_exact(a, env)
            return acc
        if n == "Power":
            b, e = t.args
            bv = eval_exact(b, env)
            if isinstance(e, Int):
                if e.v >= 0:
                    return bv ** e.v
                if bv == 0:
                    raise EvalNumError("zero to negative power")
                return Fr(1) / (bv ** (-e.v))
            ev = eval_exact(e, env)
            if ev.denominator == 1:
                v = ev.numerator
                if abs(v) <= _MAX_EXP:
                    if v >= 0:
                        return bv ** v
                    if bv != 0:
                        return Fr(1) / (bv ** (-v))
            raise EvalNumError("non-integer power not exact")
    raise EvalNumError(f"not exactly evaluable: {t!r}")
