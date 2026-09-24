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

from collections.abc import Iterable, Mapping
from fractions import Fraction

from cas.syntax import term as T
from cas.syntax.term import Expr, Int, N, S, Sym, Term


class EvalNumError(Exception):
    pass


_MAX_EXP = 4096          # literal power safety bound, against 2^(10^9)-scale blowup


def _flat(head: str, args: Iterable[Term]) -> list[Term]:
    """Flatten same-head nesting before collecting numbers: unwrapping a single
    factor during child folding lets nested literals float up through the
    syntactic constructor, so collection must happen after flattening."""
    out: list[Term] = []
    for argument in args:
        if isinstance(argument, Expr) and argument.head.name == head:
            out.extend(_flat(head, argument.args))
        else:
            out.append(argument)
    return out


def fold(t: Term) -> Term:
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
        plus_args = _flat("Plus", [fold(argument) for argument in t.args])
        total = Fraction(0)
        plus_rest: list[Term] = []
        for argument in plus_args:
            if T.is_num(argument):
                total += T.num_val(argument)
            else:
                plus_rest.append(argument)
        if not plus_rest:
            return N(total)
        if total != 0:
            plus_rest.append(N(total))
        return plus_rest[0] if len(plus_rest) == 1 else T.mk(
            S("Plus"), tuple(plus_rest)
        )

    if head == "Times":
        times_args = _flat("Times", [fold(argument) for argument in t.args])
        product = Fraction(1)
        times_rest: list[Term] = []
        for argument in times_args:
            if T.is_num(argument):
                product *= T.num_val(argument)
                if product == 0:
                    return N(0)
            else:
                times_rest.append(argument)
        if not times_rest:
            return N(product)
        if product != 1:
            times_rest.append(N(product))
        return times_rest[0] if len(times_rest) == 1 else T.mk(
            S("Times"), tuple(times_rest)
        )

    args: list[Term] = [fold(a) for a in t.args]
    if head == "Power":
        b, e = args
        if isinstance(e, Int) and abs(e.v) <= _MAX_EXP:
            if e.v == 1:
                return b                      # b^1 = b is a monoid identity, universal
            if e.v == 0:
                # 0^0 is contentious and stays interned for the domain layer to
                # refuse; a nonzero numeric base to the zero is 1, so the
                # member/normalize/equal trio of the constant domains agrees
                # (eval_exact already computes c^0 = 1 for c != 0). A symbolic
                # base is not an all-numeric subtree, so it is left to the
                # polynomial domain.
                if T.is_num(b) and T.num_val(b) != 0:
                    return T.ONE
                return T.mk(t.head, (b, e))
            if T.is_num(b):
                bv = T.num_val(b)
                if bv != 0:
                    return N(
                        bv ** e.v
                        if e.v > 0
                        else Fraction(1) / (bv ** -e.v)
                    )
                if e.v > 0:
                    return N(0)
                return T.mk(t.head, (b, e))
        return T.mk(t.head, (b, e))

    return T.mk(t.head, tuple(args))


def eval_exact(t: Term, env: Mapping[Sym, Fraction]) -> Fraction:
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
        name = t.head.name
        if name == "Plus":
            accumulator = Fraction(0)
            for argument in t.args:
                accumulator += eval_exact(argument, env)
            return accumulator
        if name == "Times":
            accumulator = Fraction(1)
            for argument in t.args:
                accumulator *= eval_exact(argument, env)
            return accumulator
        if name == "Power":
            base, exponent = t.args
            base_value = eval_exact(base, env)
            if isinstance(exponent, Int):
                if exponent.v == 0:
                    if base_value == 0:
                        raise EvalNumError("zero to the zero is undefined")
                    return Fraction(1)
                if exponent.v > 0:
                    return base_value ** exponent.v
                if base_value == 0:
                    raise EvalNumError("zero to negative power")
                return Fraction(1) / (base_value ** (-exponent.v))
            exponent_value = eval_exact(exponent, env)
            if exponent_value.denominator == 1:
                integer_exponent = exponent_value.numerator
                if abs(integer_exponent) <= _MAX_EXP:
                    if integer_exponent >= 0:
                        return base_value ** integer_exponent
                    if base_value != 0:
                        return Fraction(1) / (base_value ** (-integer_exponent))
            raise EvalNumError("non-integer power not exact")
    raise EvalNumError(f"not exactly evaluable: {t!r}")
