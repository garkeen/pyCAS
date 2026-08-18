from cas import term as T
from cas.term import S, N, Expr, Sym, Int, plus, times, pw, neg, cos, sin, tan, exp, log, ONE, MONE, TWO

_TABLE = {
    "Sin": lambda a: cos(a),
    "Cos": lambda a: neg(sin(a)),
    "Tan": lambda a: plus(ONE, pw(tan(a), TWO)),
    "Exp": lambda a: exp(a),
    "Log": lambda a: pw(a, MONE),
    "ArcTan": lambda a: T.div(ONE, plus(ONE, pw(a, TWO))),
    "ArcSin": lambda a: T.div(ONE, T.sqrt(plus(neg(ONE), pw(a, TWO)))),
    "Sqrt": lambda a: T.div(times(N(T.Fraction(1, 2)), T.sqrt(a)), ONE),
}


def d(t, x):
    if isinstance(t, Sym):
        return T.ONE if t is x else T.ZERO
    if T.is_num(t) or isinstance(t, (T.Const, T.Special, T.DB, T.BVal, T.PatVar, T.PatSeq)):
        return T.ZERO
    if isinstance(t, T.Bound):
        return T.mk(S("D"), (t, x))
    name = t.head.name
    if name == "Plus":
        return plus(*[d(a, x) for a in t.args])
    if name == "Times":
        parts = []
        for i, a in enumerate(t.args):
            rest = tuple(b for j, b in enumerate(t.args) if j != i)
            parts.append(times(d(a, x), *rest))
        return plus(*parts)
    if name == "Power":
        b, e = t.args
        if isinstance(e, Int):
            if e.v == 0:
                return T.ZERO
            return times(e, pw(b, N(e.v - 1)), d(b, x))
        return times(t, plus(times(d(e, x), T.fn("Log")(b)), T.div(times(e, d(b, x)), b)))
    if name == "Quote":
        return T.mk(S("D"), (t, x))
    if name in _TABLE:
        (a,) = t.args
        return times(_TABLE[name](a), d(a, x))
    return T.mk(S("D"), (t, x))


def verify(F, x, f, budget=100000):
    from cas.decide import equivalent, T3

    r = equivalent(d(F, x), f, budget=budget)
    if r is T3.YES:
        return "VERIFIED"
    if r is T3.NO:
        return "FAILED"
    return "UNVERIFIED"
