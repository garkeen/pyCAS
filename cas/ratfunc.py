from fractions import Fraction as Fr

from cas.errors import PolyError
from cas.poly import Poly, ugcd
from cas import term as T
from cas.term import Expr, Int


class RatFunc:
    __slots__ = ("p", "q")

    def __init__(self, p, q):
        if p.vars != q.vars:
            raise PolyError("var mismatch")
        if q.is_zero():
            raise PolyError("zero denominator")
        if p.is_zero():
            self.p = Poly.zero(p.vars)
            self.q = Poly.one(p.vars)
            return
        g = ugcd(p, q)
        p2 = p.udivmod(g)[0] if not g.is_zero() else p
        q2 = q.udivmod(g)[0] if not g.is_zero() else q
        lc = q2.lc(q2.vars[0]) if q2.vars else Fr(1)
        self.p = p2.scalar(Fr(1) / lc)
        self.q = q2.scalar(Fr(1) / lc)

    @staticmethod
    def from_poly(p):
        return RatFunc(p, Poly.one(p.vars))

    @staticmethod
    def from_const(vars_, f):
        return RatFunc(Poly.const(vars_, f), Poly.one(vars_))

    @staticmethod
    def from_term(t, vars_):
        vars_ = tuple(T.S(v) if isinstance(v, str) else v for v in vars_)
        if isinstance(t, (T.Int, T.Rat)):
            return RatFunc.from_const(vars_, T.num_val(t))
        try:
            return RatFunc.from_poly(Poly.from_term(t, vars_))
        except PolyError:
            pass
        if isinstance(t, Expr):
            name = t.head.name
            if name == "Plus":
                acc = RatFunc.from_const(vars_, 0)
                for a in t.args:
                    acc = acc + RatFunc.from_term(a, vars_)
                return acc
            if name == "Times":
                acc = RatFunc.from_const(vars_, 1)
                for a in t.args:
                    acc = acc * RatFunc.from_term(a, vars_)
                return acc
            if name == "Power":
                b, e = t.args
                if isinstance(e, Int) and e.v < 0:
                    rb = RatFunc.from_term(b, vars_)
                    return RatFunc(rb.q, rb.p)
                if isinstance(e, Int) and e.v >= 0:
                    return RatFunc.from_term(b, vars_) ** e.v
        raise PolyError(f"not rational function: {t!r}")

    def __add__(self, o):
        return RatFunc(self.p * o.q + o.p * self.q, self.q * o.q)

    def __neg__(self):
        return RatFunc(-self.p, self.q)

    def __sub__(self, o):
        return self + (-o)

    def __mul__(self, o):
        return RatFunc(self.p * o.p, self.q * o.q)

    def __truediv__(self, o):
        return RatFunc(self.p * o.q, self.q * o.p)

    def __pow__(self, n):
        if n < 0:
            return RatFunc(self.q, self.p) ** (-n)
        base = RatFunc.from_poly(Poly.one(self.p.vars))
        for _ in range(n):
            base = base * self
        return base

    def to_term(self):
        if self.q.is_const() and self.q.const_val() == 1:
            return self.p.to_term()
        return T.times(self.p.to_term(), T.pw(self.q.to_term(), T.MONE))
