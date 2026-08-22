from fractions import Fraction as Fr

from cas.errors import PolyError
from cas.poly import Poly, ugcd, mgcd, div_exact
from cas import term as T
from cas.term import Expr, Int


def _iter_leaf_coefs(p):
    """Poly 的全部叶系数（多变量递归视图）。"""
    if not p.monos:
        return
    if len(p.vars) <= 1:
        for v in p.monos.values():
            yield v
        return
    from cas.poly import _rec_view
    for sub in _rec_view(p).values():
        yield from _iter_leaf_coefs(sub)


def _coef_inv(c):
    """系数域求逆（Fr / Ga / duck-typed）。"""
    if isinstance(c, Fr):
        return Fr(1) / c
    if hasattr(c, "norm"):
        from cas.gaussian import Ga
        return Ga.one() / c
    return 1 / c


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
        if len(p.vars) == 1:
            g = ugcd(p, q)
            p2 = p.udivmod(g)[0] if not g.is_zero() else p
            q2 = q.udivmod(g)[0] if not g.is_zero() else q
        else:
            # 多变量：mgcd + 精确除法；域系数（Ga 等）时 content/符号
            # 规范无定义——跳过 gcd 约化（分数不约，正确性不受影响，
            # 下游 Hermite/residue 各自正规约化）
            all_fr = all(isinstance(v, Fr)
                         for sub in _iter_leaf_coefs(p) for v in [sub]) \
                and all(isinstance(v, Fr)
                        for sub in _iter_leaf_coefs(q) for v in [sub])
            if all_fr:
                g = mgcd(p, q)
                if not g.is_zero() and not g.is_const():
                    p2, q2 = div_exact(p, g), div_exact(q, g)
                else:
                    p2, q2 = p, q
            else:
                p2, q2 = p, q
        lc = q2.lc(q2.vars[0]) if q2.vars else Fr(1)
        inv = _coef_inv(lc)
        self.p = p2.scalar(inv)
        self.q = q2.scalar(inv)

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
        if isinstance(o, (int, Fr)):
            return RatFunc(self.p.scalar(Fr(o)), self.q)
        return RatFunc(self.p * o.p, self.q * o.q)

    def __rmul__(self, o):
        return self * o

    def __truediv__(self, o):
        return RatFunc(self.p * o.q, self.q * o.p)

    def __pow__(self, n):
        if n < 0:
            return RatFunc(self.q, self.p) ** (-n)
        base = RatFunc.from_poly(Poly.one(self.p.vars))
        for _ in range(n):
            base = base * self
        return base

    def deriv(self, x):
        return RatFunc(self.p.deriv(x) * self.q - self.p * self.q.deriv(x),
                       self.q * self.q)

    def is_zero(self):
        return self.p.is_zero()

    def is_const(self):
        return self.p.is_const() and self.q.is_const()

    def const_val(self):
        return self.p.const_val() / self.q.const_val()

    @staticmethod
    def zero(vars_):
        return RatFunc(Poly.zero(vars_), Poly.one(vars_))

    @staticmethod
    def one(vars_):
        return RatFunc(Poly.one(vars_), Poly.one(vars_))

    def to_term(self):
        if self.q.is_const() and self.q.const_val() == 1:
            return self.p.to_term()
        return T.times(self.p.to_term(), T.pw(self.q.to_term(), T.MONE))
