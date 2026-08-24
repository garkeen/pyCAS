from fractions import Fraction as Fr

from cas.errors import PolyError
from cas.poly import Poly, ugcd, mgcd, div_exact, SymRat
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
        # N1 根治：ugcd/mgcd 已域泛化（原始 PRS 路径，叶类型无关）——
        # 无条件约分。旧版按 all_fr 跳过（"content 算术无定义"系过期
        # 认知：域上无 content 概念，欧几里得+首一化即完备）
        if len(p.vars) == 1:
            g = ugcd(p, q)
            p2 = p.udivmod(g)[0] if not g.is_zero() else p
            q2 = q.udivmod(g)[0] if not g.is_zero() else q
        else:
            g = mgcd(p, q)
            if not g.is_zero() and not g.is_const():
                p2, q2 = div_exact(p, g), div_exact(q, g)
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

    def __eq__(self, o):
        if not isinstance(o, RatFunc):
            return NotImplemented
        if self.p.vars != o.p.vars:
            from cas.poly import _extend
            vs = self.p.vars + tuple(v for v in o.p.vars
                                     if v not in self.p.vars)
            a, b = _extend(self.p, vs), _extend(self.q, vs)
            c, d = _extend(o.p, vs), _extend(o.q, vs)
        else:
            a, b, c, d = self.p, self.q, o.p, o.q
        if a == c and b == d:
            return True
        # 规范形不同时交叉相乘精确判零（域系数，构造器已约分）
        return RatFunc(a * d - c * b, b * d).is_zero()

    def __hash__(self):
        return hash((self.p, self.q))

    def __add__(self, o):
        return RatFunc(self.p * o.q + o.p * self.q, self.q * o.q)

    def __neg__(self):
        return RatFunc(-self.p, self.q)

    def __sub__(self, o):
        return self + (-o)

    def __mul__(self, o):
        if isinstance(o, (int, Fr)):
            return RatFunc(self.p.scalar(Fr(o)), self.q)
        # M5.4 审计扩容：ℚ(params,α) 标量残数（SymRat/Ga 叶）——
        # 域泛化算术经 Poly.scalar 直接消化
        if isinstance(o, SymRat) or hasattr(o, "norm"):
            return RatFunc(self.p.scalar(o), self.q)
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
