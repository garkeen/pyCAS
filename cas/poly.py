from fractions import Fraction as Fr

from cas import term as T
from cas.term import Expr, Int, Rat, Sym, S, N
from cas.errors import PolyError


class Poly:
    __slots__ = ("vars", "monos")

    def __init__(self, vars_, monos):
        self.vars = tuple(vars_)
        self.monos = {k: v for k, v in monos.items() if v != 0}
        if not self.monos:
            self.monos = {}

    @staticmethod
    def zero(vars_):
        return Poly(vars_, {})

    @staticmethod
    def one(vars_):
        return Poly.const(vars_, Fr(1))

    @staticmethod
    def const(vars_, f):
        if isinstance(f, int):
            f = Fr(f)
        return Poly(vars_, {(0,) * len(tuple(vars_)): f})

    @staticmethod
    def mono(vars_, var, e):
        vars_ = tuple(vars_)
        idx = None
        for i, v in enumerate(vars_):
            if v is var:
                idx = i
                break
        if idx is None:
            raise PolyError(f"unknown var {var.name}")
        return Poly(vars_, {tuple(e if i == idx else 0 for i in range(len(vars_))): Fr(1)})

    @classmethod
    def from_term(cls, t, vars_):
        vars_ = tuple(T.S(v) if isinstance(v, str) else v for v in vars_)
        return cls._build(t, vars_)

    @classmethod
    def _build(cls, t, vars_):
        if T.is_num(t):
            return Poly.const(vars_, T.num_val(t))
        if isinstance(t, Sym):
            for v in vars_:
                if t is v:
                    return Poly.mono(vars_, t, 1)
            raise PolyError(f"free symbol {t.name}")
        if isinstance(t, Expr):
            name = t.head.name
            if name == "Plus":
                acc = Poly.zero(vars_)
                for a in t.args:
                    acc = acc + cls._build(a, vars_)
                return acc
            if name == "Times":
                acc = Poly.one(vars_)
                for a in t.args:
                    acc = acc * cls._build(a, vars_)
                return acc
            if name == "Power":
                b, e = t.args
                if isinstance(e, Int) and e.v >= 0:
                    return cls._build(b, vars_) ** e.v
                raise PolyError("non-integer power")
            if name in ("Neg",):
                return cls._build(t.args[0], vars_) * Poly.const(vars_, -1)
        raise PolyError(f"not polynomial: {t!r}")

    def to_term(self):
        if not self.monos:
            return T.ZERO
        out = []
        for exps in sorted(self.monos, reverse=True):
            c = self.monos[exps]
            facs = []
            for v, e in zip(self.vars, exps):
                if e == 1:
                    facs.append(v)
                elif e != 0:
                    facs.append(T.mk(S("Power"), (v, N(e))))
            if c != 1 or not facs:
                facs.append(N(c))
            if len(facs) == 1:
                out.append(facs[0])
            else:
                out.append(T.mk(S("Times"), tuple(facs)))
        if len(out) == 1:
            return out[0]
        return T.mk(S("Plus"), tuple(out))

    def is_zero(self):
        return not self.monos

    def is_const(self):
        return not self.monos or all(
            all(e == 0 for e in k) for k in self.monos
        )

    def const_val(self):
        for k, v in self.monos.items():
            if all(e == 0 for e in k):
                return v
        return Fr(0)

    def _same_vars(self, o):
        if self.vars != o.vars:
            raise PolyError("var mismatch")

    def __add__(self, o):
        self._same_vars(o)
        m = dict(self.monos)
        for k, v in o.monos.items():
            m[k] = m.get(k, Fr(0)) + v
        return Poly(self.vars, m)

    def __neg__(self):
        return Poly(self.vars, {k: -v for k, v in self.monos.items()})

    def __sub__(self, o):
        return self + (-o)

    def __mul__(self, o):
        self._same_vars(o)
        m = {}
        for k1, v1 in self.monos.items():
            for k2, v2 in o.monos.items():
                k = tuple(a + b for a, b in zip(k1, k2))
                m[k] = m.get(k, Fr(0)) + v1 * v2
        return Poly(self.vars, m)

    def __pow__(self, n):
        if n < 0:
            raise PolyError("negative power")
        acc = Poly.one(self.vars)
        for _ in range(n):
            acc = acc * self
        return acc

    def scalar(self, f):
        return Poly(self.vars, {k: v * f for k, v in self.monos.items()})

    def _var_idx(self, var):
        for i, v in enumerate(self.vars):
            if v is var:
                return i
        raise PolyError(f"unknown var {getattr(var, 'name', var)!r}")

    def deriv(self, var):
        idx = self._var_idx(var)
        m = {}
        for k, v in self.monos.items():
            e = k[idx]
            if e > 0:
                nk = tuple(a - (1 if i == idx else 0) for i, a in enumerate(k))
                m[nk] = m.get(nk, Fr(0)) + v * e
        return Poly(self.vars, m)

    def degree(self, var=None):
        if var is None:
            return max(
                (sum(k) for k in self.monos), default=-1
            )
        idx = self._var_idx(var)
        return max((k[idx] for k in self.monos), default=-1)

    def content(self):
        if not self.monos:
            return Fr(0)
        from math import gcd

        num = 0
        den = 1
        for v in self.monos.values():
            num = gcd(num, abs(v.numerator))
            den = den * v.denominator // gcd(den, v.denominator)
        return Fr(num, den)

    def primitive(self):
        c = self.content()
        if c == 0:
            return Fr(0), Poly.zero(self.vars)
        return c, self.scalar(Fr(1) / c)

    def udivmod(self, o):
        if len(self.vars) != 1:
            raise PolyError("univariate only")
        if o.is_zero():
            raise PolyError("division by zero")
        x = self.vars[0]
        q = Poly.zero(self.vars)
        r = Poly(self.vars, dict(self.monos))
        while not r.is_zero() and r.degree(x) >= o.degree(x):
            m = Poly(self.vars, {(r.degree(x) - o.degree(x),): r.lc(x) / o.lc(x)})
            q = q + m
            r = r - m * o
        return q, r

    def lc(self, var):
        idx = self.vars.index(var)
        best = None
        bl = -1
        for k, v in self.monos.items():
            if k[idx] > bl:
                bl = k[idx]
                best = v
        return best if best is not None else Fr(0)

    def is_monic(self, var=None):
        return self.lc(var if var else self.vars[0]) == 1

    def __str__(self):
        from cas.pprint import to_str

        return to_str(self.to_term())


def ugcd(a, b):
    if a.vars != b.vars or len(a.vars) != 1:
        raise PolyError("univariate only")
    A, B = a, b
    if A.is_zero() and B.is_zero():
        return Poly.zero(a.vars)
    if A.is_zero():
        return B.scalar(Fr(1) / B.lc(B.vars[0]))
    if B.is_zero():
        return A.scalar(Fr(1) / A.lc(A.vars[0]))
    _, pa = A.primitive()
    _, pb = B.primitive()
    while not pb.is_zero():
        _, r = pa.udivmod(pb)
        pa, pb = pb, r
    c, prim = pa.primitive()
    return prim.scalar(Fr(1) / prim.lc(prim.vars[0]))


def uresultant(a, b):
    if a.vars != b.vars or len(a.vars) != 1:
        raise PolyError("univariate only")
    x = a.vars[0]
    m, n = a.degree(x), b.degree(x)
    if m < 0 or n < 0:
        return Fr(0)
    if m == 0 and n == 0:
        return Fr(1)
    if m == 0:
        return a.lc(x) ** n
    if n == 0:
        return b.lc(x) ** m
    ca = [Fr(0)] * (m + 1)
    for k, v in a.monos.items():
        ca[m - k[0]] = v
    cb = [Fr(0)] * (n + 1)
    for k, v in b.monos.items():
        cb[n - k[0]] = v
    mat = []
    for i in range(n):
        row = [Fr(0)] * (m + n)
        for j, v in enumerate(ca):
            row[i + j] = v
        mat.append(row)
    for i in range(m):
        row = [Fr(0)] * (m + n)
        for j, v in enumerate(cb):
            row[i + j] = v
        mat.append(row)
    size = m + n
    det = Fr(1)
    for col in range(size):
        piv = None
        for r in range(col, size):
            if mat[r][col] != 0:
                piv = r
                break
        if piv is None:
            return Fr(0)
        if piv != col:
            mat[col], mat[piv] = mat[piv], mat[col]
            det = -det
        pv = mat[col][col]
        det *= pv
        for r in range(col + 1, size):
            f = mat[r][col] / pv
            if f == 0:
                continue
            row = mat[r]
            brow = mat[col]
            for c in range(col, size):
                row[c] -= f * brow[c]
    return det


def udiscriminant(a):
    if len(a.vars) != 1:
        raise PolyError("univariate only")
    x = a.vars[0]
    n = a.degree(x)
    if n <= 0:
        return Fr(1)
    r = uresultant(a, a.deriv(x))
    if (n * (n - 1) // 2) % 2 == 1:
        r = -r
    return r / a.lc(x)
