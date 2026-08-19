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


# ---------------------------------------------------------------------------
# 多元 gcd 与精确除法（递归视角：主变量单变量，系数 = 其余变量的多项式）
# 算法：原始伪除余序列（primitive PRS）；content 递归计算。
# ---------------------------------------------------------------------------


def _rec_view(p):
    """Poly(vars) -> {主变量指数: Poly(vars[1:])}（单变量时系数为 Poly((), {(): Fr})）。"""
    if p.is_zero():
        return {}
    out = {}
    for exps, v in p.monos.items():
        e0, rest = exps[0], exps[1:]
        sub = out.get(e0)
        if sub is None:
            out[e0] = Poly(p.vars[1:], {rest: v})
        else:
            sub.monos[rest] = v
    return out


def _from_rec(d, vars_):
    m = {}
    for e0, sub in d.items():
        for rest, v in sub.monos.items():
            m[(e0,) + rest] = v
    return Poly(vars_, m)


def _rat_gcd_frac(a, b):
    """有理数 gcd：gcd(分子)/lcm(分母)，取正。"""
    from math import gcd as _igcd

    if a == 0:
        return abs(b)
    if b == 0:
        return abs(a)
    n = _igcd(abs(a.numerator), abs(b.numerator))
    d = a.denominator * b.denominator // _igcd(a.denominator, b.denominator)
    return Fr(n, d)


def _sign_normalize(p):
    """首项系数取正（规范符号，使 gcd 唯一到符号）。"""
    if p.is_zero():
        return p
    if not p.vars:
        v = p.const_val()
        return p if v > 0 else p.scalar(Fr(-1))
    d = _rec_view(p)
    lc = d[max(d)]
    if lc.vars:
        dd = _rec_view(lc)
        sgn = dd[max(dd)].const_val()
    else:
        sgn = lc.const_val()
    return p if sgn > 0 else p.scalar(Fr(-1))


def _rat_content(p):
    """Fr 层 content：全体系数的有理数 gcd。"""
    c = Fr(0)
    for v in p.monos.values():
        c = _rat_gcd_frac(c, v)
    return c


def mgcd(a, b):
    """多元多项式 gcd（ℚ 上，任意变量数）。

    返回规范形（content 归一、符号规范化），约定 mgcd(0, b) = 规范化的 b。
    单变量基保留有理 content（ugcd 归一会丢，此处补回）。
    """
    if a.vars != b.vars:
        raise PolyError("var mismatch")
    vs = a.vars
    if a.is_zero():
        return _primitive_full(b)[1] if not b.is_zero() else Poly(vs, {})
    if b.is_zero():
        return _primitive_full(a)[1]
    if not vs:
        g = _rat_gcd_frac(a.const_val(), b.const_val())
        return Poly(vs, {(): g}) if g else Poly(vs, {})
    if len(vs) == 1:
        ra, rb = _rat_content(a), _rat_content(b)
        pa = Poly(vs, {k: v / ra for k, v in a.monos.items()})
        pb = Poly(vs, {k: v / rb for k, v in b.monos.items()})
        g = ugcd(pa, pb)
        gr = _rat_gcd_frac(ra, rb)
        return g.scalar(gr) if gr != 1 else g
    ca, pa = _primitive_full(a)
    cb, pb = _primitive_full(b)
    gc = mgcd(ca, cb)
    g = _prs_gcd(pa, pb)
    # content 在 vars[1:] 上，提升到全变量空间（不依赖主变量）再相乘；
    # 不再取原始部分——content gcd 本身就是结果的组成。
    gcl = Poly(vs, {(0,) + k: v for k, v in gc.monos.items()})
    return _sign_normalize(gcl * g)


def _primitive_full(p):
    """(content, 原始部分)：content = 系数 gcd（递归），主变量视角。"""
    vs = p.vars
    if p.is_zero():
        return Poly(vs[1:], {}), Poly(vs, {})
    if not vs:
        c = p.const_val()
        return Poly((), {(): c}), Poly((), {(): Fr(1)})
    coeffs = list(_rec_view(p).values())
    c = coeffs[0]
    for cc in coeffs[1:]:
        c = mgcd(c, cc)
    if c.is_zero() or (not c.vars and c.const_val() == 0):
        return Poly(vs[1:], {}), p
    prim = {}
    for e0, sub in _rec_view(p).items():
        prim[e0] = div_exact(sub, c)
    return c, _sign_normalize(_from_rec(prim, vs))


def _prem(A, B):
    """主变量伪除余数：lc(B)^δ 倍的 A mod B，系数只用 +,-,*。"""
    vs = A.vars
    n = max(_rec_view(B))
    lc = _rec_view(B)[n]
    R = dict(_rec_view(A))
    while R and max(R) >= n:
        m = max(R)
        t = R[m]
        # R <- lc*R - t*x^(m-n)*B
        scaled = {e: c * lc for e, c in R.items()}
        shifted = {e + (m - n): c * t for e, c in _rec_view(B).items()}
        merged = dict(scaled)
        for e, c in shifted.items():
            merged[e] = merged.get(e, Poly(vs[1:], {})) - c
        R = {e: c for e, c in merged.items() if not c.is_zero()}
    return _from_rec(R, vs)


def _prs_gcd(a, b):
    """原始伪除余序列 gcd（输入为主变量原始形）。"""
    da = max(_rec_view(a)) if not a.is_zero() else -1
    db = max(_rec_view(b)) if not b.is_zero() else -1
    if da < db:
        a, b = b, a
    r0, r1 = a, b
    while not r1.is_zero():
        r = _prem(r0, r1)
        if r.is_zero():
            break
        r0, r1 = r1, _primitive_full(r)[1]
    return _primitive_full(r1)[1]


def div_exact(A, B):
    """精确除法 A/B（要求 B 整除 A，否则抛 PolyError）。多元递归实现。

    原理：主变量伪除得 lc(B)^k·A = B·Q，整除时余数为 0，
    Q 的系数再递归精确除以 lc(B)^k（变量数递减，必终止）。
    """
    if A.vars != B.vars:
        raise PolyError("var mismatch")
    vs = A.vars
    if A.is_zero():
        return Poly(vs, {})
    if B.is_zero():
        raise PolyError("division by zero")
    if not vs:
        bv = B.const_val()
        if bv == 0:
            raise PolyError("division by zero")
        return Poly(vs, {(): A.const_val() / bv})
    n = max(_rec_view(B)) if not B.is_zero() else -1
    if n <= 0:
        # B 在主变量上是常数：逐系数递归除
        out = {}
        for e0, sub in _rec_view(A).items():
            out[e0] = div_exact(sub, _rec_const(B))
        return _from_rec(out, vs)
    lc = _rec_view(B)[n]
    R = dict(_rec_view(A))
    Q = {}
    k = 0
    while R and max(R) >= n:
        m = max(R)
        t = R[m]
        k += 1
        # Q <- lc*Q + t*x^(m-n)
        Q = {e: c * lc for e, c in Q.items()}
        Q[m - n] = Q.get(m - n, Poly(vs[1:], {})) + t
        # R <- lc*R - t*x^(m-n)*B
        scaled = {e: c * lc for e, c in R.items()}
        shifted = {e + (m - n): c * t for e, c in _rec_view(B).items()}
        merged = dict(scaled)
        for e, c in shifted.items():
            merged[e] = merged.get(e, Poly(vs[1:], {})) - c
        R = {e: c for e, c in merged.items() if not c.is_zero()}
    if R:
        raise PolyError("not exact division")
    lck = lc ** k
    out = {e0: div_exact(sub, lck) for e0, sub in Q.items()}
    return _from_rec(out, vs)


def _rec_const(B):
    """B 在主变量上为常数时，取其系数多项式（vars[1:]）。"""
    d = _rec_view(B)
    if list(d) != [0]:
        raise PolyError("not exact division")
    return d[0]
