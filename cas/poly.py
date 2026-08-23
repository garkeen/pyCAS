from fractions import Fraction as Fr

from cas import term as T
from cas.term import Expr, Int, Rat, Sym, Const, S, N
from cas.errors import PolyError

# 代数常数模注册表（M5.4b，SAE 语义对齐 FriCAS algext.spad）：
# 符号 -> monic 极小多项式（单变量 Poly，Fr 系数）。出现该变量的
# Poly 乘积自动做余式约简——保证零判定精确（未约简的 α²−2 叶会
# 让 is_zero 误判）。risch 侧在根式参数化时登记。
ALG_MODULI = {}


ALG_REDUCE_SUSPENDED = [False]


class alg_suspend:
    """挂起关系约简（作用域化域语义）：自由参数轨道的消费者
    （solve 参数路径等）在投影/求解期间声明"我在无关系语义下工作"，
    出口约简随之停用——半吊子语义的根治。"""

    def __enter__(self):
        ALG_REDUCE_SUSPENDED[0] = True
        return self

    def __exit__(self, *exc):
        ALG_REDUCE_SUSPENDED[0] = False
        return False


def _alg_reduce_out(p):
    """乘积出口：对含已登记代数变量的结果逐变量做模余式。"""
    if not ALG_MODULI or ALG_REDUCE_SUSPENDED[0]:
        return p
    mods = [(v, ALG_MODULI[v]) for v in p.vars if v in ALG_MODULI]
    if not mods:
        return p
    for v, m in mods:
        if p.is_zero():
            return p
        p = _reduce_alg_var(p, v, m)
    return p


def _reduce_alg_var(p, a, m):
    """p（多变量）中变量 a 模 monic 单变量多项式 m 的余式。

    按 a 的指数分桶（系数=其余变量上的 Poly），monic 首项消去法；
    系数环算术全走 Poly 反射通道，对混合叶（Ga 等）安全。
    """
    idx = p._var_idx(a)
    rest = tuple(vv for vv in p.vars if vv is not a)
    dm = max(kk[0] for kk in m.monos)
    md = {kk[0]: cc for kk, cc in m.monos.items()}
    cur = {}
    for k, c in p.monos.items():
        e = k[idx]
        ka = k[:idx] + k[idx + 1:]
        cp = Poly(rest, {ka: c})
        cur[e] = cur.get(e, Poly.zero(rest)) + cp
    while True:
        ks = [e for e, c in cur.items() if not c.is_zero()]
        if not ks:
            return Poly.zero(p.vars)
        top = max(ks)
        if top < dm:
            break
        shift = top - dm
        topc = cur.pop(top)
        nxt = dict(cur)
        for e, cc in md.items():
            if e == dm:
                continue          # monic：首项系数 1 已随 top 抵消
            te = e + shift
            prod = topc.scalar(cc)
            nxt[te] = nxt.get(te, Poly.zero(rest)) - prod
        cur = nxt
    out = {}
    for e, c in cur.items():
        for k, vv in c.monos.items():
            full = k[:idx] + (e,) + k[idx:]
            out[full] = vv
    return Poly(p.vars, out)


class Poly:
    __slots__ = ("vars", "monos")

    def __init__(self, vars_, monos):
        self.vars = tuple(vars_)
        self.monos = {k: v for k, v in monos.items() if v != 0}
        if not self.monos:
            self.monos = {}

    def __eq__(self, o):
        if not isinstance(o, Poly):
            return NotImplemented
        return self.vars == o.vars and self.monos == o.monos

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
            raise PolyError(f"unknown var {var!r}")
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
            if t.name == "i":
                # 保留名 i = 虚单位常量（ℚ(i)，M5.2.5/M5.3；用户若以
                # i 为参数符号则冲突——文档级保留，sympy I 同款取舍）
                from cas.gaussian import Ga
                return Poly.const(vars_, Ga(0, 1))
            # 不在 vars 的符号 = 参数：系数升入 ℚ(params)（SymRat 域）
            return Poly.const(vars_, _mk_param(t))
        if isinstance(t, Expr):
            # 复合项作原子变量（如 Log(x) 当生成元）：驻留 is 比较
            for v in vars_:
                if t is v:
                    return Poly.mono(vars_, t, 1)
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
        if isinstance(t, Const):
            # 命名常数查注册表（P5）：imaginary-unit 内建为域元素，
            # 其余诚实拒绝（参数化通道见 M5.6）
            from cas.spec import get_constant
            sp = get_constant(getattr(t, "name", ""))
            if sp is not None and sp.kind == "imaginary-unit":
                from cas.gaussian import Ga
                return Poly.const(vars_, Ga(0, 1))
            raise PolyError(f"not polynomial: {t!r}")
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
                facs.append(_coef_to_term(c))
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
        return _alg_reduce_out(Poly(self.vars, m))

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

        vs = list(self.monos.values())
        # 域系数（Ga/SymRat 等）：无 ℚ-content 概念，恒取单位元
        # （primitive 不改变多项式，对 gcd/cancel 正确性无损）
        for v in vs:
            nz = v.is_zero() if hasattr(v, "is_zero") else v != 0
            if not nz:
                return v / v
        num = 0
        den = 1
        for v in vs:
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


def is_param_poly(p):
    """系数域是否为 ℚ(params)（含 SymRat 系数）。"""
    return any(isinstance(v, SymRat) for v in p.monos.values())


def _monic(p):
    """首一化（域除法，Fr/SymRat 系数通用）。"""
    if p.is_zero():
        return p
    return p.scalar(_rat_inv(p.lc(p.vars[0])))


def ugcd(a, b):
    """域上单变量多项式 gcd（欧几里得，monic 规范）。

    ℚ 与 ℚ(params) 统一：系数域是域（SymRat 有理函数），无 content 概念，
    欧几里得 + 首一化即完备（原 ℚ 实现中的 primitive 清理仅控制数值膨胀）。
    """
    if a.vars != b.vars or len(a.vars) != 1:
        raise PolyError("univariate only")
    A, B = a, b
    if A.is_zero() and B.is_zero():
        return Poly.zero(a.vars)
    if A.is_zero():
        return _monic(B)
    if B.is_zero():
        return _monic(A)
    r0, r1 = A, B
    while not r1.is_zero():
        _, r = r0.udivmod(r1)
        r0, r1 = r1, r
    if r0.is_zero():
        return Poly.zero(a.vars)
    return _monic(r0)


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


def _has_nonsimple_leaf(p):
    """叶含非纯有理数（Ga/SymRat/混合）——需要域泛化 gcd。"""
    stack = [p]
    while stack:
        u = stack.pop()
        for c in getattr(u, "monos", {}).values():
            if isinstance(c, Fr):
                continue
            return True
    return False


def _fgcd(a, b):
    """域泛化多变量 gcd：系数环 = 前缀变量上的有理函数（RatFunc），
    主变量欧几里得 + 每步首一化。支持 ℚ(i)/参数/混合叶。

    返回 Poly（分母已用系数分母之积清除；不保证内容最简，但
    整除性 gcd|a、gcd|b 与唯一性（相差单位元）精确成立）。
    全程置于 RatFunc.raw_norm() 下——系数运算不做分式约分
    （约分会回调本函数，互递归；结果单位元差异不影响整除语义）。"""
    from cas.ratfunc import RatFunc

    with RatFunc.raw_norm():

        vs = a.vars
        assert vs == b.vars
        if not vs:
            # 常数：域元素 gcd 取单位元（非零时）
            return Poly.one(())
        main = vs[-1]
        rest = vs[:-1]

        def split_to_rf(t):
            """Poly(vs) -> {deg: RatFunc(rest)}，按主变量次数分桶。"""
            buckets = {}
            for k, c in t.monos.items():
                e = k[-1]
                kp = k[:-1]
                cp = Poly(rest, {kp: c})
                rf = RatFunc(cp, Poly.one(rest))
                buckets[e] = buckets.get(e, RatFunc.zero(rest)) + rf
            return buckets

        def rf_monic(buckets):
            """首一化：各系数除以首项系数——指数保持绝对位置不变。"""
            ks = [e for e, c in buckets.items() if not c.is_zero()]
            if not ks:
                return {}
            top = max(ks)
            inv = RatFunc.one(rest) / buckets[top]
            return {e: c * inv for e, c in buckets.items() if c}

        r0 = split_to_rf(a)
        r1 = split_to_rf(b)

        while any(not c.is_zero() for c in r1.values()):
            r1 = rf_monic(r1)
            if not r1:
                break
            q = {}
            r0n = {}
            top1 = max(r1)
            while True:
                ks = [e for e, c in r0.items() if not c.is_zero()]
                if not ks:
                    break
                top0 = max(ks)
                if top0 < top1:
                    break
                t = (top0 - top1, r0[top0])
                for e, c in r1.items():
                    te = e + t[0]
                    term = c * t[1]
                    r0n[te] = r0n.get(te, RatFunc.zero(rest)) - term
                for e, c in r0.items():
                    r0n[e] = r0n.get(e, RatFunc.zero(rest)) + c
                # 注：te=top0 的减式与旧首项在此相消（monic 首一化保证）
                r0 = {e: c for e, c in r0n.items() if not c.is_zero()}
                r0n = {}
            r0, r1 = r1, r0

        r0 = rf_monic(r0)
        if not r0:
            return Poly.zero(vs)

        # 清分母：各系数分母之积（非 lcm，可能有公共因子——单位元意义下无碍）
        dens = Poly.one(rest)
        for e, c in r0.items():
            dens = dens * c.q
        out = {}
        for e, c in r0.items():
            prod = c.p * dens
            for k, cc in prod.monos.items():
                full = k + (e,)
                out[full] = cc
        res = Poly(vs, out)
        # 单位元意义下返回（符号/常数因子不保证最简——整除性与零判定精确）
        return res


def _mgcd_generic(a, b):
    """mgcd 的域泛化分派入口：非纯 ℚ 叶走 _fgcd。"""
    if _has_nonsimple_leaf(a) or _has_nonsimple_leaf(b):
        g = _fgcd(a, b)
        return g
    return mgcd(a, b)


def mgcd(a, b):
    """多元多项式 gcd（ℚ 上，任意变量数）。

    返回规范形（content 归一、符号规范化），约定 mgcd(0, b) = 规范化的 b。
    单变量基保留有理 content（ugcd 归一会丢，此处补回）。
    """
    if a.vars != b.vars:
        raise PolyError("var mismatch")
    vs = a.vars
    if len(a.vars) == 1 and (_has_nonsimple_leaf(a) or _has_nonsimple_leaf(b)):
        return _fgcd(a, b)   # 单变量域泛化欧几里得（多变量待修：见 Step3 缺陷记录）
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
    if _has_nonsimple_leaf(a) or _has_nonsimple_leaf(b):
        return _fgcd(a, b)
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


# ---------------------------------------------------------------------------
# ℚ(params) 系数域：SymRat（参数有理函数）+ 与 Fr 的混合算术
# ---------------------------------------------------------------------------


class SymRat:
    """ℚ(params) 有理函数系数：num/den ∈ ℚ[params]（Fr 系数 Poly，约分规范）。

    常数（无参数）结果退化回 Fr，保持 Poly 其余代码对 Fr 的既有假设。
    """

    __slots__ = ("num", "den")

    def __init__(self, num, den):
        self.num = num
        self.den = den

    def __add__(self, o):
        return _rat_add(self, o)

    def __radd__(self, o):
        return _rat_add(o, self)

    def __sub__(self, o):
        return _rat_add(self, _rat_neg(o))

    def __rsub__(self, o):
        return _rat_add(o, _rat_neg(self))

    def __mul__(self, o):
        return _rat_mul(self, o)

    def __rmul__(self, o):
        return _rat_mul(o, self)

    def __truediv__(self, o):
        return _rat_mul(self, _rat_inv(o))

    def __rtruediv__(self, o):
        return _rat_mul(o, _rat_inv(self))

    def __neg__(self):
        return SymRat(self.num.scalar(Fr(-1)), self.den)

    def __eq__(self, o):
        if isinstance(o, SymRat):
            return self.num == o.num and self.den == o.den
        if isinstance(o, (int, Fr)):
            o = Fr(o)
            if o == 0:
                return self.num.is_zero()
            return (self.num.is_const() and self.den.is_const()
                    and self.num.const_val() / self.den.const_val() == o)
        return NotImplemented

    def is_zero(self):
        return self.num.is_zero()

    def to_term(self):
        return T.div(self.num.to_term(), self.den.to_term())


def _mk_param(sym):
    """参数符号 -> SymRat（分子=该参数，分母=1）。"""
    vs = (sym,)
    return SymRat(Poly(vs, {(1,): Fr(1)}), Poly.one(vs))


def _coef_to_term(c):
    """Fr/SymRat/Ga 系数 -> term。"""
    if isinstance(c, SymRat):
        return c.to_term()
    if hasattr(c, "to_term"):       # Ga（ℚ(i)）等自带出口的域元素
        return c.to_term()
    return N(c)


def _parts(x):
    if isinstance(x, SymRat):
        return x.num, x.den
    if isinstance(x, (Fr, int)):
        return Poly((), {(): Fr(x)}), Poly.one(())
    if hasattr(x, "norm"):
        # Ga（ℚ(i)）常量：升入混合参数多项式轨道（ℚ(i,params)，
        # M5.6#1）——叶系数 Ga 的 Poly 分式，_mk_rat 混合叶跳过规范化
        return Poly((), {(): x}), Poly.one(())
    # 其余（命名常数 Const 等）不在任何已支持系数域——诚实拒绝
    from cas.errors import PolyError
    raise PolyError(f"coefficient outside supported domains: {x!r}")


def _extend(p, vs):
    """Poly 扩展到超集变量空间（p.vars 每变量按名映射到 vs 中的索引）。"""
    if p.vars == vs:
        return p
    if not p.monos:
        return Poly.zero(vs)
    if not p.vars:
        return Poly(vs, {tuple(0 for _ in vs): p.const_val()})
    idx = [next(i for i, x in enumerate(vs) if x.name == v.name) for v in p.vars]
    m = {}
    for k, v in p.monos.items():
        full = [0] * len(vs)
        for i, e in zip(idx, k):
            full[i] = e
        m[tuple(full)] = v
    return Poly(vs, m)


def _unify_vs(p, q):
    if p.vars == q.vars:
        return p, q
    if not p.vars:
        return _extend(p, q.vars), q
    if not q.vars:
        return p, _extend(q, p.vars)
    vs = p.vars + tuple(v for v in q.vars if v not in p.vars)
    return _extend(p, vs), _extend(q, vs)


def _all_fr_leaves(p):
    """Poly 叶系数是否全为 ℚ（int/Fr）。"""
    for v in p.monos.values():
        if isinstance(v, (SymRat, Fr, int)):
            continue
        return False
    return True


def _mk_rat(num, den):
    """规范：约分 + 分母符号规范；常数退化回 Fr。

    ℚ(i,params) 混合叶（Ga×SymRat 轨道，M5.6#1 扩展）：content-gcd
    与符号规范无 ℚ-content 概念——跳过规范化（值恒等不受影响，
    is_zero/inv 仍精确；仅同值异形不保证 ==）。纯 ℚ 叶走既有规范。
    """
    num, den = _unify_vs(num, den)
    if num.is_zero():
        return Fr(0)
    if num.is_const() and den.is_const():
        return num.const_val() / den.const_val()
    if not (_all_fr_leaves(num) and _all_fr_leaves(den)):
        return SymRat(num, den)
    g = mgcd(num, den)
    if not g.is_zero() and not (g.is_const() and abs(g.const_val()) == 1):
        num = div_exact(num, g)
        den = div_exact(den, g)
    s = _sign_normalize(den)
    if s is not den:
        num = num.scalar(Fr(-1))
        den = s
    return SymRat(num, den)


def _rat_neg(x):
    if isinstance(x, SymRat):
        return -x
    return -x


def _rat_inv(x):
    if isinstance(x, SymRat):
        return _mk_rat(x.den, x.num)
    if x == 0:
        raise PolyError("division by zero")
    if hasattr(x, "norm"):          # Ga（ℚ(i)）：域逆
        from cas.gaussian import Ga
        return Ga.one() / x
    return Fr(1) / x


def _unify4(na, da, nb, db):
    """四个 Poly 统一到共同变量空间（两两并集，空 vars 提升）。"""
    na, nb = _unify_vs(na, nb)
    vs = na.vars
    if da.vars != vs:
        da = _extend(da, vs)
    if db.vars != vs:
        db = _extend(db, vs)
    return na, da, nb, db


def _rat_mul(a, b):
    if isinstance(a, SymRat) or isinstance(b, SymRat):
        na, da = _parts(a)
        nb, db = _parts(b)
        na, da, nb, db = _unify4(na, da, nb, db)
        return _mk_rat(na * nb, da * db)
    return a * b


def _rat_add(a, b):
    if isinstance(a, SymRat) or isinstance(b, SymRat):
        na, da = _parts(a)
        nb, db = _parts(b)
        na, da, nb, db = _unify4(na, da, nb, db)
        return _mk_rat(na * db + nb * da, da * db)
    return a + b
