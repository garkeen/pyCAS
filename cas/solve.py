from dataclasses import dataclass
from fractions import Fraction as Fr
from math import gcd

from cas import term as T
from cas.term import S, N, Int, Rat, Expr, Sym
from cas.poly import Poly
from cas.simplify import simplify, expand
from cas.errors import PolyError, SolveError


@dataclass
class SolveResult:
    solutions: list
    provisos: list
    status: str
    note: str = ""


def _sub(a, b):
    return T.plus(a, T.neg(b))


def _root_term(f):
    return N(f) if f.denominator == 1 else T.times(N(f.numerator), T.pw(N(f.denominator), T.MONE))


def _square_part(n):
    s = 1
    m = n
    i = 2
    while i * i <= m:
        while m % (i * i) == 0:
            s *= i
            m //= i * i
        i += 1
    return s, m


def sqrt_fr(d):
    if d == 0:
        return T.ZERO
    if d < 0:
        raise SolveError("negative radicand")
    sn, rn = _square_part(d.numerator)
    sd, rd = _square_part(d.denominator)
    s = Fr(sn, sd)
    r = Fr(rn, rd)
    if r == 1:
        return _root_term(s)
    return T.times(_root_term(s), T.sqrt(_root_term(r)))


def _free(t, var):
    if t is var:
        return False
    if isinstance(t, Expr):
        return all(_free(a, var) for a in t.args)
    return True


def _linear_split(t, var):
    if _free(t, var):
        return T.ZERO, t   # 不含未知量的子式（含 e^x 等复杂常数）整体作常数
    if t is var:
        return T.ONE, T.ZERO
    if isinstance(t, Expr):
        name = t.head.name
        if name == "Plus":
            coef = T.ZERO
            const = T.ZERO
            for a in t.args:
                r = _linear_split(a, var)
                if r is None:
                    return None
                c, k = r
                coef = T.plus(coef, c)
                const = T.plus(const, k)
            if not _free(const, var):
                return None
            return coef, const
        if name == "Times":
            lc = None
            cc = T.ONE
            for a in t.args:
                r = _linear_split(a, var)
                if r is None:
                    return None
                c, k = r
                if c is T.ZERO:
                    if not _free(k, var):
                        return None
                    cc = T.times(cc, k)
                elif k is T.ZERO:
                    if lc is not None:
                        return None
                    lc = c
                else:
                    return None
            if lc is None:
                return T.ZERO, cc
            return T.times(lc, cc), T.ZERO
        if name == "Power":
            b, e = t.args
            if isinstance(e, Int):
                if e.v == 1:
                    return _linear_split(b, var)
                if e.v == 0:
                    return T.ZERO, T.ONE
            return None
    return T.ZERO, t


def _peval(p, var, xv):
    d = p.degree(var)
    acc = Fr(0)
    for e in range(d, -1, -1):
        acc = acc * xv + p.monos.get((e,), Fr(0))
    return acc


def _quadratic(c2, c1, c0):
    D = c1 * c1 - 4 * c2 * c0
    two = Fr(2) * c2
    if D < 0:
        # 复根：(−c1 ± i·√|D|) / 2c2（纯符号，无近似）
        sD = sqrt_fr(-D)
        re = T.div(T.neg(_root_term(c1)), _root_term(two))
        im = T.div(T.times(T.IU, sD), _root_term(two))
        return [T.plus(re, im), T.plus(re, T.neg(im))], ""
    sD = sqrt_fr(D)
    x1 = T.div(T.plus(T.neg(_root_term(c1)), sD), _root_term(two))
    if D == 0:
        return [x1], ""
    x2 = T.div(T.plus(T.neg(_root_term(c1)), T.neg(sD)), _root_term(two))
    return [x1, x2], ""


def _sort_sols(sols):
    def sk(t):
        if T.is_num(t):
            return T.num_val(t)
        return Fr(10**9)

    return sorted(sols, key=sk)


def _poly_solve(p, var):
    if p.is_zero():
        return SolveResult([], [], "identity")
    d = p.degree(var)
    if d == 0:
        return SolveResult([], [], "contradiction")
    if d == 1:
        a = p.lc(var)
        b = p.const_val()
        return SolveResult([T.div(T.neg(_root_term(b)), _root_term(a))], [], "ok")
    if d == 2:
        sols, note = _quadratic(
            p.monos.get((2,), Fr(0)),
            p.monos.get((1,), Fr(0)),
            p.monos.get((0,), Fr(0)),
        )
        return SolveResult(_sort_sols(sols), [], "ok" if not note else "unsupported", note=note)

    roots = []
    P = p
    while P.degree(var) >= 3:
        den_lcm = 1
        for v in P.monos.values():
            den_lcm = den_lcm * v.denominator // gcd(den_lcm, v.denominator)
        Pi = P.scalar(Fr(den_lcm))
        a0 = Pi.monos.get((0,), Fr(0))
        an = Pi.lc(var)
        a0i = abs(int(a0))
        ani = abs(int(an)) if an != 0 else 1
        cands = {Fr(0)} if a0i == 0 else set()
        if a0i > 0 and ani > 0:
            ps = [i for i in range(1, a0i + 1) if a0i % i == 0]
            qs = [i for i in range(1, ani + 1) if ani % i == 0]
            for pp in ps:
                for qq in qs:
                    cands.add(Fr(pp, qq))
                    cands.add(Fr(-pp, qq))
        found = False
        for r in sorted(cands):
            if _peval(Pi, var, r) == 0:
                roots.append(_root_term(r))
                g = Poly.one(P.vars) * Poly.mono(P.vars, var, 1) + Poly.const(P.vars, -r)
                q, rem = P.udivmod(g)
                P = q
                found = True
                break
        if not found:
            break
    rem = P
    rd = rem.degree(var) if not rem.is_zero() else -1
    note = ""
    if rd == 1:
        roots.append(_root_term(-rem.const_val() / rem.lc(var)))
    elif rd == 2:
        sols, note = _quadratic(
            rem.monos.get((2,), Fr(0)),
            rem.monos.get((1,), Fr(0)),
            rem.monos.get((0,), Fr(0)),
        )
        roots.extend(sols)
    elif rd >= 3:
        note = "irreducible part of degree %d beyond rational-root method" % rd
    seen = []
    for r in roots:
        if r not in seen:
            seen.append(r)
    return SolveResult(_sort_sols(seen), [], "ok" if not note else "unsupported", note=note)


def _affine(a1, var):
    """a1 是否 var 的仿射式 k*var + b（k 不含 var）-> (k, b) 或 None。"""
    if a1 is var:
        return T.ONE, T.ZERO
    if not isinstance(a1, Expr):
        return None
    if a1.head.name == "Times" and var in a1.args:
        k = T.mk(T.S("Times"), tuple(c for c in a1.args if c is not var))
        if T.free_vars(k):
            return None
        return simplify(k), T.ZERO
    if a1.head.name == "Plus":
        rest = [c for c in a1.args if var not in T.free_vars(c)]
        kpart = [c for c in a1.args if var in T.free_vars(c)]
        if len(kpart) == 1:
            kk = _affine(kpart[0], var)
            if kk is not None:
                return kk[0], simplify(T.mk(T.S("Plus"), tuple(rest))) if rest else T.ZERO
    return None


def _inverse_case(lhs, var):
    """f(var) = c（f 在 spec 声明了逆 inv）：主支逆解。

    sin(x)=c -> arcsin(c) 等；tan(x/2)=t -> 2*atan(t)（仿射复合主支逆）。
    周期族通解未建，诚实标注主支条件。
    逆函数的特殊点折叠由 mk 自动完成（arcsin(1) -> π/2）。
    """
    from cas import spec as _spec

    # 裸函数形态 f(var) = 0（Plus 单项归并后只剩 f 本身）
    if isinstance(lhs, Expr) and len(lhs.args) == 1 and lhs.args[0] is var:
        sp = _spec.get(lhs.head.name)
        if sp is not None and sp.inv is not None:
            sol = simplify(T.mk(S(sp.inv), (T.ZERO,)))
            return SolveResult([sol], [], "ok",
                               note=f"principal branch of {sp.print_name or sp.name}")
        return None

    if not (isinstance(lhs, Expr) and lhs.head.name == "Plus" and len(lhs.args) == 2):
        return None

    def _unwrap(t):
        if isinstance(t, Expr) and t.head.name == "Times" and len(t.args) == 2 and t.args[0] is T.MONE:
            return -1, t.args[1]
        return 1, t

    for a, b in ((lhs.args[0], lhs.args[1]), (lhs.args[1], lhs.args[0])):
        sa, ca = _unwrap(a)
        sb, cb = _unwrap(b)
        if not (isinstance(ca, Expr) and len(ca.args) == 1):
            continue
        af = _affine(ca.args[0], var)
        if af is None:
            continue
        sp = _spec.get(ca.head.name)
        if sp is None or sp.inv is None:
            continue
        if not _free(cb, var):
            continue
        # lhs = sa·f(k·var+b) + sb·cb = 0 -> f(k·var+b) = -(sb/sa)·cb
        k, b = af
        rhs = T.div(cb, T.N(sa)) if sb != sa else T.neg(T.div(cb, T.N(sa)))
        if b is not T.ZERO:
            rhs = T.plus(rhs, T.neg(b))
        sol = simplify(T.div(T.mk(S(sp.inv), (rhs,)), k))
        return SolveResult([sol], [], "ok",
                           note=f"principal branch of {sp.print_name or sp.name}")
    return None


def solve(f, var, budget=100000):
    var = T.S(var) if isinstance(var, str) else var
    if isinstance(f, Expr) and f.head.name == "Eq":
        lhs = _sub(f.args[0], f.args[1])
    else:
        lhs = f
    lhs = simplify(expand(lhs), budget)

    inv_r = _inverse_case(lhs, var)
    if inv_r is not None:
        return inv_r

    lin = _linear_split(lhs, var)
    if lin is not None:
        coef, const = lin
        if T.is_num(coef):
            cv = T.num_val(coef)
            if cv == 0:
                if T.is_num(const) and T.num_val(const) == 0:
                    return SolveResult([], [], "identity")
                return SolveResult([], [], "contradiction")
            return SolveResult([T.div(T.neg(const), coef)], [], "ok")
        return SolveResult(
            [T.div(T.neg(const), coef)],
            [T.mk(S("Ne"), (coef, T.ZERO))],
            "ok",
        )

    try:
        p = Poly.from_term(lhs, (var,))
    except PolyError:
        return _solve_param_lowdeg(lhs, var)
    # 系数域 ℚ(params) 走 term 层参数求解（proviso 机制在 _solve_param_lowdeg）
    from cas.poly import is_param_poly

    if is_param_poly(p):
        return _solve_param_lowdeg(lhs, var)
    return _poly_solve(p, var)


def _solve_param_lowdeg(lhs, var):
    """参数化低次路径（系数域首付款）：系数为其余符号的表达式。

    次数 ≤ 1：−c0/c1（条件 c1≠0）；次数 = 2：通用求根公式（条件 c2≠0）。
    判别式保持符号根式形态——符号域上正负不可判，不做实/复分支（诚实）。
    """
    from cas import ops

    try:
        c3 = ops.coefficient(lhs, var, 3)
    except PolyError:
        return SolveResult([], [], "unsupported", note="not polynomial in " + var.name)
    if c3 is not T.ZERO:
        return SolveResult([], [], "unsupported", note="degree >= 3 with parameters")
    c2 = ops.coefficient(lhs, var, 2)
    c1 = ops.coefficient(lhs, var, 1)
    c0 = ops.coefficient(lhs, var, 0)
    if c2 is T.ZERO:
        if c1 is T.ZERO:
            if c0 is T.ZERO:
                return SolveResult([], [], "identity")
            return SolveResult([], [], "contradiction")
        # 数值系数非零时条件平凡恒真，不入 proviso
        prov = [] if T.is_num(c1) else [T.mk(S("Ne"), (c1, T.ZERO))]
        return SolveResult([T.div(T.neg(c0), c1)], prov, "ok")
    D = simplify(expand(T.plus(T.pw(c1, N(2)), T.neg(T.times(N(4), c2, c0)))))
    sD = T.sqrt(D)
    two_a = T.times(N(2), c2)
    x1 = T.div(T.plus(T.neg(c1), sD), two_a)
    x2 = T.div(T.plus(T.neg(c1), T.neg(sD)), two_a)
    prov = [] if T.is_num(c2) else [T.mk(S("Ne"), (c2, T.ZERO))]
    return SolveResult([x1, x2], prov, "ok")


def check_solution(f, sol, var, budget=100000):
    var = T.S(var) if isinstance(var, str) else var
    if isinstance(f, Expr) and f.head.name == "Eq":
        lhs = _sub(f.args[0], f.args[1])
    else:
        lhs = f
    e = simplify(T.subst(lhs, {var: sol}), budget)
    if e is T.ZERO:
        return "VERIFIED"
    return "UNVERIFIED"