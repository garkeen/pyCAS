"""ODE 基础层（M3 收尾：分类求解 + 微分回验背书）。

支持题型（每种都命名入账，可解释）：
- direct：y' = f(x)，直接积分；
- separable：y' 的系数/余项可按 x、y 分变量（g(y) 为幂函数族），
  能显式解则显式（log 情形常数重命名 e^C -> C1），否则给隐式方程；
- linear1：A(x)y' + B(x)y + C(x) = 0，积分因子 exp(∫B/A)；
- constcoef2：a y'' + b y' + c y = 0，特征方程；实根/重根/复根三角实形式。
导数形态：D(y, x) / D(D(y, x), x) 名词头。积分常数 C1/C2。
正确性：解回代微分，equivalent 判零（VERIFIED/PROBABLE/UNVERIFIED 三态诚实）。
"""

from dataclasses import dataclass
from fractions import Fraction as Fr

from cas import term as T
from cas.term import Expr
from cas.errors import PolyError
from cas.pprint import to_str
from cas.simplify import simplify, expand

C1 = T.S("C1")
C2 = T.S("C2")


@dataclass
class OdeResult:
    sol: object          # 项（显式）/ Eq（隐式）/ None（拒答）
    kind: str            # direct / separable / linear1 / constcoef2 / unsupported
    status: str          # VERIFIED / PROBABLE / UNVERIFIED / implicit / -
    note: str = ""


def _derivs(y, x):
    dy = T.mk(T.S("D"), (y, x))
    dy2 = T.mk(T.S("D"), (dy, x))
    return dy, dy2


def _coef(t, var, k):
    """var^k 的系数：var 只允许整数幂出现；不含 var 的子式视为不透明系数
    （exp(x) 类容忍，比 ops.coefficient 宽）；形态不合 -> None。"""
    terms = t.args if isinstance(t, Expr) and t.head.name == "Plus" else (t,)
    acc = []
    for m in terms:
        facs = m.args if isinstance(m, Expr) and m.head.name == "Times" else (m,)
        num = Fr(1)
        deg = 0
        rest = []
        ok = True
        for fa in facs:
            if T.is_num(fa):
                num *= T.num_val(fa)
            elif fa is var:
                deg += 1
            elif (isinstance(fa, Expr) and fa.head.name == "Power" and fa.args[0] is var
                  and isinstance(fa.args[1], T.Int) and fa.args[1].v >= 0):
                deg += fa.args[1].v
            elif var in T.free_vars(fa):
                ok = False
                break
            else:
                rest.append(fa)
        if not ok:
            return None
        if deg == k:
            acc.append(T.times(T.N(num), *rest) if rest else T.N(num))
    return simplify(T.plus(*acc)) if acc else T.ZERO


def _free_of(t, *syms):
    fv = T.free_vars(t)
    return all(s not in fv for s in syms)


def _split_vars(t, x, y):
    """Times 因子按自由变量分桶 -> (数值系数 Fr, x-only 因子积, y-only 因子积)，
    含混合因子 -> None（不可分离）。"""
    if not isinstance(t, Expr) or t.head.name != "Times":
        if T.is_num(t):
            return T.num_val(t), T.ONE, T.ONE
        if _free_of(t, y):
            return Fr(1), t, T.ONE
        if _free_of(t, x):
            return Fr(1), T.ONE, t
        return None
    num = Fr(1)
    xf = []
    yf = []
    for a in t.args:
        if T.is_num(a):
            num *= T.num_val(a)
        elif _free_of(a, y):
            xf.append(a)
        elif _free_of(a, x):
            yf.append(a)
        else:
            return None
    return num, T.times(*xf) if xf else T.ONE, T.times(*yf) if yf else T.ONE


def _verify_sol(sol, f, y, x, dy, dy2, order):
    from cas.diff import d as dd

    sub = {y: sol, dy: dd(sol, x)} if order >= 1 else {y: sol}
    if order >= 2:
        sub[dy2] = dd(dd(sol, x), x)
    r = simplify(expand(T.subst(f, sub)))
    from cas.decide import equivalent, T3

    e = equivalent(r, T.ZERO)
    return {T3.YES: "VERIFIED", T3.PROBABLE: "PROBABLE"}.get(e, "UNVERIFIED")


def _solve_constcoef2(A, B, Cc, y, x, f, dy, dy2):
    """a r^2 + b r + c = 0 特征方程 -> 实形式通解。"""
    from cas.solve import _root_term, sqrt_fr as _sqrt_fr

    a, b, c = T.num_val(A), T.num_val(B), T.num_val(Cc)
    D = b * b - 4 * a * c

    def ex(r):
        return T.exp(T.times(r, x)) if r != 0 else T.ONE

    if D > 0:
        sD = _sqrt_fr(D)
        two_a = Fr(2) * a
        r1 = T.div(T.plus(T.neg(_root_term(b)), sD), _root_term(two_a))
        r2 = T.div(T.plus(T.neg(_root_term(b)), T.neg(sD)), _root_term(two_a))
        sol = T.plus(T.times(C1, ex(r1)), T.times(C2, ex(r2)))
        kind_note = "distinct real roots"
    elif D == 0:
        r = _root_term(-b / (2 * a))
        sol = T.times(T.plus(C1, T.times(C2, x)), ex(r))
        kind_note = "repeated root"
    else:
        # 复根三角实形式：e^{αx}(C1 cos βx + C2 sin βx)，β = √|D|/2|a|
        alpha = -b / (2 * a)
        beta = T.div(_sqrt_fr(-D), _root_term(Fr(2) * abs(a)))
        ea = ex(_root_term(alpha)) if alpha != 0 else T.ONE
        core = T.plus(T.times(C1, T.cos(T.times(beta, x))),
                      T.times(C2, T.sin(T.times(beta, x))))
        sol = T.times(ea, core) if ea is not T.ONE else core
        kind_note = "complex roots (trig real form)"
    st = _verify_sol(sol, f, y, x, dy, dy2, 2)
    return OdeResult(sol, "constcoef2", st, kind_note)


def _solve_linear1(A, B, Cc, y, x, f, dy, dy2):
    """A y' + B y + C = 0 -> y' + p y = q，积分因子 exp(∫p dx)。"""
    from cas.integrate import integrate as zz_int

    p = simplify(T.div(B, A))
    q = simplify(T.div(T.neg(Cc), A))
    if not (_free_of(p, y) and _free_of(q, y)):
        return None
    try:
        P, _ok1, m1, _prov1 = zz_int(p, x)
        G, _ok2, m2, _prov2 = zz_int(simplify(T.times(q, T.exp(P))), x)
    except PolyError:
        return None
    # IF = exp(P)：解写为 (G + C1)·exp(−P)，避免 C1/exp(P) 形态
    sol = simplify(T.times(T.plus(G, C1), T.exp(T.neg(P))))
    st = _verify_sol(sol, f, y, x, dy, dy2, 1)
    return OdeResult(sol, "linear1", st, f"integrating factor exp(int {to_str(p)})")


def _solve_separable(A, B, y, x, f, dy, dy2):
    """A(x,y) y' + B(x,y) = 0 且 A、B 因子可按变量分桶 -> 分离变量。"""
    from cas.integrate import integrate as zz_int

    sa = _split_vars(A, x, y)
    sb = _split_vars(B, x, y)
    if sa is None or sb is None:
        return None
    na, ax, ay = sa
    nb, bx, by = sb
    # y' = -B/A：dy/dx = (-nb/na)·(bx/ax)·(by/ay) -> k(y) dy = f(x) dx，
    # k = ay/by，f = (-nb/na)·bx/ax（数值符号不可丢）
    ky = simplify(T.div(ay, by)) if by is not T.ONE else ay
    sgn = Fr(-1) * nb / na
    fx0 = T.times(T.N(sgn), bx) if sgn != 1 else bx
    fx = simplify(T.div(fx0, ax)) if ax is not T.ONE else simplify(fx0)
    if not (_free_of(ky, x) and _free_of(fx, y)):
        return None
    try:
        K, _o1, _m1, _p1 = zz_int(ky, y)
        F, _o2, _m2, _p2 = zz_int(fx, x)
    except PolyError:
        return None
    rhs = T.plus(F, C1)
    # 显式化：K 的常见形态
    if K is y:
        sol, note = rhs, "explicit"
    elif isinstance(K, Expr) and K.head.name == "Log" and K.args[0] is y:
        sol = T.times(C1, T.exp(F))
        note = "explicit (constant renamed e^C1 -> C1, C1 != 0)"
    else:
        # K = c*y^m 形态（幂函数族）：反解 y = (rhs/c)^(1/m)
        sol = _invert_power_K(K, y, rhs)
        if sol is None:
            imp = T.mk(T.S("Eq"), (K, rhs))
            return OdeResult(imp, "separable", "implicit", "implicit solution")
        note = "explicit (power inversion)"
    st = _verify_sol(sol, f, y, x, dy, dy2, 1)
    return OdeResult(sol, "separable", st, note)


def _invert_power_K(K, y, rhs):
    """K = c*y^m（m 非零有理数）-> y = (rhs/c)^(1/m)；否则 None。"""
    c = Fr(1)
    core = K
    if isinstance(core, Expr) and core.head.name == "Times":
        nums = [a for a in core.args if T.is_num(a)]
        rest = [a for a in core.args if not T.is_num(a)]
        if len(rest) != 1:
            return None
        for nm in nums:
            c *= T.num_val(nm)
        core = rest[0]
    if core is y:
        return simplify(T.div(rhs, T.N(c))) if c != 1 else rhs
    if not (isinstance(core, Expr) and core.head.name == "Power" and core.args[0] is y):
        return None
    e = core.args[1]
    if isinstance(e, T.Int):
        m = Fr(e.v)
    elif isinstance(e, T.Rat):
        m = e.f
    else:
        return None
    if m == 0:
        return None
    base = simplify(T.div(rhs, T.N(c)))
    return simplify(T.pw(base, T.N(Fr(m.denominator, m.numerator))))


def dsolve(f, y, x):
    """解 ODE f = 0（f 含 D(y,x) 名词头）-> OdeResult。

    分类顺序：二阶常系数齐次 -> 一阶线性 -> 可分离（含 direct）。
    """
    dy, dy2 = _derivs(y, x)
    z1, z2 = T.S("_ode_z1"), T.S("_ode_z2")
    r2 = T.subst(f, {dy2: z2})
    if z2 in T.free_vars(r2):
        # 二阶：要求对 z2 线性，余项对 D(y,x)、y 线性且系数全为数值
        A = _coef(r2, z2, 1)
        rest = _coef(r2, z2, 0)
        if A is None or rest is None or not T.is_num(A) or T.num_val(A) == 0:
            return OdeResult(None, "unsupported", "-", "second order: not constant-coefficient linear")
        r1 = T.subst(rest, {dy: z1})
        B = _coef(r1, z1, 1)
        rem = _coef(r1, z1, 0)
        if B is None or rem is None or not T.is_num(B):
            return OdeResult(None, "unsupported", "-", "second order: not linear in y'")
        Cc = _coef(rem, y, 1)
        tail = _coef(rem, y, 0)
        if Cc is None or tail is None or not T.is_num(Cc) or tail is not T.ZERO:
            return OdeResult(None, "unsupported", "-", "second order: only homogeneous supported")
        # 重构守卫：rem 必须恰为 Cc*y（防 y² 类非线性项被零系数误吞）
        if simplify(T.plus(rem, T.neg(T.times(Cc, y)))) is not T.ZERO:
            return OdeResult(None, "unsupported", "-", "second order: only homogeneous supported")
        return _solve_constcoef2(A, B, Cc, y, x, f, dy, dy2)
    # 一阶
    r1 = T.subst(f, {dy: z1})
    if z1 not in T.free_vars(r1):
        return OdeResult(None, "unsupported", "-", "no derivative found")
    A = _coef(r1, z1, 1)
    B = _coef(r1, z1, 0)
    if A is None or B is None:
        return OdeResult(None, "unsupported", "-", "not first-degree in y'")
    # direct：y' = f(x)
    if _free_of(A, y) and _free_of(B, y):
        from cas.integrate import integrate as zz_int

        try:
            F, ok, _m, _prov = zz_int(simplify(T.div(T.neg(B), A)), x)
        except PolyError:
            return OdeResult(None, "unsupported", "-", "direct: integrand not integrable")
        sol = T.plus(F, C1)
        st = _verify_sol(sol, f, y, x, dy, dy2, 1)
        return OdeResult(sol, "direct", st, "y = int f dx + C1")
    # 一阶线性：A(x) y' + B(x) y + C(x) = 0（余项重构必须恰为零，防 y² 类误判）
    Bc = _coef(B, y, 1)
    Cc = _coef(B, y, 0)
    if (Bc is not None and Cc is not None and _free_of(A, y)
            and _free_of(Bc, y) and _free_of(Cc, y)
            and simplify(T.plus(B, T.neg(T.times(Bc, y)), T.neg(Cc))) is T.ZERO):
        lin = _solve_linear1(A, Bc, Cc, y, x, f, dy, dy2)
        if lin is not None:
            return lin
    # 可分离
    sep = _solve_separable(A, B, y, x, f, dy, dy2)
    if sep is not None:
        return sep
    return OdeResult(None, "unsupported", "-", "no classification matched")
