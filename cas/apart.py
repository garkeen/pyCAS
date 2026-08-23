from fractions import Fraction as Fr

from cas.errors import PolyError
from cas.factor import squarefree_decomp, factor
from cas.poly import Poly, SymRat, _rat_inv, _rat_add, _rat_mul, div_exact, is_param_poly


def _poly_sqrt(p):
    """Fr 系数 Poly 完全平方 -> sqrt（Poly）；否则 None。

    主变量长除法平方根：q 最高项系数 s = sqrt(p 最高项系数)（低变量递归），
    后续项由 cur = p − q² 的最高项除以 2·q 最高项系数逐项解出；
    末尾 q·q == p 精确复核（交叉项如 (a-b)² 展开后仍被正确处理）。
    """
    from math import isqrt

    if p.is_zero():
        return p
    if not p.vars:
        c = p.const_val()
        if c < 0:
            return None
        a = isqrt(c.numerator)
        b = isqrt(c.denominator)
        if a * a == c.numerator and b * b == c.denominator:
            return Poly((), {(): Fr(a, b)})
        return None
    x = p.vars[0]

    def _lc_poly(q):
        d = q.degree(x)
        return Poly(q.vars[1:], {k[1:]: v for k, v in q.monos.items() if k[0] == d})

    cur = p
    q = Poly.zero(p.vars)
    while not cur.is_zero():
        d = cur.degree(x)
        dq = q.degree(x) if not q.is_zero() else -1
        if dq == -1:
            if d % 2:
                return None
            slc = _poly_sqrt(_lc_poly(cur))
            if slc is None:
                return None
            m = Poly(p.vars, {(d // 2,) + k: v for k, v in slc.monos.items()})
        else:
            dr = d - dq
            if dr < 0 or dr >= dq:
                return None
            try:
                mc = div_exact(_lc_poly(cur), _lc_poly(q).scalar(Fr(2)))
            except PolyError:
                return None
            if mc.is_zero():
                return None
            m = Poly(p.vars, {(dr,) + k: v for k, v in mc.monos.items()})
        q_old = q
        q = q + m
        cur = cur - q_old.scalar(Fr(2)) * m - m * m
    if q * q == p:
        return q
    return None


def _coef_is_square(c):
    if isinstance(c, SymRat):
        return _poly_sqrt(c.num) is not None and _poly_sqrt(c.den) is not None
    from math import isqrt

    a = isqrt(c.numerator)
    b = isqrt(c.denominator)
    return a * a == c.numerator and b * b == c.denominator


def _coef_sqrt(c):
    if isinstance(c, SymRat):
        return SymRat(_poly_sqrt(c.num), _poly_sqrt(c.den))
    from math import isqrt

    return Fr(isqrt(c.numerator), isqrt(c.denominator))


def _param_factor_quad(g, x):
    """ℚ(params) 上 monic 二次因子的不可约分解。

    判别式完全平方 -> 两个互素线性因子（根 ∈ 系数域）；否则 None（不可约）。
    """
    pc = g.monos.get((1,), Fr(0))
    qc = g.monos.get((0,), Fr(0))
    D = _rat_add(_rat_mul(pc, pc), _rat_mul(Fr(-4), qc))
    if _coef_is_square(D):
        sd = _coef_sqrt(D)
        half = Fr(1) / 2
        r1 = _rat_mul(_rat_add(_rat_mul(Fr(-1), pc), sd), half)
        r2 = _rat_mul(_rat_add(_rat_mul(Fr(-1), pc), _rat_mul(Fr(-1), sd)), half)
        return [
            Poly((x,), {(1,): Fr(1), (0,): _rat_mul(Fr(-1), r1)}),
            Poly((x,), {(1,): Fr(1), (0,): _rat_mul(Fr(-1), r2)}),
        ]
    return None


def _param_factors(g, x):
    """ℚ(params) 上单变量多项式分解为互素不可约因子。

    因子保留首项系数（与 ℚ 域 factor 的 primitive 部分一致，积分器内部
    自行按 lc 规范化）；可约二次的 lc 作为 content 返回，由 apart 折入
    ctotal 校正分子。返回 (因子列表, content 或 None)。
    """
    n = g.degree(x)
    if n <= 0:
        return [], None
    if n == 1:
        return [g], None
    if n == 2:
        lc = g.lc(x)
        facs = _param_factor_quad(g.scalar(_rat_inv(lc)), x)
        if facs is None:
            return [g], None
        return facs, lc
    raise PolyError(f"parameter-domain factorization: degree {n} unsupported")


# ---------------------------------------------------------------------------
# A3：Trager 范数因子分解 over 单代数扩张 Q(alpha)。
#
# p in Q(alpha)[x]：Norm(p) = det(p 在 Q[x][alpha]/(m) 自由模上的乘法
# 矩阵) in Q[x]（m 为 alpha 的 monic 极小多项式）。Norm 的 Q 因子给出
# p 的共轭轨道积——对每个不可约 F|Norm 取 gcd_{Q(alpha)[x]}(p, F)
# 提取真因子。系数域算术全走 SymRat 分数形态（Poly 乘积出口的模约简
# 保证 alpha 次数有界）。适用边界：单 AN 符号、无自由参数混合、
# alpha 次数 <=5；不满足则诚实返回 None 回退既有路径。
# ---------------------------------------------------------------------------


def _an_detect(g):
    """g 的系数中的代数常数符号（经作用域/全局关系表）。

    返回唯一 AN 符号（列表单元素）或 None（无 AN / 多符号 / 自由
    参数混合 / 叶域不支持）。"""
    from cas.integrate import AN_RELATIONS
    from cas.poly import ALG_MODULI

    syms = set()
    for c in g.monos.values():
        if isinstance(c, Fr):
            continue
        if isinstance(c, SymRat):
            for pp in (c.num, c.den):
                syms.update(pp.vars)
                for cc in pp.monos.values():
                    if not isinstance(cc, Fr):
                        return None
        else:
            return None
    if not syms:
        return None
    rel = [v for v in syms if v in AN_RELATIONS or v in ALG_MODULI]
    if len(rel) == 1 and syms == set(rel):
        return rel[0]
    return None


def _det_poly(mat):
    """Poly 条目行列式（余子式展开 + 零元剪枝）。"""
    n = len(mat)
    if n == 1:
        return mat[0][0]
    if n == 2:
        return mat[0][0] * mat[1][1] - mat[0][1] * mat[1][0]
    total = None
    for j in range(n):
        a = mat[0][j]
        if a.is_zero():
            continue
        minor = [row[:j] + row[j + 1:] for row in mat[1:]]
        sub = _det_poly(minor)
        term = a * sub
        if total is None:
            total = -term if j % 2 else term
        else:
            total = total - term if j % 2 else total + term
    if total is None:
        total = Poly.zero(mat[0][0].vars)
    return total


def _norm_det(p2, alpha, m):
    """p2 in Q[x,alpha] -> Norm(p2) in Q[x]。

    M[j][k] = (p2*alpha^j mod m) 的 alpha^k 系数；行列式 = 范数。
    """
    from cas.poly import _reduce_alg_var

    n = m.degree(alpha)
    ai = p2.vars.index(alpha)
    amono = tuple(1 if i == ai else 0 for i in range(len(p2.vars)))
    alpha_p2 = Poly(p2.vars, {amono: Fr(1)})
    zero_m = {tuple(0 for _ in p2.vars): Fr(0)}

    def coef_in(q, k):
        idx = q._var_idx(alpha)
        out = {}
        for kk, vv in q.monos.items():
            if kk[idx] == k:
                rest = kk[:idx] + kk[idx + 1:]
                out[rest] = out.get(rest, Fr(0)) + vv
        vs = tuple(v for v in q.vars if v is not alpha)
        return Poly(vs, out)

    pw = Poly(p2.vars, dict(zero_m))
    pw.monos[tuple(0 for _ in p2.vars)] = Fr(1)
    mat = []
    for _j in range(n):
        col = _reduce_alg_var(p2 * pw, alpha, m)
        mat.append([coef_in(col, k) for k in range(n)])
        pw = pw * alpha_p2
    return _det_poly(mat)


def _kx_gcd(a, b, alpha, m):
    """K[x] 欧几里得 gcd（K 系数走 SymRat 分数域）。

    每步余式的 α 部分显式模约简（_reduce_alg_var）——外层通道在
    alg_suspend 下运行（保持参数语义与答案形态），gcd 的零判定
    必须用关系语义（α²−2 折叠为零），此处局部开启。
    返回 monic 化 gcd；平凡（零/常量）返回 None。"""
    from cas.poly import _reduce_alg_var

    def kred(p):
        out = {}
        for k, c in p.monos.items():
            if isinstance(c, SymRat):
                out[k] = SymRat(_reduce_alg_var(c.num, alpha, m),
                                _reduce_alg_var(c.den, alpha, m))
            else:
                out[k] = c
        return Poly(p.vars, out)

    r0, r1 = kred(a), kred(b)
    while not r1.is_zero():
        _, rr = r0.udivmod(r1)
        rr = kred(rr)
        r0, r1 = r1, rr
    if r0.is_zero() or r0.degree(r0.vars[0]) < 1:
        return None
    lc = r0.lc(r0.vars[0])
    return r0.scalar(_rat_inv(lc))


def _an_factor(g, x):
    """Q(alpha)[x] Trager 分解。返回 (monic 因子列表, lc content) 或 None。"""
    alpha = _an_detect(g)
    if alpha is None:
        return None
    from cas.integrate import AN_RELATIONS
    from cas.poly import ALG_MODULI

    m = AN_RELATIONS.get(alpha) or ALG_MODULI.get(alpha)
    if m is None or m.degree(alpha) > 5:
        return None

    # 1) 清分母：p~ 的系数为 Q[alpha]-Poly
    items = []
    for k, c in g.monos.items():
        if isinstance(c, Fr):
            items.append((k, Poly((alpha,), {(0,): c}), None))
        elif isinstance(c, SymRat):
            items.append((k, c.num, c.den))
        else:
            return None
    D = Poly.one((alpha,))
    for _, _num, den in items:
        if den is not None:
            D = D * den
    coeffs = {k: (num * D if den is not None else num)
              for k, num, den in items}

    # 2) 两变量空间 (x, alpha) 构造 Norm 并在 Q[x] 上分解
    two = (x, alpha)
    p2m = {}
    for k, cp in coeffs.items():
        for kk, vv in cp.monos.items():
            p2m[(k[0],) + kk] = vv
    norm = _norm_det(Poly(two, p2m), alpha, m)
    if norm.is_const() or norm.degree(x) < 1:
        return None
    _c0, irrs = factor(norm)

    # 3) 逐轨道积 F 提取真因子（squarefree 输入保证互素分离）
    one_a = Poly.one((alpha,))
    pk = Poly((x,), {k: SymRat(cp, one_a) for k, cp in coeffs.items()})
    facs = []
    for h, _mult in irrs:
        gg = _kx_gcd(pk, h, alpha, m)
        if gg is not None and gg.degree(x) >= 1:
            facs.append(gg)
    if not facs:
        return None

    # 4) 完整性守卫：提取的因子次数和必须等于 deg(g)（否则漏提，
    #    宁可诚实放弃也不给残缺分解）
    total = sum(f_.degree(x) for f_ in facs)
    if total != g.degree(x):
        return None
    monic = [f_.scalar(_rat_inv(f_.lc(x))) for f_ in facs]
    return monic, g.lc(x)


def _xgcd(a, b, x):
    r0, r1 = a, b
    s0, s1 = Poly.one(a.vars), Poly.zero(a.vars)
    t0, t1 = Poly.zero(a.vars), Poly.one(a.vars)
    while not r1.is_zero():
        q, r = r0.udivmod(r1)
        r0, r1 = r1, r
        s0, s1 = s1, s0 - q * s1
        t0, t1 = t1, t0 - q * t1
    if r0.is_zero():
        return Poly.zero(a.vars), Poly.zero(a.vars)
    lc = r0.lc(x)
    return s0.scalar(Fr(1) / lc), t0.scalar(Fr(1) / lc)


def _apart_power(f, g, k, x):
    out = []
    whole = Poly.zero(f.vars)
    cur = f
    j = k
    while not cur.is_zero() and j >= 1:
        qq, rr = cur.udivmod(g)
        out.append((rr, g, j))
        cur = qq
        j -= 1
    if not cur.is_zero():
        whole = cur
    return out, whole


def _split_frac(r, sqf, x, out, whole):
    if len(sqf) == 1:
        g0, k0 = sqf[0]
        terms, w = _apart_power(r, g0, k0, x)
        out.extend(terms)
        if not w.is_zero():
            whole.append(w)
        return
    mid = len(sqf) // 2
    left, right = sqf[:mid], sqf[mid:]
    a = Poly.one(r.vars)
    for g0, k0 in left:
        a = a * g0 ** k0
    b = Poly.one(r.vars)
    for g0, k0 in right:
        b = b * g0 ** k0
    s, t = _xgcd(a, b, x)
    _split_frac(r * s, right, x, out, whole)
    _split_frac(r * t, left, x, out, whole)


def apart(f, g, x=None):
    if len(f.vars) != 1 or f.vars != g.vars:
        raise PolyError("univariate only")
    x = f.vars[0] if x is None else x
    if g.is_zero():
        raise PolyError("division by zero")
    q, r = f.udivmod(g)
    sqf = []
    ctotal = Fr(1)
    for g0, k0 in squarefree_decomp(g):
        if is_param_poly(g0):
            # 参数域：deg<=2 走既有判别式路径（AN 符号同样适用，保持
            # log(x±√2) 教科书形态）；deg>=3 的 AN 多项式走 Trager
            # 范数分解；更高阶不可约诚实拒。
            # 可约因子的首项系数作为 content 折入 ctotal，校正分子。
            an = _an_factor(g0, x) if g0.degree(x) >= 3 else None
            if an is not None:
                facs, pc = an
            else:
                facs, pc = _param_factors(g0, x)
            if pc is not None:
                ctotal = _rat_mul(ctotal, pc)
            for h in facs:
                sqf.append((h, k0))
        else:
            c0, facs = factor(g0)
            ctotal = ctotal * c0
            for h, _ in facs:
                sqf.append((h, k0))
    out, whole = [], []
    if not r.is_zero():
        if ctotal != 1:
            r = r.scalar(_rat_inv(ctotal))
        _split_frac(r, sqf, x, out, whole)
    for w in whole:
        q = q + w
    return q, out


# ---------------------------------------------------------------------------
# 复合项作原子变量的推广：把 Log(x)/Sin(x)/Exp(x) 等非多项式头复合项当
# 生成元，表达式看作 ℚ[其余符号][atom] 的元素做多项式除法。
# 数学本质与字面变量 apart 同（多项式长除法 + 因式分解），只是"变量"是复合项。
# ---------------------------------------------------------------------------

_POLY_HEADS = ("Plus", "Times", "Power")


def _collect_atoms(t, out):
    """收集非多项式头复合项（Log/Sin/Cos/Exp/Abs/...）作为原子变量候选。"""
    from cas import term as T

    if isinstance(t, T.Expr):
        n = t.head.name
        if n in _POLY_HEADS:
            for a in t.args:
                _collect_atoms(a, out)
        elif n in ("Lt", "Le", "Gt", "Ge", "Eq", "Ne", "And", "Or", "Not"):
            return   # 比较/逻辑头不是数值表达式
        else:
            if not any(a is t for a in out):
                out.append(t)


def find_atom(*terms):
    """自动选原子：唯一复合项 → 用之；多个/无 → None（回退字面变量路径）。"""
    atoms = []
    for t in terms:
        _collect_atoms(t, atoms)
    return atoms[0] if len(atoms) == 1 else None


def apart_term(num, den, atom):
    """复合项作原子变量的 apart：num/den 视作 ℚ[其余符号][atom] 上分式。

    atom 是驻留复合项（如 Log(x)）。返回 apart 结果的 term。
    """
    from cas import term as T
    from cas.term import S

    f = Poly.from_term(num, (atom,))
    g = Poly.from_term(den, (atom,))
    q, terms = apart(f, g)
    parts = []
    if not q.is_zero():
        parts.append(q.to_term())
    for nn, dd, k in terms:
        d = dd.to_term()
        if k == 1:
            parts.append(T.div(nn.to_term(), d))
        else:
            parts.append(T.div(nn.to_term(), T.pw(d, T.N(k))))
    if not parts:
        return T.ZERO
    if len(parts) == 1:
        return parts[0]
    return T.mk(S("Plus"), tuple(parts))