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
    if c < 0:
        return False
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

    推广：任意次数。二次走判别式完全平方精确分解；高次先试
    有理根线性因子剥离（ℚ(params) 上：常数项/首项系数整除搜索
    经 SymRat 精确验证），剩余不可约部分诚实返回 [g]（不抛
    RischUnsupported——分解粒度不足不影响正确性，仅使部分分式
    更粗）。理论最优为 ℚ(params) 上 Zassenhaus 通用分解，本函数
    为其可验证子集。
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
    # n >= 3：一般有理根剥离（ℚ(params) 上：r∈ℚ 候选经 SymRat 求值精确验证）
    # 覆盖 (x - r) 因子对任意次数，含参多项式亦可（ر∈ℚ 时参量消去，非参根需 Trager）。
    try:
        lc = g.lc(x)
        # 收集候选 r：若系数全ℚ则 divisor 枚举；含参时仅试小集合 r∈{0,±1,±2,±1/2}
        # 评估经 SymRat 零判定精确，避免整数分解爆炸
        cand_rs = set()
        # 常数项为零 → 0 根
        c0 = g.monos.get((0,), Fr(0))
        def _is_zero_coef(c):
            return c.is_zero() if hasattr(c, "is_zero") else c == 0
        if _is_zero_coef(c0):
            cand_rs.add(Fr(0))
        # 小有理候选集
        for r_ in (Fr(1), Fr(-1), Fr(2), Fr(-2), Fr(1,2), Fr(-1,2)):
            cand_rs.add(r_)
        # 若全ℚ系数则扩充 divisor 枚举
        all_fr = all(isinstance(c, Fr) for c in g.monos.values())
        if all_fr:
            from math import gcd as _gcd
            # 复用 solve 的 divisor 逻辑：den_lcm 已消除分母
            den_lcm = 1
            for v in g.monos.values():
                den_lcm = den_lcm * v.denominator // _gcd(den_lcm, v.denominator)
            # 此处简化：仅试已列小集合，避免 a0i/ani 大数枚举爆炸
            pass
        facs = []
        cur = g
        for r_ in sorted(cand_rs, key=lambda f: (abs(f), f)):
            # 试除 (x - r)
            lin = Poly((x,), {(1,): Fr(1), (0,): -r_})
            # 需 Poly 域上精确整除判定
            try:
                q, rem = cur.udivmod(lin)
            except Exception:
                continue
            if rem.is_zero() or all((c.is_zero() if hasattr(c, "is_zero") else c==0) for c in rem.monos.values()):
                facs.append(lin)
                cur = q
                if cur.degree(x) <= 2:
                    break
        if facs:
            # 剩余部分递归
            if cur.degree(x) >= 1:
                sub_facs, sub_pc = _param_factors(cur, x) if cur.degree(x) >=3 else ([cur], None) if cur.degree(x)>=1 else ([], None)
                # 二次剩余走判别式路径
                if cur.degree(x)==2:
                    lc2 = cur.lc(x)
                    qfacs = _param_factor_quad(cur.scalar(_rat_inv(lc2)), x)
                    if qfacs is not None:
                        return facs + qfacs, lc if len(facs)==1 else None
                    else:
                        return facs + [cur], None
                return facs + sub_facs, None
            return facs, None
        return [g], None
    except Exception:
        return [g], None


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


def _coeff_domain(g):
    """Poly g 的系数域标签（支撑矩阵分发表键）。

    唯一真源：cas.kernel_proj.coeff_domain_of_poly（N5 统一投影）。
    本函数为历史名薄壳，保留导入面不变。
    """
    from cas.kernel_proj import coeff_domain_of_poly as _proj
    tag = _proj(g)
    # 兼容旧名：kernel_proj 返回 "Q"/"QI"/"PARAMS"/"AN"/"MIXED"/"UNKNOWN"
    # apart 旧分发表用 'Q'/'QI'/'PARAMS'/'AN'/'MIXED'
    return tag


def _an_detect(g):
    """g 的系数中的代数常数符号（M7.0-b 统一登记处）。

    返回唯一 AN 符号（列表单元素）或 None（无 AN / 多符号 / 自由
    参数混合 / 叶域不支持）。多符号时由上层 _an_factor_multi 经
    primelt 压单处理。
    """
    from cas.algfield import ALG_FIELDS

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
    rel = [v for v in syms if v in ALG_FIELDS]
    if len(rel) == 1 and syms == set(rel):
        return rel[0]
    return None


def _an_detect_multi(g):
    """g 中全部 AN 符号列表（多符号时返回列表，供 primelt 压单）。"""
    from cas.algfield import ALG_FIELDS
    syms = set()
    for c in g.monos.values():
        if isinstance(c, SymRat):
            for pp in (c.num, c.den):
                syms.update(v for v in pp.vars if v in ALG_FIELDS)
    rel = [v for v in syms if v in ALG_FIELDS]
    return rel if len(rel) >= 2 else None


def _det_poly(mat):
    """Poly 条目行列式（兼容薄壳，B4 已统一 Bareiss）。

    旧 O(n!) 余子式展开已退役，保留名仅供 tests/test_an_rational 对照；
    实现直接委托 _det_bareiss（O(n³)，域泛化）。
    """
    return _det_bareiss(mat)


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
    return _det_bareiss(mat)


def _det_bareiss(mat):
    """Poly 条目行列式（Bareiss 免分数消元）。

    取代余子式展开（O(n!)——旧 deg(m)<=5 限界的真实根源，B4 统一
    项）：Bareiss 主步 a_ij <- (a_ij*p_k - a_ik*a_kj)/p_{k-1} 除法
    精确（整域性质），O(n^3) 次乘除；行交换记号差。条目为同变元
    Poly（coef_in 输出），零元保留 vars。"""
    from cas.poly import div_exact

    n = len(mat)
    zero = mat[0][0].scalar(Fr(0))
    M = [row[:] for row in mat]
    sign = Fr(1)
    prev = None
    for k in range(n - 1):
        if M[k][k].is_zero():
            for r in range(k + 1, n):
                if not M[r][k].is_zero():
                    M[k], M[r] = M[r], M[k]
                    sign = -sign
                    break
            else:
                return zero
        p = M[k][k]
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                t = M[i][j] * p - M[i][k] * M[k][j]
                if prev is None:
                    M[i][j] = t
                elif isinstance(prev, Poly) and len(prev.monos) == 1 \
                        and next(iter(prev.monos)) == ():
                    # 常数除数：纯缩放（div_exact 的 _rec_view 不支持
                    # 空 exponent 键——常数 Poly 直除在此短路）
                    M[i][j] = t.scalar(Fr(1) / next(iter(prev.monos.values())))
                else:
                    M[i][j] = div_exact(t, prev)
            M[i][k] = zero
        prev = p
    return M[n - 1][n - 1].scalar(sign)


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


def _binom(a, b):
    from math import comb
    return comb(a, b)


def _ga_factor(g, x):
    """ℚ(i)[x] 分解：Norm = g·conj(g) ∈ ℚ[x] → factor → gcd 拉回。

    单扩张二次，Norm 次数 2·deg(g)，Bareiss 已 O(n³)。"""
    from cas.gaussian import Ga
    # 构造共轭多项式
    conj_monos = {}
    for k, c in g.monos.items():
        if isinstance(c, Ga):
            conj_monos[k] = Ga(c.re, -c.im)
        elif isinstance(c, Fr):
            conj_monos[k] = c
        else:
            return None
    gc = Poly(g.vars, conj_monos)
    norm = g * gc
    # Norm 系数应落 ℚ（虚部消去）
    for v in norm.monos.values():
        if isinstance(v, Ga) and v.im != 0:
            return None
        if not isinstance(v, (Fr, Ga)):
            return None
    # 化为 Fr 系数 Poly 调用 factor
    norm_q = Poly(g.vars, {k: (v.re if isinstance(v, Ga) else v) for k, v in norm.monos.items()})
    if norm_q.is_const() or norm_q.degree(x) < 1:
        return None
    _c0, irrs = factor(norm_q)
    # 逐因子拉回
    def _ga_gcd(a, b):
        # ℚ(i)[x] 欧几里得 gcd，系数 Ga 域
        r0, r1 = a, b
        while not r1.is_zero():
            _, rr = r0.udivmod(r1)
            r0, r1 = r1, rr
        if r0.is_zero() or r0.degree(x) < 1:
            return None
        return r0.scalar(Ga(Fr(1)) / r0.lc(x)) if isinstance(r0.lc(x), Ga) else r0.scalar(Fr(1) / r0.lc(x))
    facs = []
    for h, _ in irrs:
        # h ∈ ℚ[x] 提升为 ℚ(i)[x]
        h_ga = Poly(g.vars, {k: Ga(v) for k, v in h.monos.items()})
        gg = _ga_gcd(g, h_ga)
        if gg is not None and gg.degree(x) >= 1:
            facs.append(gg)
    if not facs:
        return None
    total = sum(f_.degree(x) for f_ in facs)
    if total != g.degree(x):
        return None
    # 首一化
    monic = []
    for f_ in facs:
        lc = f_.lc(x)
        inv = Ga(Fr(1)) / lc if isinstance(lc, Ga) else Fr(1) / lc
        monic.append(f_.scalar(inv))
    return monic, g.lc(x)


def _an_factor(g, x):
    """Q(alpha)[x] Trager 分解。返回 (monic 因子列表, lc content) 或 None。

    支持多 α：经 primelt.compress_chain 压单 β 后走单扩张 Trager。
    """
    from cas.algfield import ALG_FIELDS
    alpha = _an_detect(g)
    multi = None
    if alpha is None:
        # 多符号尝试压单
        multi = _an_detect_multi(g)
        if multi is None:
            return None
        # 压单：收集各 α 的极小多项式与原始项
        try:
            from cas.primelt import compress_chain
            ms = []
            terms = []
            for sym in multi:
                fld = ALG_FIELDS[sym]
                # 仅 Fr 系数单扩张可压（SymRat 混域 honest None）
                if any(not isinstance(c, Fr) for c in fld.m):
                    return None
                ms.append([Fr(c) if not isinstance(c, Fr) else c for c in fld.m])
                terms.append(fld.origin if fld.origin is not None else sym)
            cres = compress_chain(ms, terms)
            if cres is None:
                return None
            Scoefs, maps, beta_term = cres
            # 多α → 单β 系数重写（M78.6 闭合）：ℚ(α₁,…,αₙ)[x] → ℚ(β)[x]
            try:
                from cas.algfield import af_q
                from cas.term import S as _S
                bsym = _S("_an_beta")
                beta_fld = af_q([Fr(c) for c in Scoefs])
                # 旧 α 映射表：sym -> AlgElem(β)
                amap = {}
                for sym, mp in zip(multi, maps):
                    amap[sym] = beta_fld.elem([Fr(c) for c in mp])
                def _poly_to_beta(p):
                    if not p.vars:
                        return Poly((bsym,), {(0,): p.const_val()}) if not p.is_zero() else Poly.zero((bsym,))
                    # p  vars ⊆ old alphas
                    # 逐单项式在 β 域上求值
                    acc = beta_fld.zero
                    for mono, cf in p.monos.items():
                        term_elem = beta_fld.const(cf)
                        for idx, sym in enumerate(p.vars):
                            e = mono[idx]
                            if e == 0:
                                continue
                            ae = amap.get(sym)
                            if ae is None:
                                raise PolyError("unknown alpha var")
                            term_elem = term_elem * (ae ** e)
                        # term_elem.cs -> Poly over bsym
                        acc = acc + term_elem
                    # acc.cs -> Poly((bsym,))
                    if acc.is_zero():
                        return Poly.zero((bsym,))
                    mm = {(i,): c for i, c in enumerate(acc.cs) if c != 0}
                    return Poly((bsym,), mm)
                # 重写 g：x 系数 SymRat/Fr → ℚ(β) 上
                new_monos = {}
                for k, c in g.monos.items():
                    if isinstance(c, Fr):
                        new_monos[k] = c
                    elif isinstance(c, SymRat):
                        nb = _poly_to_beta(c.num)
                        db = _poly_to_beta(c.den)
                        # db 为 Poly((bsym,)) ，需提升为 SymRat(β)
                        if db.is_zero():
                            raise PolyError("zero denominator")
                        # 若 nb/db 均为 β 上多项式，构造 SymRat(β)
                        # 单变量 β 上 SymRat 规范形经 _mk_rat 自动处理
                        from cas.poly import SymRat as _SR
                        # 统一到 β 单变量空间后转 SymRat
                        # 若 db 为常数 1 则直接 Fr 有理化
                        if nb.is_const() and db.is_const():
                            new_monos[k] = nb.const_val() / db.const_val()
                        else:
                            # 构造 ℚ(β) 元素：Poly((bsym,)) -> SymRat
                            # 借 SymRat(β) 的分式形态：分子分母均为 Poly((bsym,))
                            new_monos[k] = _SR(nb, db) if not (nb.is_zero() and False) else Fr(0)
                            # 若分子为零则退化为 Fr(0)
                            if nb.is_zero():
                                new_monos[k] = Fr(0)
                    else:
                        raise PolyError("unsupported coeff type")
                g_beta = Poly(g.vars, new_monos)
                # 递归走单β Trager（避免重入多α分支）
                # 构造临时单α标签 bsym
                # 直接内联单扩张 Trager 逻辑（复用下文 flour）
                alpha = bsym
                # 覆盖 m 为 β 极小多项式
                fld_beta = beta_fld
                m_beta = fld_beta.minpoly_poly(alpha)
                # 清分母与 Norm 路径与单α同
                items2 = []
                for k, c2 in g_beta.monos.items():
                    if isinstance(c2, Fr):
                        items2.append((k, Poly((alpha,), {(0,): c2}), None))
                    elif isinstance(c2, SymRat):
                        items2.append((k, c2.num, c2.den))
                    else:
                        raise PolyError("coeff type")
                D2 = Poly.one((alpha,))
                for _, _num, den in items2:
                    if den is not None:
                        D2 = D2 * den
                coeffs2 = {k: (num * D2 if den is not None else num) for k, num, den in items2}
                two2 = (x, alpha)
                p2m2 = {}
                for k, cp in coeffs2.items():
                    for kk, vv in cp.monos.items():
                        p2m2[(k[0],) + kk] = vv
                norm2 = _norm_det(Poly(two2, p2m2), alpha, m_beta)
                if norm2.is_const() or norm2.degree(x) < 1:
                    return None
                _c0, irrs2 = factor(norm2)
                one_a2 = Poly.one((alpha,))
                pk2 = Poly((x,), {k: SymRat(cp, one_a2) for k, cp in coeffs2.items()})
                facs2 = []
                for h, _mult in irrs2:
                    gg2 = _kx_gcd(pk2, h, alpha, m_beta)
                    if gg2 is not None and gg2.degree(x) >= 1:
                        facs2.append(gg2)
                if not facs2:
                    return None
                total2 = sum(f_.degree(x) for f_ in facs2)
                if total2 != g_beta.degree(x):
                    return None
                monic2 = [f_.scalar(_rat_inv(f_.lc(x))) for f_ in facs2]
                return monic2, g_beta.lc(x)
            except Exception:
                return None
        except Exception:
            return None
    fld = ALG_FIELDS.get(alpha)
    m = fld.minpoly_poly(alpha) if fld is not None else None
    if m is None or m.degree(alpha) > 20:
        # FriCAS 最通用对齐：Bareiss O(n³) 后提至 20（理论无界）
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
        dom = _coeff_domain(g0)
        if dom == 'QI':
            facs_pc = _ga_factor(g0, x)
            if facs_pc is not None:
                facs, pc = facs_pc
                if pc is not None:
                    ctotal = _rat_mul(ctotal, pc)
                for h in facs:
                    sqf.append((h, k0))
                continue
            # QI 不可约回退 ℚ 分解（Norm 整体）
            c0, facs = factor(g0)
            ctotal = ctotal * c0
            for h, _ in facs:
                sqf.append((h, k0))
        elif dom in ('AN', 'MIXED'):
            # 代数/混域：Trager 仅高次（deg≥3）才有收益，二次走判别式路径
            # 保持与历史分派一致（避免 RootOf 回退形态变化）
            an = _an_factor(g0, x) if g0.degree(x) >= 3 else None
            if an is not None:
                facs, pc = an
                if pc is not None:
                    ctotal = _rat_mul(ctotal, pc)
                for h in facs:
                    sqf.append((h, k0))
                continue
            facs, pc = _param_factors(g0, x)
            if pc is not None:
                ctotal = _rat_mul(ctotal, pc)
            for h in facs:
                sqf.append((h, k0))
        elif dom == 'PARAMS':
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