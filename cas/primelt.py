"""N9 本原元压缩（M78.5）。

参照物：primelt.spad PrimitiveElement（Bronstein）——两生成元
resultant 法：试小整数 c，R(u)=Res_γ(A(u−cγ), B)，squarefree 判
据定本原；FunctionSpace 版回传 β 与极小多项式。

对源码的两处强化（notes.md N9 条目有账）：
  1. 接受判据：源码要求 r == squareFreePart(r)，在依赖退化域
     （ℚ(∛2,∛4) 类，合成次数 < 乘积次数）永不触发而无限循环；
     此处恒取 squarefree 部 S，本原性改由「生成元精确表出 +
     极小性回验 m_γ(f(β)) ≡ 0」裁决，验败换 c 重试。
  2. 表达式回收：源码两生成元版不回传 ai=qᵢ(a)；此处用迹线性系
     ——Hankel 矩阵取 m_β 的幂和（牛顿恒等式），右端 Tr(γ·βˡ)
     取乘积幂和（独立嵌入下 Tr(αᵘγᵛ)=sᵤ·sᵥ），ℚ 上精确消元，
     零数值猜测。

诚实边界：>2 生成元不收（链式可扩，当前无消费者）；全部 c 尝试
失败返回 None，调用方诚实降级；本模块纯函数、零全局登记。
"""

from fractions import Fraction as Fr
from math import comb

from cas.term import S, N, is_num, num_val
import cas.term as T
from cas.poly import Poly, sqrfree_mults


def _shift_subst(P, t_, u_, g_, c):
    """α := u − c·γ：单变量 Fr 系数 P(α) -> 双变量 (u,g)。"""
    out = {}
    for (i,), cf in P.monos.items():
        for r in range(i + 1):
            k = i - r
            v = cf * Fr(comb(i, r)) * ((-Fr(c)) ** k)
            key = (r, k)
            out[key] = out.get(key, Fr(0)) + v
    return Poly((u_, g_), {k: v for k, v in out.items() if v != 0})


def _col(P2, jdeg, u_):
    """双变量 Poly 的 g^jdeg 系数（u 多项式）。"""
    mm = {}
    for k_, cf in P2.monos.items():
        if k_[1] == jdeg and cf != 0:
            mm[(k_[0],)] = cf
    return Poly((u_,), mm)


def _res_gamma(A2, B2, u_, g_):
    """Res_g(A2,B2)：Sylvester 行列式，条目统一 u 多项式。"""
    from cas.apart import _det_bareiss
    da = A2.degree(g_)
    db = B2.degree(g_)
    if da < 1 or db < 1:
        return None
    A_desc = [_col(A2, j, u_) for j in range(da, -1, -1)]
    B_desc = [_col(B2, j, u_) for j in range(db, -1, -1)]
    zero = Poly((u_,), {})
    M = []
    for r0 in range(db):
        row = [zero] * (da + db)
        row[r0:r0 + da + 1] = A_desc
        M.append(row)
    for r0 in range(da):
        row = [zero] * (da + db)
        row[r0:r0 + db + 1] = B_desc
        M.append(row)
    return _det_bareiss(M)


def _sqfree_part(R):
    _c, facs = sqrfree_mults(R)
    S = Poly.one(R.vars)
    for f, _m in facs:
        S = S * f
    return S


def _gauss(Amat, bvec):
    """ℚ 上高斯消元（部分主元）。奇异返回 None。"""
    n = len(bvec)
    M = [list(Amat[i]) + [bvec[i]] for i in range(n)]
    for col in range(n):
        piv = max(range(col, n), key=lambda r: abs(M[r][col]))
        if M[piv][col] == 0:
            return None
        M[col], M[piv] = M[piv], M[col]
        pv = M[col][col]
        M[col] = [v / pv for v in M[col]]
        for r in range(n):
            if r != col and M[r][col] != 0:
                f = M[r][col]
                M[r] = [a - f * bb for a, bb in zip(M[r], M[col])]
    return [M[i][n] for i in range(n)]


def _power_sums(coefs, upto):
    """s_0..s_upto（s_0=次数）。复用 AlgField 牛顿幂和。"""
    from cas.algfield import af_q
    fld = af_q([Fr(x) for x in coefs])
    ps = fld.pow_sums(upto)
    return [Fr(len(coefs) - 1)] + [Fr(x) for x in ps]


def express_gen(S_coefs, mA, mB, c, which):
    """把 α（which='A'）或 γ（'B'）表为 f(β) 的 ℚ 系数向量。

    β = α + c·γ。线性系：Σⱼ aⱼ·s_{j+l}(m_β) = Tr(gen·βˡ)，
    右端按二项式展开折成乘积幂和。解后精确回验。"""
    d = len(S_coefs) - 1
    sS = _power_sums(S_coefs, 2 * d)
    sA = _power_sums(mA, 2 * d + 1)
    sB = _power_sums(mB, 2 * d + 1)
    Amat = [[sS[j + l] for l in range(d)] for j in range(d)]
    bvec = []
    for l in range(d):
        acc = Fr(0)
        for u in range(l + 1):
            v = l - u
            w = Fr(comb(l, u)) * (Fr(c) ** v)
            if which == 'A':
                acc += w * sA[u + 1] * sB[v]
            else:
                acc += w * sA[u] * sB[v + 1]
        bvec.append(acc)
    sol = _gauss(Amat, bvec)
    if sol is None:
        return None
    # 精确回验：m_gen(f(β)) ≡ 0 于 ℚ(β)
    from cas.algfield import af_q
    fld = af_q([Fr(x) for x in S_coefs])
    gen = fld.gen()
    f_el = fld.zero
    for j, a in enumerate(sol):
        if a != 0:
            f_el = f_el + fld.const(a) * (gen ** j)
    target = mA if which == 'A' else mB
    val = fld.const(Fr(0))
    for cc in reversed(target):
        val = val * f_el + fld.const(cc)
    if not val.is_zero() or f_el.is_zero():
        return None
    return [Fr(a) for a in sol]


def primitive_pair(mA, mB, cap=12):
    """两生成元压缩。mA/mB：首一 Fr 升序系数表。
    返回 (S_coefs, c, mapA, mapB) 或 None。"""
    t_ = S('_pm_t')
    A = Poly((t_,), {(i,): Fr(v) for i, v in enumerate(mA) if v != 0})
    B = Poly((t_,), {(i,): Fr(v) for i, v in enumerate(mB) if v != 0})
    u_ = S('_pm_u')
    g_ = S('_pm_g')
    for c in range(1, cap + 1):
        A2 = _shift_subst(A, t_, u_, g_, c)
        B2 = Poly((u_, g_), {(0, j): Fr(v)
                             for j, v in enumerate(mB) if v != 0})
        try:
            R = _res_gamma(A2, B2, u_, g_)
        except Exception:
            continue
        if R is None or R.is_zero():
            continue
        try:
            Sq = _sqfree_part(R)
        except Exception:
            continue
        d = Sq.degree(u_)
        if d < max(len(mA) - 1, len(mB) - 1):
            continue
        Scoefs = [Sq.monos.get((i,), Fr(0)) for i in range(d + 1)]
        # 不可约性门：sqfree 部仍可缩（依赖退化域的独立结果式会给出
        # 分支乘积），乘积环上「回验」会假阳性——非域即拒
        from cas.algfield import af_q as _afq, af_irreducible_q
        if af_irreducible_q(_afq([Fr(x) for x in Scoefs])) is not True:
            continue
        mapA = express_gen(Scoefs, mA, mB, c, 'A')
        if mapA is None:
            continue
        mapB = express_gen(Scoefs, mA, mB, c, 'B')
        if mapB is None:
            continue
        return Scoefs, c, mapA, mapB
    return None


def compress_chain(ms, terms, cap=8):
    """m 生成元链式压缩（N9 通用入口）。

    ms：首一 Fr 升序极小多项式表；terms：对应生成元的原始项。
    返回 (S_coefs, maps, beta_term)：
      S_coefs —— 最终本原元 β 的极小多项式（不可约已验）
      maps    —— 每个原始生成元在 ℚ(β) 的系数表（Fr，升序）
      beta_term —— β 的项级形态（线性组合沿链携带）
    任一步不可约门/回验失败 ⟹ None（诚实降级）。"""
    from cas.algfield import af_q
    if len(ms) != len(terms) or not ms:
        return None
    cur = list(ms[0])
    term_cur = terms[0]
    maps = [list(map(Fr, [0, 1]))]
    for idx in range(1, len(ms)):
        res = primitive_pair(cur, ms[idx], cap)
        if res is None:
            return None
        Scoefs, c, mapCur, mapNext = res
        # 旧生成元表达式经 mapCur 复合到新 β（域算术求值后取系数）
        fld_step = af_q([Fr(x) for x in Scoefs])
        gnew = fld_step.gen()

        def evalmap(mp):
            e = fld_step.zero
            for cc in reversed(mp):
                e = e * gnew + fld_step.const(cc)
            return e

        d = len(Scoefs) - 1
        newmaps = []
        for mp in maps:
            e = fld_step.zero
            for cc in reversed(mp):
                e = e * evalmap(mapCur) + fld_step.const(cc)
            v = list(e.cs) + [Fr(0)] * (d - len(e.cs))
            newmaps.append(v)
        newmaps.append(mapNext)
        maps = newmaps
        # 新 β 项级形态 = mapCur(旧 β)：经旧域 origin 回化
        fld_prev = af_q([Fr(x) for x in cur], origin=term_cur)
        gold = fld_prev.gen()
        e_old = fld_prev.zero
        for cc in reversed(mapCur):
            e_old = e_old * gold + fld_prev.const(cc)
        term_cur = e_old.to_term()
        cur = Scoefs
    return cur, maps, term_cur
