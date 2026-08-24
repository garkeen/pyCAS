"""N3 落域判定 / denesting 核心原语（M78.4）。

职责（入域闸门链第②道的判定引擎）：判断代数域元素是否完全幂——

    perfect_power(x, k) ∈ 𝔄 ?   （x,y ∈ 𝔄, y^k = x）

算法（Groebner 坐标法，类完备）：设 𝔄=ℚ(θ)，deg=m，y = Σ u_i·θ^i
（u_i ∈ ℚ 未定元）。则
    ∃y: y^k = x  ⟺  ∃ 商式 q(t)：y(t)^k − x(t) − q(t)·m(t) ≡ 0。
引入未知元 (t, u_*, w_*)，差式按 t 幂展开的每个系数置零，得 ℚ 上
多项式方程组，交 groebner.solve_system（lex 消元 + 有理根回代）；
解得候选坐标后用 AlgElem 乘回精确验证。

三态诚实：
  ('yes', y)        —— 完全幂（已乘回验证）
  ('no', None)      —— 方程组无解（proved 非幂；可用范数预筛）
  ('unknown', None) —— 超出能力上限（次数/叶型/求解器不支持）

参照物：rsimp.spad RootSimplification（Borodin JSC1985 / Zippel
JSC1985）以候选多项式法解决同一问题于 ℚ(√r) 底 + 素数 k≤11；
此处取一般坐标方程路线以覆盖任意 binomial 塔层与复合 k，代价是
小规模限制（_DEG_CAP/_K_CAP，超限诚实 'unknown'）。

项级接入（√g 注册闸门的消费方）随 N6/B2 统一登记批次接线，
本模块保持纯函数、无副作用、不触碰 ALG_FIELDS。
"""

from fractions import Fraction as Fr

from cas.term import S, N, is_num, num_val
import cas.term as T
from cas.poly import Poly, PolyError
from cas.algfield import AlgElem, _z

_DEG_CAP = 5          # 域次数上限（Groebner 规模守卫）
_K_CAP = 7            # 指数上限


def perfect_power(elem, k):
    """x ∈ 𝔄 是否 k 次幂。返回 (verdict, y_or_None)。"""
    if not isinstance(elem, AlgElem) or k < 2 or k > _K_CAP:
        return 'unknown', None
    fld = elem.fld
    d = len(fld.m) - 1
    if d < 1 or d > _DEG_CAP or len(fld.m) != d + 1:
        return 'unknown', None
    # 本批限定全 Fr 叶（ℚ 塔层）；混合叶域诚实放弃
    m_coefs = []
    for c in fld.m:
        if isinstance(c, Fr):
            m_coefs.append(c)
        else:
            return 'unknown', None
    x_cs = list(elem.cs)
    while len(x_cs) < d:
        x_cs.append(Fr(0))
    for c in x_cs:
        if not isinstance(c, Fr):
            return 'unknown', None
    if elem.is_zero():
        return 'yes', fld.const(Fr(0))

    # 范数预筛（数学必然）：y^k = x ⟹ N(x) = N(y)^k 为有理数 k 次幂。
    # 不满足 ⟹ proved no，免进方程组。范数 = Res(m, x_poly)（ℚ 常数）。
    nrm = _norm_q(m_coefs, x_cs)
    if nrm is not None and not _is_kth_power_rat(nrm, k):
        return 'no', None

    # 有界精确枚举快路（小系数构造类；每个候选举 AlgElem 乘回验证，
    # 漏检只是落入后方通用路——诚实性不受影响）
    hit = _bounded_search(fld, elem, x_cs, d, k)
    if hit is not None:
        return 'yes', hit

    t = S("_den_t")
    us = [S(f"_den_u{i}") for i in range(d)]
    # 商式 q 的次数 = k(d−1) − d，系数个数 = 次数 + 1
    ws_n = max(k * (d - 1) - d + 1, 0)
    ws = [S(f"_den_w{j}") for j in range(ws_n)]

    # Groebner 后备规模闸（爆炸守卫）：快路未命中且系统过大 ⟹ 诚实
    # unknown（d=2 全 k、d=3 k≤2 在闸内；更大组合待分域专用算法）
    if ws_n > 3 or d * (ws_n + 1) > 9 or k > 5:
        return 'unknown', None

    def mono(sym, e):
        return sym if e == 0 else (sym if e == 1 else T.pw(sym, N(e)))

    def scaled(sym, c, e):
        ct = N(c)
        if e == 0:
            return ct
        return T.times(ct, mono(t, e)) if c != 1 else mono(t, e)

    y_t = T.plus(*[T.times(us[i], mono(t, i)) if i else us[i]
                   for i in range(d)])
    diff = T.plus(_expand_pow(y_t, k), T.neg(
        T.plus(*[scaled(t, cj, j) for j, cj in enumerate(x_cs) if cj != 0])
    ) if any(cj != 0 for cj in x_cs) else _expand_pow(y_t, k))
    if ws_n:
        q_t = T.plus(*[T.times(ws[j], mono(t, j)) if j else ws[j]
                       for j in range(ws_n)])
        m_t = T.plus(*[scaled(t, mc, i)
                       for i, mc in enumerate(m_coefs) if mc != 0])
        diff = T.plus(diff, T.neg(T.times(q_t, m_t)))
    diff = _expand(diff)

    vs = [t] + us + ws
    try:
        p = Poly.from_term(diff, tuple(vs))
    except PolyError:
        return 'unknown', None
    if p.is_zero():
        return 'unknown', None          # 全零：构造病态，不宣称

    ti = 0                               # t 的位置
    eqs_by_deg = {}
    for key, coef in p.monos.items():
        subkey = key[1:]
        acc = eqs_by_deg.setdefault(key[ti], {})
        acc[subkey] = acc.get(subkey, Fr(0)) + coef
    vs_rest = tuple(vs[1:])
    fs = []
    for e_t in sorted(eqs_by_deg):
        monos_f = {kk: vv for kk, vv in eqs_by_deg[e_t].items() if vv != 0}
        if not monos_f:
            continue
        fs.append(Poly(vs_rest, monos_f).to_term())

    status, sols = _solve(fs, vs_rest)
    if status == 'contradiction':
        return 'no', None               # 1 ∈ 理想：proved 非幂
    if status not in ('ok', 'partial', 'identity'):
        return 'unknown', None          # positive-dim / unsupported / 其他    seen = set()
    for sol in sols:
        # 契约：list[tuple(term)]，按 vars 顺序（groebner.SolveSysResult）
        if len(sol) != len(vs_rest):
            continue
        valmap = dict(zip(vs_rest, sol))
        coords = []
        for u in us:
            v = valmap.get(u)
            if isinstance(v, Fr):
                coords.append(v)
            elif is_num(v):
                nv = num_val(v)
                if isinstance(nv, Fr):
                    coords.append(nv)
                else:
                    coords = None
                    break
            else:
                coords = None
                break
        if coords is None:
            continue
        key = tuple(coords)
        if key in seen:
            continue
        seen.add(key)
        cand = AlgElem(fld, list(coords))
        if _elem_eq((cand ** k).cs, elem.cs):
            return 'yes', cand
    return 'unknown', None


def _expand(t):
    from cas.simplify import expand
    return expand(t)


def _norm_q(m_coefs, x_cs):
    """N(x) = Res(m, x_poly)，ℚ 常数；不可靠（大素数）返回 None。"""
    try:
        from cas.poly import uresultant

        tv = S("_den_T")
        pm = Poly((tv,), {(i,): c for i, c in enumerate(m_coefs) if c != 0})
        px = Poly((tv,), {(i,): c for i, c in enumerate(x_cs) if c != 0})
        r = uresultant(pm, px)
        if isinstance(r, Fr):
            return r
        return None
    except Exception:
        return None


def _is_kth_power_rat(f, k):
    """f 是否有理数 k 次幂（素重数全整除 + 符号）；大数诚实 False
    仅当符号已违——分解不出时返回 True（跳过预筛，不误杀）。"""
    if f == 0:
        return True
    if f < 0 and k % 2 == 0:
        return False
    from cas.radnorm import _factor_int

    for part in (abs(f.numerator), abs(f.denominator)):
        if part == 1:
            continue
        fac = _factor_int(part)
        if fac is None:
            return True               # 分解不出：放弃预筛（不误杀）
        if any(e % k for e in fac.values()):
            return False
    return True


def _bounded_search(fld, elem, x_cs, d, k, box=None):
    """小系数有理坐标的精确枚举（逐候选举 AlgElem 乘回验证）。

    界自适应输入量级；漏检安全落入通用路。返回根 AlgElem 或 None。
    """
    import itertools

    mag = max(abs(c.numerator) + c.denominator for c in x_cs)
    b = box if box is not None else min(16, int(round(mag ** (1.0 / k))) + 3)
    dens = (Fr(1), Fr(2), Fr(3))
    zero = Fr(0)
    seen = set()
    for combo in itertools.product(range(-b, b + 1), repeat=d):
        if all(v == 0 for v in combo):
            continue
        for den in dens:
            coords = [Fr(v) / den for v in combo]
            key = tuple(coords)
            if key in seen:
                continue
            seen.add(key)
            cand = AlgElem(fld, list(coords))
            if _elem_eq((cand ** k).cs, elem.cs):
                return cand
    return None


def _expand_pow(base_t, k):
    acc = N(1)
    for _ in range(k):
        acc = _expand(T.times(acc, base_t))
    return acc


def _solve(fs, vars_):
    """solve_system 包装 -> (status, sols)。"""
    from cas.groebner import solve_system
    r = solve_system([T.mk(S("Eq"), (f, N(0))) for f in fs],
                     list(vars_))
    sols = getattr(r, "solutions", None)
    if sols is None:
        try:
            unpacked = r[0]
            st = r[1] if len(r) > 1 else ""
            return str(st), unpacked
        except Exception:
            return "unsupported", []
    st = getattr(r, "status", "")
    return (st if isinstance(st, str) else str(st)), sols


def _elem_eq(a, b):
    la = list(a) + [Fr(0)] * (len(b) - len(a))
    lb = list(b) + [Fr(0)] * (len(a) - len(b))
    return all(_z(x - y) for x, y in zip(la, lb))
