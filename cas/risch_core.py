# -*- coding: utf-8 -*-
"""微分域塔·核心（自 cas/risch.py 拆出）：DiffExt 塔构建、derivation、
term<->塔双向转换、三角复指数化、代数常数登记、出口收缩。

参照：Bronstein《Symbolic Integration I》第 4-6 章；sympy risch.py 的
DifferentialExtension（level/case 结构）；maxima risch.lisp。

拆分布局（M6.7）：
    risch_core   本模块——塔地基（本文件）
    risch_exp    exp 层积分（Hermite 推广+RT 残数）+ 实化配对
    risch_rdesup RDE 支撑（weak normalization / split / limited_integrate）
    risch_prde   参数化对数导数判定（_pld_solve 三态）
    risch_rde    塔上 RDE 完备判定求解器 + 频率分量
    risch        门面 + 递归驱动（_risch_rec/_integrate_in_K）

诚实边界：代数依赖（exp(log(x)/2)）、嵌套超越参数（exp(x*e^x)）、
三角函数输入一律 RischUnsupported 拒绝——绝不静默错。
"""

from fractions import Fraction as Fr
from math import gcd

from cas import term as T
from cas.term import S, N, Expr, Sym, Const, Int, ONE, IU, is_num, num_val
from cas.poly import Poly, SymRat
from cas.errors import PolyError
from cas.gaussian import Ga
from cas.univar import (from_poly, u_add, u_sub, u_mul0, u_mul,
                        u_neg, u_pow, u_deg, u_trim, u_divmod, u_gcd,
                        u_xgcd, u_inv_mod, u_inv_mod_t, u_is_zero,
                        u_deriv_x, u_formal_deriv, u_diophantine,
                        u_gauss_solve_k)
from cas.scalarutil import (rf_const_ga, ga_den, lcm2,
                            ga_vec_to_ints, mk_zero_like,
                            leaf_has_ga, symrat_has_ga,
                            coef_zero, coef_re_im, poly_re_im)


class RischUnsupported(Exception):
    """塔构建失败（携带原因，诚实拒答的载体）。"""

    def __init__(self, reason):
        super().__init__(reason)
        self.reason = reason


class RischNonElementary(Exception):
    """不可初等证明载体（Bronstein 决策程序的否定结论）。"""

    def __init__(self, reason):
        super().__init__(reason)
        self.reason = reason


class DiffExt:
    """微分域塔 K_0 < K_1 < ... < K_n，K_0 = Q(x)。

    levels[i]：塔变量（levels[0] = 积分变量 x）；
    cases[i]：'base' | 'exp' | 'primitive' | 'algebraic'；
    ws[i]：RatFunc（K_{i-1} 上）——exp: D(t_i) = w*t_i；
    primitive: D(t_i) = w；algebraic: 同 exp 形态 D(t_i) = w*t_i
      （w = D(M)/(q·M)，M = 极小多项式首一多项式部分）；
    terms[i]：塔变量的原函数形态（backsubs 用，如 Exp(x/2)、Log(x)）；
    minpolys[i]：algebraic 层专用——(q, M) 其中 M ∈ K_{i-1}[t_i] 首一，
      塔不变量 = 全部代数层变量指数 < q（_ta_reduce 维护）。
    """

    __slots__ = ("levels", "cases", "ws", "terms", "minpolys")

    def __init__(self, x):
        self.levels = [x]
        self.cases = ["base"]
        self.ws = [None]
        self.terms = [x]
        self.minpolys = [None]

    @property
    def vars(self):
        return tuple(self.levels)

    def add(self, case, w, term, name_hint, mp=None):
        t = _fresh_sym(self.levels, name_hint)
        self.levels.append(t)
        self.cases.append(case)
        self.ws.append(w)
        self.terms.append(term)
        self.minpolys.append(mp)
        return t

    def dpair(self, j, all_vars):
        """D(levels[j]) 作为 all_vars 上的 (num, den) 分式。"""
        if self.cases[j] == "base":
            return Poly.const(all_vars, Fr(1)), Poly.one(all_vars)
        w = self.ws[j]
        wn = _embed(w.p, all_vars)
        wd = _embed(w.q, all_vars)
        if self.cases[j] in ("exp", "algebraic"):
            tj = _embed(Poly.mono(all_vars, self.levels[j], 1), all_vars)
            return _rmul_polys(wn, wd, tj, Poly.one(all_vars))
        return wn, wd


def _ta_reduce(p, de):
    """塔不变量维护：p（Poly on de.vars）逐 algebraic 层做 θ^q → M 余式。

    代数层的极小多项式给出商环结构——所有塔上算术的出口都保持
    各代数变量次数 < q 的规范形（M78 合并地基；与 exp/primitive 层
    的超越无关性不同，这里的关系必须显式约简）。
    """
    for j, case in enumerate(de.cases):
        if case != "algebraic" or p.is_zero():
            continue
        tj = de.levels[j]
        if tj not in p.vars:
            continue
        q_, mp_low = de.minpolys[j]
        rest = tuple(v for v in p.vars if v is not tj)
        mf = {}
        for k, c in mp_low.monos.items():
            mf[k] = _embed(c, rest)
        from cas.poly import _reduce_alg_var
        p = _reduce_alg_var(p, tj, Poly((tj,) + rest, mf))
    return p


# ---------------------------------------------------------------------------
# 分式助手（塔元素的 (num, den) 代数；den monic 化由 cancel 保证）
# ---------------------------------------------------------------------------

def _embed(p, all_vars):
    """Poly(子集变量) -> Poly(all_vars)（缺失维度指数置零）。"""
    if p.vars == tuple(all_vars):
        return p
    idx = [all_vars.index(v) for v in p.vars]
    out = {}
    for k, c in p.monos.items():
        nk = [0] * len(all_vars)
        for i, j in enumerate(idx):
            nk[j] = k[i]
        out[tuple(nk)] = c
    return Poly(all_vars, out)


def _rmul_polys(an, ad, bn, bd):
    """(an/ad)*(bn/bd)，约化。"""
    n = an * bn
    d = ad * bd
    return _cancel(n, d)


def _cancel(n, d):
    """轻量规范：常数 content 约化 + 分母 monic。

    多项式 gcd 约化不在 M5.0 范围（Hermite 推广在 M5.1 正规处理）；
    此处只防分式代数的系数膨胀。含域系数（Ga/SymRat，或混合——
    Poly 构造把常量 SymRat 退化回 Fr，同一多项式可两种并存）时
    content 已是单位元，仅 monic 化用域除法。
    """
    if n.is_zero():
        return Poly.zero(n.vars), Poly.one(n.vars)
    cn, cd = n.content(), d.content()
    if not (isinstance(cn, Fr) and isinstance(cd, Fr)):
        # 域/混合系数路径
        lc = d.lc(d.vars[0])
        inv = Fr(1) / lc if isinstance(lc, Fr) else 1 / lc
        n = n.scalar(inv)
        d = d.scalar(inv)
        return n, d
    c = _fr_gcd(cn, cd)
    if c != 0 and c != 1:
        n = n.scalar(Fr(1) / c)
        d = d.scalar(Fr(1) / c)
    lc = d.lc(d.vars[0])
    if lc != 1:
        n = n.scalar(Fr(1) / lc)
        d = d.scalar(Fr(1) / lc)
    return n, d


def _fr_gcd(a, b):
    from math import gcd as _g

    if a == 0:
        return abs(b)
    if b == 0:
        return abs(a)
    n = _g(abs(a.numerator), abs(b.numerator))
    d = a.denominator * b.denominator // _g(a.denominator, b.denominator)
    return Fr(n, d)


def _radd(a, b):
    """(an,ad)+(bn,bd)。"""
    an, ad = a
    bn, bd = b
    if an.is_zero():
        return b
    if bn.is_zero():
        return a
    return _cancel(an * bd + bn * ad, ad * bd)


# ---------------------------------------------------------------------------
# 收集与归组
# ---------------------------------------------------------------------------

def _collect_exts(t):
    """显式栈遍历：收集 (Exp 参数项集合, Log 参数项集合)。"""
    exps, logs = [], []
    seen = set()
    stack = [t]
    while stack:
        u = stack.pop()
        if id(u) in seen:
            continue
        seen.add(id(u))
        if isinstance(u, Expr):
            n = u.head.name
            if n == "Exp" and len(u.args) == 1:
                exps.append(u.args[0])
            elif n == "Log" and len(u.args) == 1:
                logs.append(u.args[0])
            stack.extend(u.args)
    return exps, logs


# ---------------------------------------------------------------------------
# M5.3：三角/双曲经复指数（trigs2explogs 同款前置重写）
#
# Sin(u) = (e^{iu} − e^{−iu})/(2i)、Cos(u) = (e^{iu} + e^{−iu})/2、
# Tan = Sin/Cos；Sinh/Cosh/Tanh 同构（无 i）。自底向上递归；
# 虚单位为保留符号 i（Poly._build/_frac_num 识别为 Ga 常量，i²=−1
# 关系由此保留——升参数会破坏它）。
# ---------------------------------------------------------------------------

_TRIG_HEADS = ("Sin", "Cos", "Tan", "Cot", "Sec", "Csc",
               "Sinh", "Cosh", "Tanh")


def _param_provisos(expr, x):
    """答案中纯参数分母 -> [Ne(D,0)] 条件声明（M5.6#4 阶段一）。

    generic 答案在参数退化点（如 e^{ax}/a 的 a=0）无定义而原函数
    存在——静默输出即撒谎，必须声明成立条件。参数 = 分母中非 x、
    非保留名 i 的自由符号；含 x 的分母属有理积分极点语义不在此列；
    Log(常量)/数值分母是真实非零常数亦排除。
    """
    provs = []
    seen = set()
    stack = [expr]
    while stack:
        v = stack.pop()
        if isinstance(v, Expr) and getattr(v, "head", None) is not None:
            n = v.head.name
            if n == "Power" and isinstance(v.args[1], T.Int) \
                    and v.args[1].v < 0:
                base = v.args[0]
                fv = T.free_vars(base) - {S("i")}
                if fv and x not in fv and base not in seen:
                    seen.add(base)
                    provs.append(T.mk(S("Ne"), (base, T.ZERO)))
            stack.extend(v.args)
    return provs


def _exp_of(tt):
    return T.mk(S("Exp"), (tt,))


# 代数常数关系登记（M5.4 切片 a → M7.0-b 迁移）：符号 -> AlgField
# （极小多项式/出处键/区间全在域对象上，单一来源 cas.algfield）。
_ALG_RADICAL_COUNTER = [0]
_NCPOW_COUNTER = [0]


def _collect_radical(pterm, subs, xv=None):
    """正有理指数幂 b^(p/q) -> 代数常数符号 + AlgField 登记。

    P3/B2：建域与去重收敛至 kernelreg（register_numeric_radical /
    register_symbolic_radical），本函数降级为项级消费者适配——
    解析底、分流、把结果写入调用方 subs 字典。语义与原实现逐条
    保持（含可约二项式的 RischUnsupported 诚实拒答、变元底/嵌套
    底不登记的 M7.3 边界）。
    """
    b, e = pterm.args
    if not (isinstance(e, T.Rat)) or e.f <= 0 or e.f == 1 \
            or e.f.denominator == 1:
        return
    p_, q_ = e.f.numerator, e.f.denominator
    from cas.kernelreg import register_numeric_radical, \
        register_symbolic_radical

    if T.is_num(b):
        bv = T.num_val(b)
        sym = register_numeric_radical(bv, p_, q_, origin=pterm)
        if sym is not None:
            subs[pterm] = sym
        return

    # ---- 符号底（ℚ(params) 元素，M7.2） -----------------------------
    if xv is None or xv in T.free_vars(b):
        return                  # 无变量语境 / 变元底：不登记（M8 属塔层）
    from cas.poly import Poly, SymRat
    try:
        gp = Poly.from_term(b, ())
    except PolyError:
        return                  # 嵌套根式/超越项底（M7.3 边界）：不登记
    leaf = gp.const_val()
    if isinstance(leaf, SymRat):
        num, den = leaf.num, leaf.den
    elif isinstance(leaf, Fr):
        num, den = Poly((), {(): leaf}), Poly((), {(): Fr(1)})
    else:
        return                  # Ga 底等（M7.3 边界）：不登记
    sym = register_symbolic_radical(num, den, p_, q_, origin=pterm)
    if sym is not None:
        subs[pterm] = sym


def _const_blockage_hint(f, xv=None):
    """被积函数含命名常数/非常量域超越常量时的 Richardson 卡点提示。

    π、e、γ 类命名常数与 sin(1)、e² 类未求值超越项目前不在任何精确
    常数域中（零等价不可判定，Richardson）——塔覆盖失败时如实点名：
    这是数学边界而非实现缺陷；M5.6#1 参数化通道可部分解锁。
    """
    from cas.pprint import to_str
    # M6.7 缺陷修复：本函数原引用 simplify 却从未导入（主路径测试
    # 不经此提示分支，NameError 潜伏至拆分审计才暴露）
    from cas.simplify import simplify

    from cas.spec import iter_constants
    named = {c.name for c in iter_constants("transcendental-named")}
    names = []
    tconsts = set()
    seen = set()
    stack = [f]
    while stack:
        v = stack.pop()
        if id(v) in seen:
            continue
        seen.add(id(v))
        if isinstance(v, Const):
            nm = getattr(v, "name", "")
            if nm in named and nm not in names:
                names.append(nm)
            continue
        if isinstance(v, Expr) and getattr(v, "head", None) is not None:
            n = v.head.name
            if n in ("Sin", "Cos", "Tan", "Atan") and not T.free_vars(v):
                tconsts.add(to_str(simplify(v)))
            stack.extend(v.args)      # 深入找嵌套常数（如 e^{πx} 里的 π）
    if not names and not tconsts:
        return ""
    parts = []
    if names:
        parts.append("named constants {" + ",".join(names) + "}")
    if tconsts:
        parts.append("transcendent terms {"
                     + ",".join(sorted(tconsts)) + "}")
    return (" [constant problem: " + "; ".join(parts)
            + " outside exact coefficient domains; zero-equivalence "
            "undecidable in general (Richardson); partial unlock via "
            "M5.6#1 parametrization]")


def _lin_exp_freq(tt, x):
    """Exp 参数 tt -> 频率 γ（常数项 × x 的 γ），非该形态返回 None。

    保留名 i（虚单位）不算自由变量——塔内复指数系数天然含它。
    """
    fv = T.free_vars(tt) - {S("i")}
    if fv != {x}:
        return None
    # γ = tt / x：用 RatFunc 除法取常数商
    from cas.ratfunc import RatFunc
    try:
        rf = RatFunc.from_term(tt, (x,)) / RatFunc.from_term(x, (x,))
    except Exception:
        return None
    if not rf.is_const():
        return None
    cv = rf.const_val()
    if isinstance(cv, Fr):
        cv = Ga(cv, Fr(0))
    return cv


def _ef_contract(t):
    """exp-log 收缩（M5.3 出口扩展；FriCAS elemntry.spad iiilog 同款）。

    Exp(k·Log(u)) -> Power(u,k)，k∈ℤ 无条件精确（整数幂单值，
    e^{Log z}=z 为定义）；k=1 隐式同款。分支敏感的 Log(Exp(u)) 不在此
    处理（需实性门控，走账本 refine 通道）。
    """
    head = getattr(t, "head", None)
    if head is None:
        return t
    args = tuple(_ef_contract(a) for a in t.args)
    if head.name == "Exp":
        u = args[0]
        # 拆因子找有理数倍 Log（k∈ℚ 与本系统 Power 主支语义一致——
        # 变指数幂归一本就把 b^e 定义为 Exp(e·Log b)，往返恒等）
        if isinstance(u, Expr) and u.head.name == "Times":
            k = Fr(1)
            logs = []
            rest = []
            for fac in u.args:
                if isinstance(fac, (Int, T.Rat)):
                    k *= fac.f if isinstance(fac, T.Rat) else Fr(fac.v)
                elif isinstance(fac, Expr) and fac.head.name == "Log":
                    logs.append(fac.args[0])
                else:
                    rest.append(fac)
            if logs and not rest and len(logs) == 1 and k != 0:
                return T.pw(logs[0], N(k))
        if isinstance(u, Expr) and u.head.name == "Log":
            return T.pw(u.args[0], ONE)
    return T.mk(head, args)


def _ef_expand_trans(t):
    """超越头的参数做环层展开（expand 不深入非环节点——log 参数内的
    多项式差不展开则塔看到的是伪装形态）。"""
    head = getattr(t, "head", None)
    if head is None:
        return t
    args = tuple(_ef_expand_trans(a) for a in t.args)
    u = T.mk(head, args)
    if head.name in ("Log", "Sin", "Cos", "Tan", "Atan",
                     "Sinh", "Cosh", "Tanh"):
        from cas.simplify import simplify as _s, expand as _e

        try:
            u = T.mk(head, (_s(_e(u.args[0])),))
        except Exception:
            pass
    return u


def _neg_term(tt):
    return T.mk(S("Times"), (N(-1), tt))


def _iu(u):
    """i·u 与 −i·u 的 term。"""
    iu = T.mk(S("Times"), (T.S("i"), u))
    return iu, _neg_term(iu)


def trigs_to_exp(t):
    """三角/双曲函数 -> 复指数有理式（无三角头则原样返回）。"""
    if not isinstance(t, Expr):
        return t
    n = t.head.name
    if len(t.args) == 1 and n in _TRIG_HEADS:
        u = trigs_to_exp(t.args[0])
        if n in ("Sin", "Cos", "Tan", "Cot", "Sec", "Csc"):
            iu, niu = _iu(u)
            e1, e2 = _exp_of(iu), _exp_of(niu)
            if n == "Sin":
                return T.div(T.plus(e1, _neg_term(e2)),
                             T.times(N(2), T.S("i")))
            if n == "Cos":
                return T.div(T.plus(e1, e2), N(2))
            c1 = T.div(T.plus(e1, _neg_term(e2)),
                       T.times(N(2), T.S("i")))
            c2 = T.div(T.plus(e1, e2), N(2))
            if n == "Tan":
                return T.div(c1, c2)
            if n == "Cot":
                return T.div(c2, c1)
            if n == "Sec":
                return T.pw(c2, N(-1))
            return T.pw(c1, N(-1))       # Csc
        eu, enu = _exp_of(u), _exp_of(_neg_term(u))
        if n == "Sinh":
            return T.div(T.plus(eu, _neg_term(enu)), N(2))
        if n == "Cosh":
            return T.div(T.plus(eu, enu), N(2))
        return T.div(T.plus(eu, _neg_term(enu)), T.plus(eu, enu))
    if t.args:
        return T.mk(t.head, tuple(trigs_to_exp(a) for a in t.args))
    return t


def _as_real_rat(q):
    """q -> 纯实有理数 Fr（可作指数幂次归组），否则 None。

    域感知：Fr/int 直取；Ga 仅实部纯 ℚ 时取 re；SymRat 仅常数且
    两端纯 ℚ 时相除。参数依赖比值（如 γ 与 2γ 的 2）经常数退化
    自然到达，真参数比（γ/δ 类）诚实 None——独立基处理。
    """
    if isinstance(q, Fr):
        return q
    if isinstance(q, int):
        return Fr(q)
    if isinstance(q, Ga):
        if q.is_real() and isinstance(q.re, Fr):
            return q.re
        return None
    if isinstance(q, SymRat):
        if q.num.is_const() and q.den.is_const():
            n_, d_ = q.num.const_val(), q.den.const_val()
            if isinstance(n_, Fr) and isinstance(d_, Fr):
                return n_ / d_
        return None
    return None


def _group_integer_powers(args):
    """Fr 倍数关系归组（sympy integer_powers 同款）。

    返回 [(base_arg, [(arg, mult)])]，mult 为整数且组内互素
    （content = 1，基取最大合法形态）。
    """
    groups = []
    for a in args:
        placed = False
        for base, members in groups:
            q = _ratio(a, base)
            if q is None:
                continue
            qr = _as_real_rat(q)
            if qr is None:
                continue      # 非实有理倍数（i 倍/参数比）= 独立基
            members.append((a, qr))
            placed = True
            break
        if not placed:
            groups.append((a, [(a, Fr(1))]))
    out = []
    for base, members in groups:
        k = 1
        for _, q in members:
            k = k * q.denominator // gcd(k, q.denominator)
        mults = [int(q * k) for _, q in members]
        g = 0
        for m in mults:
            g = gcd(g, abs(m))
        g = g or 1
        # 新基 = base * g/k（倍数 m/g 全整数且互素）
        new_base = _scale_arg(base, Fr(g, k))
        out.append((new_base, list(zip([a for a, _ in members], [m // g for m in mults]))))
    return out


def _ratio(a, b):
    """a/b 是 Fr 则返回，否则 None（Q(x) 上：pb 整除 pa 且商为常数）。"""
    pa = _try_qx(a)
    pb = _try_qx(b)
    if pa is None or pb is None or pb.is_zero():
        return None
    qa, ra = pa.udivmod(pb)
    if not ra.is_zero() or not qa.is_const():
        return None
    return qa.const_val()


def _scale_arg(arg, c):
    """arg 的 Fr 倍（保驻留形态）。"""
    return T.mk(S("Times"), (arg, N(c))) if c != 1 else arg


def _try_qx(t):
    """term -> Poly((x,)) 或 None（非 Q(x) 有理函数形态）。"""
    try:
        return Poly.from_term(t, (T.S("x"),))
    except PolyError:
        return None


def _fresh_sym(levels, hint):
    used = {v.name for v in levels}
    if hint not in used:
        return S(hint)
    i = 1
    while f"{hint}{i}" in used:
        i += 1
    return S(f"{hint}{i}")


# ---------------------------------------------------------------------------
# 塔构建
# ---------------------------------------------------------------------------

def _tower_deriv_frac(nn, nd, de):
    """D(nn/nd) 在塔上的 RatFunc（nn, nd: Poly(de.vars)）。"""
    from cas.ratfunc import RatFunc

    an, ad = derivation(nn, de)
    bn, bd = derivation(nd, de)
    num = an * bd * nd - nn * bn * ad
    den = ad * bd * nd * nd
    return RatFunc(num, den)


def _tower_logderiv(nn, nd, de):
    """D(nn/nd)/(nn/nd)（primitive 层 w = u'/u）在塔上的 RatFunc。"""
    from cas.ratfunc import RatFunc

    an, ad = derivation(nn, de)
    bn, bd = derivation(nd, de)
    num = an * bd * nd - nn * bn * ad
    den = ad * bd * nn * nd     # 注意分母含 nn——除以 u 本身
    return RatFunc(num, den)


def build_extension(f, x):
    """term -> (DiffExt, fa, fd)：f 在塔上的 (num, den) 表示。

    建塔顺序 log 先 exp 后（sympy handle_first='log' 同款：primitive
    在下、超指数在外）。参数重写到当前塔上表示（M5.2b 多层：log(log x)
    类嵌套合法）；参数非塔上有理函数 -> RischUnsupported。
    """
    from cas.ratfunc import RatFunc

    # M7.2 诚实守卫：符号底根式常数（√(a²−4) 类，key[0]=='sym'）已
    # 参数化为 _ak 时，塔上系数域实为 ℚ(a)[α]——当前 RatFunc 系数层
    # 无商环感知算术，残数/gcd 链会次数爆炸（实测挂死级）。在进入
    # 塔机制前如实拒答，等待系数域升格（M8.1 代数层提前）。数值底
    # （√2 类，key[0]=='num'）系数仍是标量叶，不触发。
    from cas.algfield import ALG_FIELDS
    sym_rad = {s for s, fld in ALG_FIELDS.items()
               if fld.key is not None and fld.key[0] == "sym"}
    if sym_rad and (sym_rad & T.free_vars(f)):
        raise RischUnsupported(
            "symbolic-radical constant coefficients pending "
            "coefficient-field upgrade (M8.1 algebraic tower layer)")

    # N5 统一投影服务（M78.5）：expr→(CoeffDomain,KernelSet) 单源，建塔前预投影
    try:
        from cas.kernel_proj import projection as _proj
        _ = _proj(f)
    except Exception:
        pass

    de = DiffExt(x)
    subs = {}   # 原始 Exp/Log term -> 塔符号（驻留键）

    def tower_frac(t):
        """t 在当前塔上的 (num, den)；含未覆盖 Exp/Log/非有理 -> PolyError。"""
        g = T.subst(t, subs) if subs else t
        return _frac_from_term(g, de.vars)

    # 工作队列：反复扫描直到无新层可建（嵌套参数依赖内层先建，
    # 如 log(log(x)) 外层需等内层）；永久建不了的由末尾残留检查拒绝。
    while True:
        exps, logs = _collect_exts(f)
        changed = False

        # log 层（primitive）：u = 塔上分式且非常数
        for u in logs:
            key = T.mk(S("Log"), (u,))
            if key in subs:
                continue
            try:
                un, ud = tower_frac(u)
            except PolyError:
                continue   # 本轮建不了（内层未就绪或永不可建）
            if un.is_const() and ud.is_const():
                continue   # log(常数) 属常数域，不建层
            w = _tower_logderiv(un, ud, de)   # D(u)/u
            tl = de.add("primitive", w, key, "l")
            subs[key] = T.S(tl.name)
            changed = True

        # exp 层（hyperexponential）：base = 塔上分式，Fr 倍数归组
        for base, members in _group_integer_powers(exps):
            key = T.mk(S("Exp"), (base,))
            if key in subs:
                continue
            try:
                bn, bd = tower_frac(base)
            except PolyError:
                continue
            if bn.is_const() and bd.is_const():
                continue   # exp(常数) = 常数因子
            # 代数依赖守卫（M5.2c-iii 精确判定版）：e^base 与塔代数
            # 相关 ⟺ ∃n∈ℤ≠0, w: n·D(base) = D(w)/w —— 对底数的导数
            # 做对数导数-根式判定（经典 Risch 结构定理；直接判 base 会
            # 漏掉 e^{log x /2}=√x 类无极点代数情形）。判定为超越
            # （None）=> 放行建新层；代数相关 => 诚实拒绝。
            if any(e > 0 for mono in bn.monos for e in mono[1:]) \
                    or any(e > 0 for mono in bd.monos for e in mono[1:]):
                from cas.ratfunc import RatFunc as _RFg
                cur_vars = tuple(de.levels)
                g_rf = _RFg(_embed(bn, cur_vars), _embed(bd, cur_vars))
                dg_rf = _tower_deriv_frac(g_rf.p, g_rf.q, de)
                # 懒导入断环：core(塔构建) <- prde(判定件) 互引，
                # 调用期双方均已加载（与全库懒导入风格一致）
                from cas.risch_prde import _is_logderiv_radical
                dep = _is_logderiv_radical(dg_rf, de,
                                           len(de.levels) - 1)
                if dep is not None:
                    raise RischUnsupported(
                        "exponent algebraically dependent on existing "
                        "tower variables (log-derivative radical)")
            w = _tower_deriv_frac(bn, bd, de)   # eta' = D(base)
            tl = de.add("exp", w, key, "t")
            subs[key] = T.S(tl.name)
            # 组内各成员方向同步登记（复合底的下一轮解析依赖：
            # 如 Exp(−ix) 建层后 Exp(+ix) 须映射为 t^{-1}）
            for arg_m, mm2 in members:
                mkey = T.mk(S("Exp"), (arg_m,))
                subs[mkey] = (T.pw(T.S(tl.name), N(mm2)) if mm2 != 1
                              else T.S(tl.name))
            changed = True

        # 代数层（M78 合并地基）：变元底根式 Power(u, p/q)，u 含塔变量
        for pw in _collect_alg_candidates(f, de):
            if pw in subs:
                continue
            b_, e_ = pw.args
            p_, q_ = e_.f.numerator, e_.f.denominator
            r_ = gcd(p_, q_)
            pp_, qq_ = p_ // r_, q_ // r_
            try:
                bn, bd = tower_frac(b_)
            except PolyError:
                continue
            # 根式 R = B^{pp}（B = bn/bd 约化分式）
            rn, rd = _cancel(bn ** pp_, bd ** pp_)
            if rn.is_const() and rd.is_const():
                continue          # 常数底：常数域路径（ALG_FIELDS）
            from cas.algfield import binomial_irreducible
            if not binomial_irreducible(rn, rd, qq_):
                raise RischUnsupported(
                    "variable-base radical with reducible binomial "
                    "min polynomial (degenerate form)")
            # 积分生成元 ϑ：ϑ^{qq} = rn·rd^{qq−1}（首一整关系）
            Mp = _ta_reduce(rn * (rd ** (qq_ - 1)) if qq_ > 1 else rn, de)
            Mp = _cancel(Mp, Poly.one(Mp.vars))[0]
            # η = D(ϑ)/ϑ = D(Mp)/(q·Mp)
            dmn, dmd = derivation(Mp, de)
            from cas.ratfunc import RatFunc as _RFa
            eta = _RFa(dmn, dmd.scalar(Fr(qq_)) * Mp)
            t_new = _fresh_sym(de.levels, "a")
            lower = tuple(de.levels)
            mp_low = Poly((t_new,),
                          {(qq_,): Poly.one(lower),
                           (0,): Mp.scalar(Fr(-1))})
            de.levels.append(t_new)
            de.cases.append("algebraic")
            de.ws.append(eta)
            # 方向一致性：ϑ = θ·rd。前向 leaf ↦ ϑ/rd（值恒等）；
            # 回代 sym ↦ ϑ 的值 = leaf·rd（rd 平凡时退化为叶本身）
            leaf_term = T.mk(S("Power"), (b_, e_))
            rd_term = rd.to_term()
            if rd.is_const() and abs(rd.const_val()) == 1:
                fwd_term, retract_term = t_new, leaf_term
            else:
                fwd_term = T.div(t_new, rd_term)
                retract_term = T.times(leaf_term, rd_term)
            de.terms.append(retract_term)
            de.minpolys.append((qq_, mp_low))
            subs[pw] = fwd_term
            changed = True

        if not changed:
            break

    # 重写 f 到塔上：Exp(m*base) -> t^m（归组成员按幂次展开），Log(u) -> tl
    full_subs = dict(subs)
    for base, members in _group_integer_powers(_collect_exts(f)[0]):
        key = T.mk(S("Exp"), (base,))
        if key not in subs:
            continue
        tv = subs[key]
        for arg, m in members:
            full_subs[T.mk(S("Exp"), (arg,))] = T.pw(tv, N(m)) if m != 1 else tv
    g = T.subst(f, full_subs) if full_subs else f

    # 残留检查：漏网的 Exp/Log = 塔覆盖不全（诚实拒绝；含命名/超越
    # 常数时附 Richardson 卡点提示）
    rexp, rlog = _collect_exts(g)
    if rexp or rlog:
        raise RischUnsupported(
            "expression not covered by the differential extension"
            + _const_blockage_hint(f, xv=x))

    try:
        fa, fd = _frac_from_term(g, de.vars)
        # 代数层规范形：约简指数 < q（M78.3 _ta_reduce）
        fa = _ta_reduce(fa, de)
        fd = _ta_reduce(fd, de)
    except PolyError as ex:
        raise RischUnsupported("not rational over the extension: " + str(ex))
    return de, fa, fd


def _collect_alg_candidates(f, de):
    """扫描 f 中变元底根式叶：Power(u, p/q)，u 含塔变量、q ≥ 2。

    纯参数底（√2 类常数）不在此列——常数域路径（ALG_FIELDS）负责。
    按驻留节点身份去重。
    """
    out = []
    seen = set()
    tower = set(de.levels)
    stack = [f]
    while stack:
        u = stack.pop()
        if not isinstance(u, Expr):
            continue
        if u.head.name == "Power":
            b_, e_ = u.args
            if isinstance(e_, T.Rat) and e_.f.denominator > 1 \
                    and e_.f > 0 \
                    and (tower & T.free_vars(b_)):
                if id(u) not in seen:
                    seen.add(id(u))
                    out.append(u)
                continue          # 整叶处理，不再深入
        stack.extend(u.args)
    return out


def _frac_from_term(t, vars_):
    """term -> 约化 (num, den) Poly 对（负整数幂入分母）。"""
    num = _frac_num(t, vars_)
    return _cancel(num[0], num[1])


def _frac_num(t, vars_):
    if T.is_num(t):
        return Poly.const(vars_, T.num_val(t)), Poly.one(vars_)
    if isinstance(t, Sym):
        for v in vars_:
            if t is v:
                return Poly.mono(vars_, t, 1), Poly.one(vars_)
    if isinstance(t, (Sym, Const)) and t.name == "i":
        # 虚单位单一收口（N1，与 Poly._build 同款保留名）：
        # Sym("i")/Const("i") 同路径 → Ga(0,1)
        from cas.gaussian import Ga
        return Poly.const(vars_, Ga(0, 1)), Poly.one(vars_)
    if isinstance(t, Sym):
        # 不在 vars 的符号 = 超越参数：升入 ℚ(params)（M5.6 首项，
        # ∫2^x 全族；与 Poly._build 同款语义）
        from cas.poly import _mk_param
        return Poly.const(vars_, _mk_param(t)), Poly.one(vars_)
    if isinstance(t, Const):
        # 命名常数查注册表（P5）：imaginary-unit 内建为域元素
        from cas.spec import get_constant
        sp = get_constant(getattr(t, "name", ""))
        if sp is not None and sp.kind == "imaginary-unit":
            from cas.gaussian import Ga
            return Poly.const(vars_, Ga(0, 1)), Poly.one(vars_)
        raise PolyError("not rational over extension: " + repr(t))
    if isinstance(t, Expr):
        n = t.head.name
        if n == "Plus":
            an, ad = Poly.zero(vars_), Poly.one(vars_)
            for a in t.args:
                bn, bd = _frac_num(a, vars_)
                an, ad = _radd((an, ad), (bn, bd))
            return an, ad
        if n == "Times":
            an, ad = Poly.one(vars_), Poly.one(vars_)
            for a in t.args:
                bn, bd = _frac_num(a, vars_)
                an, ad = _rmul_polys(an, ad, bn, bd)
            return an, ad
        if n == "Power":
            b, e = t.args
            bn, bd = _frac_num(b, vars_)
            if isinstance(e, T.Int) and e.v >= 0:
                return bn ** e.v, bd ** e.v
            if isinstance(e, T.Int):
                return bd ** (-e.v), bn ** (-e.v)
            raise PolyError("non-integer power in extension")
    raise PolyError("not rational over extension: " + repr(t))


# ---------------------------------------------------------------------------
# 塔上求导（maxima spderivative 对应物：扁平 Poly 全变量链式法则）
# ---------------------------------------------------------------------------

def derivation(p, de):
    """Poly(de.vars) -> (num, den)：塔上导数 D（约化分式）。

    D(sum c_k * prod v^e) = sum_j [d(mono)/dv_j] * D(v_j)；
    系数 c_k in Q 导数为零；D(v_j) 由 cases/ws 给出。
    """
    vars_ = p.vars
    acc_n, acc_d = Poly.zero(vars_), Poly.one(vars_)
    for exps, c in p.monos.items():
        for j, v in enumerate(vars_):
            e = exps[j]
            if e == 0:
                continue
            nk = tuple(x - (1 if i == j else 0) for i, x in enumerate(exps))
            pre = Poly(vars_, {nk: c * e})
            dn, dd = de.dpair(j, vars_)
            acc_n, acc_d = _radd(
                (acc_n, acc_d), _rmul_polys(pre, Poly.one(vars_), dn, dd)
            )
    # M78：代数层的乘积中途会产生 θ 指数 ≥ q 的项（D(θ)=η·θ 使
    # θ^{e-1}·θ 相乘），出口统一约简回规范形
    return _cancel(_ta_reduce(acc_n, de), _ta_reduce(acc_d, de))


# ---------------------------------------------------------------------------
# 回写（塔 -> term）
# ---------------------------------------------------------------------------

def tower_to_term_pair(a, d, de, backsub=True):
    """(num, den) Poly -> term（backsub=False 保留塔符号）。"""
    nt = a.to_term() if not a.is_zero() else T.ZERO
    dt = d.to_term()
    val = T.div(nt, dt) if not dt is T.ONE else nt
    if not backsub:
        return val
    subs = {}
    for i in range(1, len(de.levels)):
        subs[T.S(de.levels[i].name)] = de.terms[i]
    if not subs:
        return val
    return T.subst(val, subs)


def _norm_const_base_powers(t, x):
    """自底向上：变指数幂 b^e（e 含 x，底任意）-> Exp(e·Log(b))。

    通用桥接恒等式（Maxima/FriCAS/sympy 积分器对 a^b 的标准处理）：
    变指数幂是 x 的超越函数，塔只认 Exp/Log 头。与系统自身语义自洽：
    diff.py 幂规则 d(b^e)=b^e(D(e)Log(b)+eD(b)/b) 同用 Log(b)（单值
    主支承诺）；_fold_power 的 E^a->Exp(a) 是本规则在欧拉数底的
    构造级特例。常指数幂（x²、√x）不动——代数名词归 M7a。
    """
    head = getattr(t, "head", None)
    if head is None:
        return t          # Int/Fr 等数值叶（无头，无需重写）
    args = tuple(_norm_const_base_powers(a, x) for a in t.args)
    u = T.mk(head, args)
    uhead = getattr(u, "head", None)
    if uhead is None:
        return u          # mk 规范化可能整体折叠（如 exp(x·log2)−2^x -> 0）
    if uhead.name == "Power":
        b, e = u.args
        if x in T.free_vars(e):
            return T.mk(S("Exp"), (T.times(e, T.fn("Log")(b)),))
        # 数值非整指数且底含变量（sqrt/x^(p/q) 类）：代数核 ->
        # exp-log 超越通道。初等可积性优先（int x^(p/q) 全族解锁）；
        # 代数核追踪（Trager/M7a）后续再选道——语义与 diff 幂规则一致。
        if isinstance(e, T.Rat) and e.f.denominator != 1 \
                and x in T.free_vars(b):
            return T.mk(S("Exp"), (T.times(e, T.fn("Log")(b)),))
    return u


def _parametrize_const_logs(f, x):
    """Log(不含积分变量的项)/命名常数 -> 独立超越参数符号（M5.6）。

    log 2 / π / e / γ 类常量须进系数域做线性代数，而此类常量间的
    数值关系不可判定（Richardson）；积分全程只需"互相超越独立"假设
    ——零等价 = ℚ(params, c₁..cₙ) 上有理恒等（可判定，SymRat 参数
    机器），出口回代还原。形式恒等 ⇒ 对一致特化（c=真值）成立：
    独立性假设只可能保守拒绝，不产生误证。
    命名常数按名字确定编号（pi/e/gamma -> _nc1/_nc2/_nc3）；IU 已由
    Ga 内建不经此通道。
    返回 (新 f, 回代表 {塔符号 -> 原 term})。
    """
    named = {"pi": "_nc1", "e": "_nc2", "gamma": "_nc3"}
    found = {}
    nc_subs = {}
    pow_subs = {}                        # 复合替换（值非符号，不进回代）
    stack = [f]
    while stack:
        u = stack.pop()
        if isinstance(u, Expr) and getattr(u, "head", None) is not None:
            if u.head.name == "Log" and x not in T.free_vars(u.args[0]):
                found[u] = None      # 整体替换，不再深入 arg
                continue
            if u.head.name == "Exp" and x not in T.free_vars(u.args[0]):
                # N6-P2/P2c 面孔统一：exp(k·字面) 与命名常数 e 的精确
                # 幂关系收进参数化层——exp(1)≡_nc2（定义级）；非零整
                # 字面 k（|k|≤64）→ _nc2^k 复合替换（不进回代，出口随
                # _nc2→E 还原为规范面孔 e^k）。非整字面诚实保持核形态
                # （分数幂需关系感知参数，N9/M78.8 辖区）。
                a0 = u.args[0]
                if is_num(a0):
                    v0 = num_val(a0)
                    if isinstance(v0, Fr):
                        if v0 == 1:
                            found[u] = None
                            nc_subs.setdefault(u, S(named["e"]))
                            continue
                        if v0.denominator == 1 and v0 != 0 \
                                and abs(v0) <= 64:
                            found[u] = None
                            nc_subs.setdefault(T.E, S(named["e"]))
                            pow_subs[u] = T.pw(S(named["e"]), N(v0.numerator))
                            continue
                stack.append(u.args[0])
            stack.extend(u.args)
            # 命名常数收集（Log 子树已整体替换，其内部 π 不重复点名）
            for a in u.args:
                if isinstance(a, Const) and getattr(a, "name", "") in named:
                    nc_subs.setdefault(a, S(named[a.name]))
                elif isinstance(a, Expr) and a.head.name == "Power":
                    _collect_radical(a, nc_subs, xv=x)
                    # M5.5 支援切片：命名常数的非整幂（sqrt(pi) 类）
                    # -> 独立参数。独立性假设 Richardson 安全（同 _nc），
                    # 使 erf 族答案的验证链（d(F) 与 f 的常数因子
                    # sqrt(pi)/sqrt(pi) 抵消）在塔上精确归零。
                    if a not in nc_subs:
                        b_, e_ = a.args
                        nm_ = getattr(b_, "name", "")
                        if isinstance(b_, Const) and nm_ in named \
                                and isinstance(e_, T.Rat) \
                                and e_.f.denominator != 1:
                            _NCPOW_COUNTER[0] += 1
                            nc_subs.setdefault(a, S(f"_np{_NCPOW_COUNTER[0]}"))
        elif isinstance(u, Const) and getattr(u, "name", "") in named:
            nc_subs[u] = S(named[u.name])
    subs = {}
    backsub = {}
    for k, lt in enumerate(sorted(found, key=repr), 1):
        sym = S(f"_cl{k}")
        subs[lt] = sym
        backsub[sym] = lt
    for c_term, sym in nc_subs.items():
        subs[c_term] = sym
        backsub[sym] = c_term
    subs.update(pow_subs)
    if not subs:
        return f, {}
    return T.subst(f, subs), backsub
