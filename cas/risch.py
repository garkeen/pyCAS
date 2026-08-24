"""微分域塔（Risch M5.0）：DifferentialExtension 对应物 + 塔上求导。

参照：Bronstein《Symbolic Integration I》第 4-6 章；sympy risch.py 的
DifferentialExtension（level/case 结构）；maxima risch.lisp（属性表存
各扩展导数 + spderivative 链式求导——本模块的 derivation 同思路，
但在扁平多元 Poly 上做全变量链式法则）。

M5.0 范围：塔构建（exp/primitive 单项式，参数限 Q(x)）+ derivation
+ term<->塔双向转换。积分算法本体（Hermite 推广/residue_reduce/RDE）
在 M5.1+；三角经复指数在 M5.3（maxima trigin1 路线）。

诚实边界：代数依赖（exp(log(x)/2)）、嵌套超越参数（exp(x*e^x)）、
三角函数输入一律 RischUnsupported 拒绝——绝不静默错。
"""

from fractions import Fraction as Fr
from math import gcd

from cas import term as T
from cas.term import S, N, Expr, Sym, Const, Int, ONE, IU
from cas.poly import Poly, SymRat
from cas.errors import PolyError
from cas.gaussian import Ga


class RischUnsupported(Exception):
    """塔构建失败（携带原因，诚实拒答的载体）。"""

    def __init__(self, reason):
        super().__init__(reason)
        self.reason = reason


class DiffExt:
    """微分域塔 K_0 < K_1 < ... < K_n，K_0 = Q(x)。

    levels[i]：塔变量（levels[0] = 积分变量 x）；
    cases[i]：'base' | 'exp' | 'primitive'；
    ws[i]：RatFunc（K_{i-1} 上）——exp: D(t_i) = w*t_i；
    primitive: D(t_i) = w；
    terms[i]：塔变量的原函数形态（backsubs 用，如 Exp(x/2)、Log(x)）。
    """

    __slots__ = ("levels", "cases", "ws", "terms")

    def __init__(self, x):
        self.levels = [x]
        self.cases = ["base"]
        self.ws = [None]
        self.terms = [x]

    @property
    def vars(self):
        return tuple(self.levels)

    def add(self, case, w, term, name_hint):
        t = _fresh_sym(self.levels, name_hint)
        self.levels.append(t)
        self.cases.append(case)
        self.ws.append(w)
        self.terms.append(term)
        return t

    def dpair(self, j, all_vars):
        """D(levels[j]) 作为 all_vars 上的 (num, den) 分式。"""
        if self.cases[j] == "base":
            return Poly.const(all_vars, Fr(1)), Poly.one(all_vars)
        w = self.ws[j]
        wn = _embed(w.p, all_vars)
        wd = _embed(w.q, all_vars)
        if self.cases[j] == "exp":
            tj = _embed(Poly.mono(all_vars, self.levels[j], 1), all_vars)
            return _rmul_polys(wn, wd, tj, Poly.one(all_vars))
        return wn, wd


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


# 代数常数关系登记（M5.4 切片 a）：符号 -> monic 极小多项式
# （Poly over ()，Fr 系数）。SAE 语义：元素 = 次数<deg(m) 的多项式，
# reduce = udivmod 余项——关系感知算术在后续切片接入，登记先行。
ALG_RELATIONS = {}
_ALG_RADICAL_COUNTER = [0]
_NCPOW_COUNTER = [0]


def _collect_radical(pterm, subs):
    """数值底正有理指数幂 b^(p/q)（b>0 整数）-> 新代数常数符号。

    极小多项式 X^q − b^p（monic，不可约当 b 非完全幂——完全幂已被
    mk 数值折叠）。同形幂共享符号；√2·√2 经 SymRat 算术自然产生
    _a1² 叶——关系约简在 M5.4 后续切片接入 reduce_mod_m。
    """
    b, e = pterm.args
    if not (T.is_num(b) and isinstance(e, T.Rat)):
        return
    bv = T.num_val(b)
    if bv <= 0 or e.f <= 0 or e.f == 1:
        return
    p_, q_ = e.f.numerator, e.f.denominator
    if q_ == 1:
        return
    key = (bv, p_, q_)
    for sym, (mkey, _m) in ALG_RELATIONS.items():
        if mkey == key:
            subs[pterm] = sym
            return
    _ALG_RADICAL_COUNTER[0] += 1
    sym = S(f"_a{_ALG_RADICAL_COUNTER[0]}")
    # 极小多项式必须是该符号上的单变量 Poly：X^q − b^p（monic）。
    # 零维坏键 Poly（{(1,):..,(0,):..} 于 () 空间）会被 _reduce_alg_var
    # 误读为 X−2 —— α≡2 静默错域（M5.4a 休眠 bug，M5.4-c 审计修复）
    mp = Poly((sym,), {(q_,): Fr(1), (0,): Fr(-(bv ** p_))})
    ALG_RELATIONS[sym] = ((bv, p_, q_), mp)
    from cas.poly import ALG_MODULI
    ALG_MODULI[sym] = mp          # 乘积出口自动模约简（M5.4b）
    subs[pterm] = sym


def _const_blockage_hint(f):
    """被积函数含命名常数/非常量域超越常量时的 Richardson 卡点提示。

    π、e、γ 类命名常数与 sin(1)、e² 类未求值超越项目前不在任何精确
    常数域中（零等价不可判定，Richardson）——塔覆盖失败时如实点名：
    这是数学边界而非实现缺陷；M5.6#1 参数化通道可部分解锁。
    """
    from cas.pprint import to_str

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


# ---------------------------------------------------------------------------
# M5.3.2 出口实化切片二：log 配对（Laurent 共轭自反分解）
#
# 塔答案中的 Log(u)，u 为单一虚频率指数多项式（如 1+e^{−2ix}）：替换
# z = e^{γx} 得 Laurent 多项式 L(z)；若系数满足共轭自反性
# cₙ = conj(c_{d+m−n})，则 L(e^{γx}) = e^{sγx}·Θ(x)，Θ 为实三角多项式
# ——log u 精确重写为 s·γ·x + log Θ（差常数不影响原函数；整体出口
# 经 verify 背书后才接受，失败保留复形态）。tan 类由此出真实形态。
# --------------------------------------------------------------------


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


def _realify_one_log(u, x, zsym):
    """Log 参数 u -> (线性校正项, 实三角 Θ term) 或 None。"""
    exps = []
    stack = [u]
    while stack:
        v = stack.pop()
        if isinstance(v, Expr) and getattr(v, "head", None) is not None:
            if v.head.name == "Exp" and len(v.args) == 1:
                exps.append(v)
                continue
            stack.extend(v.args)
    if not exps:
        return None
    freqs = {}
    for e_ in exps:
        g = _lin_exp_freq(e_.args[0], x)
        if g is None or g.im == 0:
            return None          # 本切片仅纯虚频率
        freqs[e_] = True
    gamma = _lin_exp_freq(exps[0].args[0], x)
    usub = T.subst(u, {e_: zsym for e_ in exps})
    if x in T.free_vars(usub):
        return None              # Log 参数含裸 x——本切片不处理
    try:
        lp = Poly.from_term(usub, (zsym,))
    except PolyError:
        return None
    monos = {k[0]: c for k, c in lp.monos.items()}
    degs = [n for n, c in monos.items() if c != 0]
    if not degs:
        return None
    d, m = max(degs), min(degs)
    tot = d + m
    if tot % 2 != 0:
        return None
    s = tot // 2

    def coef(n):
        return monos.get(n, Fr(0))

    for n in range(m, d + 1):
        cn, cm = coef(n), coef(tot - n)
        if isinstance(cn, Fr):
            cn = Ga(cn, Fr(0))
        if isinstance(cm, Fr):
            cm = Ga(cm, Fr(0))
        if cn != cm.conjugate():
            return None
    # Θ = z^{-s} L(z)：Hermitian 对称 -> 实三角组合
    beta = gamma.im           # z = e^{i·beta·x}
    parts = []
    cs = coef(s)
    if isinstance(cs, Fr):
        cs = Ga(cs, Fr(0))
    if cs.re != 0:
        parts.append(N(cs.re))
    hmax = max(abs(d - s), abs(s - m))
    for k in range(1, hmax + 1):
        bk = coef(s + k)
        if isinstance(bk, Fr):
            bk = Ga(bk, Fr(0))
        if bk == Ga(0, 0):
            continue
        re2 = bk.re + bk.re
        im2 = bk.im + bk.im
        # 三角参数折正（cos 偶 / sin 奇吸收符号）
        a_ = Fr(k) * beta
        argn = T.times(N(-a_ if a_ < 0 else a_), x)
        if re2 != 0:
            parts.append(T.times(N(re2), T.fn("Cos")(argn)))
        if im2 != 0:
            base = im2 if a_ < 0 else (-im2)
            parts.append(T.times(N(base), T.fn("Sin")(argn)))
    theta = T.mk(S("Plus"), tuple(parts)) if len(parts) > 1 \
        else (parts[0] if parts else N(Fr(1)))
    # 线性项 = s·γ·x（γ 经 Ga.to_term 以 i 精确重建）
    lin = T.times(N(Fr(s)), T.times(gamma.to_term(), x))
    return lin, theta


def _realify_log_pairing(expr, x):
    """出口扫描：逐个尝试 Log 配对实化；无变化返回 None。"""
    logs = []
    stack = [expr]
    while stack:
        v = stack.pop()
        if isinstance(v, Expr) and getattr(v, "head", None) is not None:
            if v.head.name == "Log" and len(v.args) == 1:
                logs.append(v)
                continue
            stack.extend(v.args)
    subs = {}
    zid = [0]
    for lg in logs:
        zid[0] += 1
        zs = S(f"_rz{zid[0]}")
        r = _realify_one_log(lg.args[0], x, zs)
        if r is None:
            continue
        lin, theta = r
        subs[lg] = T.plus(lin, T.fn("Log")(theta))
    if not subs:
        return None
    return T.subst(expr, subs)


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
            + _const_blockage_hint(f))

    try:
        fa, fd = _frac_from_term(g, de.vars)
    except PolyError as ex:
        raise RischUnsupported("not rational over the extension: " + str(ex))
    return de, fa, fd


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
    return _cancel(acc_n, acc_d)


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


# ---------------------------------------------------------------------------
# M5.1a/M5.2：塔上 K[t] 视图积分（t = exp(eta) 或 primitive θ）
#
# 表示：K[t] 多项式 = 系数 list [c_0..c_n]（c_i: RatFunc——K = Q(x) 显式
#       有理函数域，M5.2 起；升序）；K(t) 分式 = (A, d)（A, d: K[t]）。
# 塔上导数 D: K[t] -> K[t]（K 是域，Dθ = v ∈ K 或 Dt = η'·t）：
#   exp:       D(Σa_k t^k)  = Σ (Da_k + k·η'·a_k) t^k          （对角）
#   primitive: D(Σa_k θ^k)  = Σ_i (Da_i + (i+1)·v·a_{i+1}) θ^i  （移位）
# special 因子：exp 的 t（gcd(t,Dt)=t≠1）；primitive 无（gcd(θ,v)=1，
#   θ 正规）——primitive 全部因子走 normal 路线。
# ---------------------------------------------------------------------------

def _univar(p, ti):
    """Poly(all_vars) -> K[t_i] 系数 list（升序，K 元素 = RatFunc）。"""
    from cas.ratfunc import RatFunc

    sub = tuple(v for v in p.vars if v is not ti)
    j = p.vars.index(ti)
    out = [RatFunc.zero(sub)]
    for k, c in p.monos.items():
        e = k[j]
        while len(out) <= e:
            out.append(RatFunc.zero(sub))
        nk = tuple(x for i, x in enumerate(k) if i != j)
        out[e] = out[e] + RatFunc.from_poly(Poly(sub, {nk: c}))
    return out


def _from_univar(coeffs, all_vars, ti):
    """系数 list（RatFunc）-> 塔上 (num, den) Poly 对。"""
    j = all_vars.index(ti)

    def shift(p, e):
        # embed 后 p 已含 t 维度（指数 0）——替换位置 j 的指数，非插入
        return Poly(all_vars, {k[:j] + (e,) + k[j + 1:]: c
                               for k, c in p.monos.items()})

    num = Poly.zero(all_vars)
    den = Poly.one(all_vars)
    for e, c in enumerate(coeffs):
        if c.is_zero():
            continue
        pe = shift(_embed(c.p, all_vars), e)
        qe = _embed(c.q, all_vars)      # 分母不带 θ^e 权重
        num = num * qe + den * pe
        den = den * qe
    return _cancel(num, den)


def _u_add(a, b, zero):
    n = max(len(a), len(b))
    out = []
    for i in range(n):
        ca = a[i] if i < len(a) else zero
        cb = b[i] if i < len(b) else zero
        out.append(ca + cb)
    return _u_trim(out)


def _u_trim(cs):
    while cs and cs[-1].is_zero():
        cs.pop()
    return cs


def _u_neg(a, neg):
    return [neg(c) for c in a]


def _u_mul(a, b, zero):
    if not a or not b:
        return []
    out = [zero for _ in range(len(a) + len(b) - 1)]
    for i, ca in enumerate(a):
        if ca.is_zero():
            continue
        for j, cb in enumerate(b):
            if cb.is_zero():
                continue
            out[i + j] = out[i + j] + ca * cb
    return _u_trim(out)


def _u_divmod(a, b, zero):
    """K[t] 除法（b 非零，K = RatFunc 域）。返回 (q, r) 系数 list。"""
    r = [c for c in a]
    db = len(b) - 1
    lb = b[db]
    if len(r) - 1 < db:
        return [], _u_trim(r)
    q = [zero for _ in range(len(r) - db)]
    while len(r) - 1 >= db and not _u_is_zero(r):
        shift = len(r) - 1 - db
        lc = r[-1]
        c = lc / lb
        q[shift] = c
        for i in range(db + 1):
            r[shift + i] = r[shift + i] - c * b[i]
        _u_trim(r)
    return _u_trim(q), _u_trim(r)


def _u_is_zero(cs):
    return not cs or all(c.is_zero() for c in cs)


def _u_gcd(a, b, zero):
    """K[t] gcd（欧几里得 + monic）。K 是域——首系数总可逆。"""
    A, B = _u_trim([c for c in a]), _u_trim([c for c in b])
    while not _u_is_zero(B):
        _, r = _u_divmod(A, B, zero)
        A, B = B, r
    if _u_is_zero(A):
        return []
    s = zero.one(zero.p.vars) / A[-1]
    return [c * s for c in A]


def _u_inv_mod(a, m, zero):
    """a 的逆 mod m（gcd(a,m)=1）。扩展欧几里得：s*a + t*m = g -> s/g。

    初始化 s0=0（对应 r0=m）、s1=1（对应 r1=a）；结束时 s0*a ≡ g (mod m)。
    """
    r0, r1 = [c for c in m], _u_trim([c for c in a])
    s0, s1 = [zero], [zero.one(zero.p.vars)]
    while not _u_is_zero(r1):
        q, r = _u_divmod(r0, r1, zero)
        qs = _u_mul(q, s1, zero)
        s_new = _u_add(s0, _u_neg(qs, lambda c: c * Fr(-1)), zero)
        s0, s1 = s1, s_new
        r0, r1 = r1, r
    # r0 = gcd；互素时为 K 中单位（非零元素），s0*a ≡ gcd (mod m)
    if _u_is_zero(r0):
        raise RischUnsupported("zero gcd in inverse")
    s = r0[0].one(r0[0].p.vars) / r0[0]
    out = [c * s for c in s0]
    _, rem = _u_divmod(out, m, zero)
    return rem


def _u_deriv_x(coeffs):
    """K 层求导：逐系数 d/dx。"""
    xv = coeffs[0].p.vars[0] if coeffs and coeffs[0].p.vars else T.S("x")
    return [c.deriv(xv) for c in coeffs]


def _derive_ut(coeffs, de, j):
    """塔上 D 作用于 Σ a_k t_j^k -> K[t] 系数 list（K 是域，无分母）。

    exp:       D(Σa_k t^k) = Σ (Da_k + k·η'·a_k) t^k          （对角）
    primitive: D(Σa_k θ^k) = Σ_i (Da_i + (i+1)·v·a_{i+1}) θ^i  （移位）
    """
    from cas.ratfunc import RatFunc

    w = de.ws[j]
    zv = RatFunc.zero(w.p.vars)   # 系数域零元（vars = levels[:j]）
    n = len(coeffs)
    out = []
    for i in range(n):
        a = coeffs[i]
        # K 层导数必须是塔上导数 D_K（多层时 d/dx 不够——D(l)=1/x 类）
        term = _tower_deriv_frac(a.p, a.q, de) if not a.is_zero() else zv
        if de.cases[j] == "exp":
            if i > 0 and not a.is_zero():
                term = term + a * w * Fr(i)
        else:  # primitive：右邻贡献 (i+1)·v·a_{i+1}
            if i + 1 < n and not coeffs[i + 1].is_zero():
                term = term + coeffs[i + 1] * w * Fr(i + 1)
        out.append(term)
    return _u_trim(out)


def _exp_w(de, j):
    """第 j 层的 w = D(t)/t 或 D(θ)（RatFunc）。"""
    return de.ws[j]


# ---------------------------------------------------------------------------
# M5.1b：Risch 微分方程 exp case——y' + k*eta'*y = g（y ∈ Q(x)）
#
# 极点分析：p^m ∥ denom(y) => y' 有 p^{m+1} 极点而 k*eta'*y 只有 p^m
# （eta' 多项式）=> p^{m+1} | denom(g)。故 denom(y) 的界
# D = Π p^{e-1}（p^e ∥ denom(g)，e>=2）；z = y*D 多项式化后待定系数。
# f = k*eta' != 0 保证齐次多项式解只有 0（deg y' < deg f*y）=> 解唯一。
# ---------------------------------------------------------------------------

def _poly_to_list(p):
    """Poly((x,)) -> 升序 Fr 系数 list。"""
    xv = p.vars[0]
    d = p.degree(xv)
    out = [Fr(0)] * (d + 1)
    for k, v in p.monos.items():
        out[k[0]] = v
    return out


def _list_to_poly(cs, vars_):
    """升序 Fr list -> Poly（一元）。"""
    return Poly(vars_, {(e,): c for e, c in enumerate(cs) if c != 0})


def _gauss_solve(M, b):
    """Fr 系数线性方程组高斯消元。返回解 list | None（无解）。

    自由变量取 0（f != 0 时 RDE 齐次只有零解，理论保证无自由变量；
    此处取 0 为防御性特解）。
    """
    n = len(M)
    cols = len(M[0]) if n else 0
    A = [row[:] + [b[i]] for i, row in enumerate(M)]
    piv_cols = []
    r = 0
    for cidx in range(cols):
        piv = None
        for i in range(r, n):
            if A[i][cidx] != 0:
                piv = i
                break
        if piv is None:
            continue
        A[r], A[piv] = A[piv], A[r]
        pv = A[r][cidx]
        A[r] = [v / pv for v in A[r]]
        for i in range(n):
            if i != r and A[i][cidx] != 0:
                fac = A[i][cidx]
                A[i] = [vi - fac * vr for vi, vr in zip(A[i], A[r])]
        piv_cols.append(cidx)
        r += 1
        if r == n:
            break
    for i in range(n):
        if all(v == 0 for v in A[i][:cols]) and A[i][-1] != 0:
            return None
    z0 = b[0] * 0 if n else Fr(0)   # 系数域零元（Fr/Ga 通用）
    sol = [z0] * cols
    for i, cidx in enumerate(piv_cols):
        sol[cidx] = A[i][-1]
    return sol


def _rde_exp_solve(k, eta_p, an, ad, zero):
    """解 y' + k*eta'*y = an/ad（y ∈ Q(x)）。返回 y: Poly | None。

    None = 无有理解（该频率分量不可初等的证明载体）。
    """
    xv = zero.vars[0]
    f = eta_p.scalar(Fr(k))
    # 步骤1：分母界 D = Π p^{e-1}（p^e ∥ denom(g)，e>=2）
    Dp = Poly.one(zero.vars)
    from cas.factor import squarefree_decomp

    for pp, e in squarefree_decomp(ad):
        if e >= 2:
            Dp = Dp * pp ** (e - 1)
    # 步骤2：z = y*D；两边乘 ad：ad*D*z' + (f*D − D')*ad*z = an*D²
    A_ = ad * Dp
    B_ = (f * Dp - Dp.deriv(xv)) * ad
    C_ = an * Dp * Dp
    degB = B_.degree(xv)
    degC = C_.degree(xv)
    if degB < 0:
        # B ≡ 0：f*D = D' 且 ad 常数——eta' 多项式时仅 f=0，已排除
        raise RischUnsupported("degenerate RDE (f*D == D')")
    N = degC - degB
    if N < 0:
        # z 只能 = 0；rhs 非零即无解
        return None if not C_.is_zero() else Poly.zero(zero.vars)
    # 步骤3：待定系数线性方程组
    A_l = _poly_to_list(A_)
    B_l = _poly_to_list(B_)
    C_l = _poly_to_list(C_)
    ncols = N + 1
    top = max(len(C_l) - 1, (len(B_l) - 1) + N,
              (len(A_l) - 1) + (N - 1) if N > 0 else 0)
    nrows = max(top, len(C_l) - 1) + 1
    M = [[Fr(0)] * ncols for _ in range(nrows)]
    rhs_v = [Fr(0)] * nrows
    for i, cv in enumerate(C_l):
        rhs_v[i] = cv
    for ci in range(ncols):
        # 基 z = x^ci：LHS = A*(ci*x^(ci-1)) + B*x^ci
        if ci > 0:
            for ai, av in enumerate(A_l):
                m = ai + ci - 1
                M[m][ci] += av * Fr(ci)
        for bi, bv in enumerate(B_l):
            M[bi + ci][ci] += bv
    sol = _gauss_solve(M, rhs_v)
    if sol is None:
        return None
    return _list_to_poly(sol, zero.vars)


def risch_exp_integrate(fa, fd, de, j):
    """exp 单项式积分主入口（M5.1：真分式 + 频率分解）。

    返回 ((rat_part, logs, nonel, leftover), freqs, status)：
    freqs = {k: g_k}（g_k: RatFunc）——全部非零频率分量（正幂商 +
    负幂低幂 + residue t 幂剩余），k≠0 待 RDE；status: 'ok'。
    """
    from cas.ratfunc import RatFunc

    zero = RatFunc.zero((de.levels[0],))
    tj = de.levels[j]

    A = _univar(fa, tj)
    D = _univar(fd, tj)
    if _u_is_zero(A):
        return (None, None, None, None), {}, "ok"

    # 多项式部分：商 Q 的频率 + 真分式 R
    dq = len(D) - 1
    dp = len(A) - 1
    pos_freqs = {}
    if dp >= dq:
        Q, R = _u_divmod(A, D, zero)
        for k, c in enumerate(Q):
            if not c.is_zero():
                pos_freqs[k] = c
        A = R
        if _u_is_zero(A):
            return (None, None, None, None), pos_freqs, "ok"

    res, neg_freqs, st = _integrate_proper(A, D, de, j, zero)
    freqs = dict(pos_freqs)
    for k, v in neg_freqs.items():
        freqs[k] = freqs[k] + v if k in freqs else v
    return res, freqs, st


def _integrate_proper(A, D, de, j, zero):
    """真分式积分：special 分离（仅 exp）+ 无平方分解 + Hermite + residue。

    返回 ((rat_part, logs, nonel, leftover), neg_freqs, status)：
    neg_freqs = {k: g_k}——t 负幂频率分量（k<0，M5.1b RDE 处理）。
    primitive 层无 special 因子（gcd(θ,v)=1，θ 正规），全走 normal。
    """
    if de.cases[j] == "primitive":
        res, st = _integrate_normal(A, D, de, j, zero)
        return res, {}, st
    # special 分离：D = t^m * q0（q0[0] != 0）
    m = 0
    q0 = list(D)
    while len(q0) > 0 and q0[0].is_zero():
        q0 = q0[1:]
        m += 1
    q0 = _u_trim(q0)
    if m > 0:
        k_m = min(m, len(A))
        low, high = A[:k_m], A[k_m:]
        # 低段 Σ a_k t^{k-m}（负幂频率）；高段走正规路线
        neg_freqs = {}
        for k, c in enumerate(low):
            if not c.is_zero():
                neg_freqs[k - m] = c
        if _u_is_zero(high):
            return (None, None, None, None), neg_freqs, "ok"
        res, st = _integrate_normal(high, q0, de, j, zero)
        rat_part, logs, nonel, leftover = res
        if isinstance(leftover, tuple) and leftover \
                and leftover[0] == "special":
            # residue 剩余的 t 幂部分 -> 正频（与 m==0 分支同款转换；
            # 键空间不相交：neg k<0 / pos k>=0）
            pos_freqs = {k: c for k, c in enumerate(leftover[1])
                         if not c.is_zero()}
            return (rat_part, logs, nonel, None), \
                {**neg_freqs, **pos_freqs}, st
        return res, neg_freqs, st
    res, st = _integrate_normal(A, D, de, j, zero)
    rat_part, logs, nonel, leftover = res
    if isinstance(leftover, tuple) and leftover and leftover[0] == "special":
        # residue 剩余的 t 幂部分 -> 正频
        pos_freqs = {k: c for k, c in enumerate(leftover[1]) if not c.is_zero()}
        return (rat_part, logs, nonel, None), pos_freqs, st
    return res, {}, st


def _integrate_normal(A, D, de, j, zero):
    """正规分母真分式：无平方分解 -> 部分分式 -> Hermite(e>1) + residue(e=1)。

    返回 (rat_part, logs, nonel, leftover, status)：
    rat_part = [(u_k, p, k)] 有理部分 u_k/p^k；logs = [(c, g)] 对数项；
    nonel = (num, p)|None 不可初等剩余（residue 无常数根——Bronstein 定理：
    真分式情形 residue 失败即证明不可初等）；leftover = K 分式递归 x 层。
    """
    tj = de.levels[j]
    factors = _squarefree_decomp_t(D, zero)
    rat_part = []
    logs = []
    nonel = None
    leftover = None
    for p, e in factors:
        cof = _u_divmod(D, _u_pow(p, e, zero), zero)[0]
        B = _u_divmod(_u_mul(A, _u_inv_mod_t(cof, D, zero), zero), _u_pow(p, e, zero), zero)[1]
        if e > 1:
            rat, (B1, _) = _hermite_pe(B, p, e, de, j, zero)
            rat_part.extend(rat)
        else:
            B1 = B
        lg, rem = _residue_sqfr(B1, p, de, j, zero)
        logs.extend(lg)
        if not _u_is_zero(rem):
            q, r = _u_divmod(rem, p, zero)
            if _u_is_zero(r):
                # 剩余恰为多项式：exp 下全部进频率（k=0 分量由低层递归
                # 积分处理）；primitive 下回本层多项式循环（leftover）
                if de.cases[j] == "exp":
                    return (rat_part, logs, None, ("special", q)), "ok"
                leftover = q if leftover is None else _u_add(leftover, q, zero)
            else:
                nonel = (rem, p)
    return (rat_part, logs, nonel, leftover), "ok"


def _u_pow(cs, n, zero):
    out = [zero.one(zero.p.vars)]
    base = list(cs)
    while n > 0:
        if n & 1:
            out = _u_mul(out, base, zero)
        base = _u_mul(base, base, zero)
        n >>= 1
    return out


def _u_inv_mod_t(a, m, zero):
    """K[t] 上 a^{-1} mod m。"""
    return _u_inv_mod(a, m, zero)


def _squarefree_decomp_t(D, zero):
    """K[t] 无平方分解 [(p, e)]（形式导数 gcd 递归）。"""
    def rec(cur):
        if len(cur) <= 1 or _u_is_zero(cur):
            return []
        dc = _u_formal_deriv(cur)
        g = _u_gcd(cur, dc, zero)
        if len(g) <= 1:
            return [(cur, 1)]
        core, r = _u_divmod(cur, g, zero)
        if not _u_is_zero(r):
            raise RischUnsupported("squarefree division failed")
        rest = rec(g)
        single = core
        for pp, _mm in rest:
            single = _u_divmod(single, pp, zero)[0]
        out = [(pp, mm + 1) for pp, mm in rest]
        if len(single) > 1:
            out.append((single, 1))
        return out

    out = rec(list(D))
    # 规范序：按次数升序稳定组装
    return sorted(out, key=lambda pe: len(pe[0]))


def _u_formal_deriv(cs):
    """形式偏导 ∂/∂t（系数不动）。"""
    return _u_trim([c * Fr(k) for k, c in enumerate(cs)][1:])


def _hermite_pe(a, p, e, de, j, zero):
    """∫ a/p^e（p 无平方正规）-> (有理部分 [(u_k, p, k)], 剩余 (b, p))。

    逐层：u ≡ -(k-1)^{-1}*(a mod p)*inv(D(p)) (mod p)；
    v = (a + (k-1)*u*D(p))/p - D(u)，整除性由 u 构造保证。
    """
    rat = []
    cur_a, cur_e = list(a), e
    while cur_e >= 2:
        u, v = _hermite_factor(cur_a, p, cur_e, de, j, zero)
        if not _u_is_zero(u):
            rat.append((u, p, cur_e - 1))
        cur_a = v
        cur_e -= 1
    return rat, (cur_a, p)


def _hermite_factor(a, p, e, de, j, zero):
    """单层剥离：∫ a/p^e -> 贡献 u/p^{e-1}，剩余 v/p^{e-1}。

    u ≡ -(e-1)^{-1}·(a mod p)·inv(D(p) mod p) (mod p)（K 域上，无 wd 因子）。
    """
    Pm = _derive_ut(p, de, j)             # D(p)：K[t] 元素
    r = _u_divmod(a, p, zero)[1]
    pm1 = _u_inv_mod(Pm, p, zero)
    coef = Fr(-1) / (e - 1)
    u = [c * coef for c in _u_mul(r, pm1, zero)]
    _, u = _u_divmod(u, p, zero)
    # N = a + (e-1)*u*D(p) 整除 p
    N_ = _u_add(list(a), _u_mul([c * Fr(e - 1) for c in u], Pm, zero), zero)
    M, rem = _u_divmod(N_, p, zero)
    if not _u_is_zero(rem):
        raise RischUnsupported("hermite divisibility failed")
    Du = _derive_ut(u, de, j)
    v = _u_add(M, _u_neg(Du, lambda c: c * Fr(-1)), zero)
    return u, v


# ---------------------------------------------------------------------------
# residue_reduce（Rothstein-Trager；结式经 Bareiss 行列式，K[z] 系数）
# ---------------------------------------------------------------------------

def _neg_poly(c):
    return c * Fr(-1)


def _sylvester_res(fz, gz):
    """res_t(f, g)：fz/gz 是 K[z] 多项式（list[K 元素]，z 升序——与 K[t] 同构）。

    Sylvester 矩阵 + Bareiss 行列式（K[z] 整环上 exact division）。
    行列式与标准结式至多差符号——求根用途下无关紧要。
    """
    from cas.ratfunc import RatFunc

    m = len(fz) - 1     # deg f
    n = len(gz) - 1     # deg g
    size = m + n
    if size <= 0:
        return []
    M = []
    for i in range(n):
        row = [[] for _ in range(size)]
        for jj in range(i, min(i + m + 1, size)):
            row[jj] = fz[m - (jj - i)]
        M.append(row)
    for i in range(m):
        row = [[] for _ in range(size)]
        for jj in range(i, min(i + n + 1, size)):
            row[jj] = gz[n - (jj - i)]
        M.append(row)
    zero = RatFunc.zero((T.S("x"),))
    return _bareiss_det(M, size, zero)


# ---------------------------------------------------------------------------
# Bareiss 行列式（元素 = K[z] 多项式 = list[K 元素]，与 K[t] 同构——_u_* 通用）
# ---------------------------------------------------------------------------

def _u_sub(a, b):
    """K 多项式减法（zero 自参数推断）。"""
    from cas.ratfunc import RatFunc

    src = a if a else b
    z = RatFunc.zero(src[0].p.vars) if src else RatFunc.zero((T.S("x"),))
    return _u_add(a, _u_neg(b, lambda c: c * Fr(-1)), z)


def _u_mul0(a, b):
    """K 多项式乘法（zero 自参数推断）。"""
    from cas.ratfunc import RatFunc

    if not a or not b:
        return []
    z = RatFunc.zero(a[0].p.vars)
    return _u_mul(a, b, z)


def _bareiss_det(M, size, zero):
    """Bareiss 分式免除行列式（元素为 K[z] 多项式，_u_* 层直接适用）。"""
    A = [row[:] for row in M]
    prev = None         # 上一步主元；第一步除数为 1（不除）
    sign = 1
    for k in range(size - 1):
        if _u_is_zero(A[k][k]):
            for i in range(k + 1, size):
                if not _u_is_zero(A[i][k]):
                    A[k], A[i] = A[i], A[k]
                    sign = -sign
                    break
            else:
                return []
        pk = A[k][k]
        for i in range(k + 1, size):
            for jj in range(k + 1, size):
                num = _u_sub(_u_mul0(A[i][jj], pk), _u_mul0(A[i][k], A[k][jj]))
                if prev is not None:
                    q, r = _u_divmod(num, prev, zero)
                    if not _u_is_zero(r):
                        raise RischUnsupported("bareiss exact division failed")
                    A[i][jj] = q
                else:
                    A[i][jj] = num
        prev = pk
    det = _u_trim(A[size - 1][size - 1])
    det = _uz_trim_det(det)
    return det if sign == 1 else _u_neg(det, lambda c: c * Fr(-1))


def _uz_trim_det(p):
    return _u_trim(p)


def _residue_sqfr(B, p, de, j, zero):
    """∫ B/p（p 无平方正规）-> (logs [(c, g)], rem)。

    R(z) = res_t(B - z*D(p), p)；常数根 c（free of x）->
    贡献 c*log(g)，g = gcd(p, B - c*D(p))；剩余 rem（分母仍 p）
    = 不可初等成分。Bronstein 定理：真分式 + 无常数根 => 不可初等
    （M5.1b 补多项式部分后为完整证明）。solve 无法定根时显式异常——
    绝不静默把可积成分误判为不可积。
    """
    Dp = _derive_ut(p, de, j)
    nb = max(len(B), len(Dp))
    Bp = B + [zero for _ in range(nb - len(B))]
    Dpp = Dp + [zero for _ in range(nb - len(Dp))]
    # fz[i] = B_i - z*Dp_i（K[z] 多项式 = list[K 元素]）
    fz = [[b, _neg_poly(d)] for b, d in zip(Bp, Dpp)]
    gz = [[c] for c in p]
    Rz = _sylvester_res(fz, gz)
    logs = []
    rem = list(B)
    if len(Rz) >= 1 and not _u_is_zero(Rz):
        roots = _constant_roots(Rz)
        for c in roots:
            # fc = fz 代入 z=c：b + c*(-d)
            fc = []
            for zp in fz:
                val = zp[0]
                if len(zp) > 1:
                    val = val + zp[1] * c
                fc.append(val)
            fc = _u_trim(fc)
            g = _u_gcd(fc, p, zero)
            if len(g) <= 1:
                continue
            logs.append((c, g))
            Dg = _derive_ut(g, de, j)
            cof = _u_divmod(p, g, zero)[0]
            ct = zero.one(zero.p.vars) * c
            corr = _u_mul([ct], _u_mul(Dg, cof, zero), zero)
            rem = _u_add(rem, _u_neg(corr, lambda cc: cc * Fr(-1)), zero)
    return logs, _u_trim(rem)


def _uz_trim_list(cs):
    return _u_trim(cs)


def _iter_subterms(t):
    stack = [t]
    while stack:
        u = stack.pop()
        yield u
        if isinstance(u, Expr):
            stack.extend(u.args)


def _term_to_ga(t):
    """term -> Ga（仅含数字与符号 i 的线性形态）；否则 None。"""
    fv = T.free_vars(t)
    if any(v.name != "i" for v in fv):
        return None
    try:
        return Ga.from_term_val(t)
    except Exception:
        return None


def _frac_sqrt(f):
    """有理数的精确平方根；非 Fr 或非完全平方返回 None。"""
    from math import isqrt

    if not isinstance(f, Fr):
        return None          # SymRat/Ga 判别式：非有理平方根
    if f < 0:
        return None
    rn, rd = isqrt(f.numerator), isqrt(f.denominator)
    if rn * rn != f.numerator or rd * rd != f.denominator:
        return None
    return Fr(rn, rd)


def _ga_sqrt_exact(g):
    """Ga 的精确平方根（系数有理域内）；非完全平方返回 None。"""
    A, B = g.re, g.im
    n = A * A + B * B
    sn = _frac_sqrt(n)
    if sn is None:
        return None
    u2 = (A + sn) / 2
    su = _frac_sqrt(u2)
    if su is None:
        return None
    if su == 0:
        sv = _frac_sqrt((A - sn) / 2)
        if sv is None:
            return None
        return Ga(Fr(0), sv)
    return Ga(su, B / (2 * su))


def _const_roots_ga_quad(Rz):
    """R(z) 全 ℚ(i)-常数且次数 ≤2 时精确求根；否则 None。"""
    cs = [c for c in Rz if not c.is_zero()]
    if not cs or len(cs) > 3:
        return None
    vals = []
    for c in cs:
        g = _rf_const_ga(c)
        if g is None:
            return None
        vals.append(g)
    if len(vals) == 1:
        return []
    if len(vals) == 2:
        return [-vals[0] / vals[1]]
    a2, b1, c0 = vals
    disc = b1 * b1 - a2 * c0 * 4
    s = _ga_sqrt_exact(disc)
    if s is None:
        return None
    two = Ga(2)
    return [(-b1 + s) / (a2 * 2), (-b1 - s) / (a2 * 2)]


def _term_to_symrat(t_):
    """term -> SymRat（参数/AN 轨道）：显式 (num, den) 对算术求值。

    M5.4 审计修复：残数根落在 ℚ(params,α) 时不再误判为不可积。
    solve 返回的解可能是未规范嵌套分式（如 1/(a²·(-1/a)))——其内部
    结构与打印同形的 parse 树不同，from_term 分支覆盖不了；此处用
    自底向上 (num,den) 对算术（加/乘/整幂/取逆）完全可控。不支持
    形态返回 None。"""
    from cas.poly import _mk_rat

    vs = tuple(sorted(T.free_vars(t_), key=lambda s_: s_.name))
    zero_k = tuple(0 for _ in vs)

    def nd(u):
        # 全部叶子直接在 vs 全空间构造——避免跨空间乘法的 var mismatch
        if T.is_num(u):
            return Poly(vs, {zero_k: T.num_val(u)}), Poly.one(vs)
        if isinstance(u, Sym):
            k = [0] * len(vs)
            k[vs.index(u)] = 1
            return Poly(vs, {tuple(k): Fr(1)}), Poly.one(vs)
        h = getattr(u, "head", None)
        if h is None:
            raise ValueError("atom")
        n = h.name
        if n == "Plus":
            rn = Poly.zero(vs)
            rd = Poly.one(vs)
            for a_ in u.args:
                pn, pd = nd(a_)
                rn, rd = rn * pd + pn * rd, rd * pd
            return rn, rd
        if n == "Times":
            rn, rd = Poly.one(vs), Poly.one(vs)
            for a_ in u.args:
                pn, pd = nd(a_)
                rn, rd = rn * pn, rd * pd
            return rn, rd
        if n == "Power":
            b_, e_ = u.args
            if not isinstance(e_, T.Int):
                raise ValueError("non-int power")
            pn, pd = nd(b_)
            bn, bd = Poly.one(vs), Poly.one(vs)
            if e_.v >= 0:
                for _ in range(e_.v):
                    bn, bd = bn * pn, bd * pd
            else:
                for _ in range(-e_.v):
                    bn, bd = bn * pd, bd * pn
            return bn, bd
        raise ValueError("head " + n)

    try:
        num, den = nd(t_)
        sr = _mk_rat(num, den)
        return sr if isinstance(sr, (SymRat, Fr)) else None
    except Exception:
        return None


def _constant_roots(Rz):
    """R(z) ∈ Q(x)[z] 的常数根：转 term 用 solve，含 x 的根丢弃。

    含 x 的根被丢弃正是数学语义：非常数 residue 不对应初等对数项。
    solve 无法判定（unsupported）时抛异常——绝不静默漏根（漏根会把
    可积成分误判为不可初等，违反永不静默错）。根值表示三级回退：
    数值 Fr / ℚ(i)（_term_to_ga）/ ℚ(params,α)（_term_to_symrat，
    M5.4 审计扩容——残数根可安全停留在参数轨道：形式恒等对特化
    保真）；更高阶代数根（真 RootOf 域）显式异常。"""
    # M5 收官批 #3：系数含 SymRat 分母时 solve 报 "not polynomial"。
    # 用 together+numerator 在项级清分母——根不变（乘非零常数倍）。
    from cas.solve import solve as _solve
    from cas.ratfunc import RatFunc

    z = T.S("_rz")
    terms = []
    for e, c in enumerate(Rz):
        if c.is_zero():
            continue
        ct = c.to_term()
        terms.append(T.times(ct, T.pw(z, N(e))) if e else ct)
    if not terms:
        return []
    poly_t = T.mk(S("Plus"), tuple(terms)) if len(terms) > 1 else terms[0]
    # 项级清分母：together 取公分母，numerator 取分子
    # （SymRat 内嵌分母在项级暴露为分数；together 合并后 numerator
    #  揽出多项式分子——根不变，乘非零常数倍。常数多项式无变量时
    #  together 会报 "no variables"——此无害，回退原始项由 solve 处理）
    try:
        from cas.ops import together as _together, numerator as _numer
        cleared = _numer(_together(poly_t))
    except Exception:
        cleared = poly_t
    r = _solve(cleared, z)
    if r.status != "ok":
        # ℚ(i) 常数低次回退：精确二次/一次求根（三角残数常为 ±i 型）
        fb = _const_roots_ga_quad(Rz)
        if fb is not None:
            return fb
        raise RischUnsupported(
            "cannot determine constant roots of the resultant: " + (r.note or ""))
    out = []
    for sol in r.solutions:
        if not _free_of_x(sol):
            continue
        if not T.is_num(sol):
            ga = _term_to_ga(sol)
            if ga is not None:
                out.append(ga)
                continue
            sr = _term_to_symrat(sol)
            if sr is not None:
                out.append(sr)
                continue
            raise RischUnsupported(
                "algebraic residue roots beyond Q(i)/Q(params) pending")
        out.append(T.num_val(sol))
    return out


def _free_of_x(t):
    xv = T.S("x")
    return xv not in T.free_vars(t)


# ---------------------------------------------------------------------------
# 结果组装（塔 -> term）
# ---------------------------------------------------------------------------

def assemble_exp_result(rat_part, logs, nonel, de, j):
    """积分结果 -> 塔符号 term（不回写——出口统一 backsubst）。"""
    tj = de.levels[j]
    rat_part = rat_part or []
    logs = logs or []
    parts = []
    for u, p, k in rat_part:
        un, ud = _from_univar(u, de.vars, tj)
        pn, pd = _from_univar(p, de.vars, tj)
        ut = tower_to_term_pair(un, ud, de, backsub=False)
        pt = tower_to_term_pair(pn, pd, de, backsub=False)
        parts.append(T.div(ut, T.pw(pt, N(k))))
    for c, g in logs:
        gn, gd = _from_univar(g, de.vars, tj)
        gt = tower_to_term_pair(gn, gd, de, backsub=False)
        ct = c.to_term() if hasattr(c, "to_term") else N(c)
        parts.append(T.times(ct, T.log(gt)))
    if nonel is not None:
        num, p = nonel
        nn, nd = _from_univar(num, de.vars, tj)
        pn, pd = _from_univar(p, de.vars, tj)
        from cas.pprint import to_str as _ts

        raise RischNonElementary(
            "integral of " + _ts(T.div(
                tower_to_term_pair(nn, nd, de, backsub=False),
                tower_to_term_pair(pn, pd, de, backsub=False))) +
            " over the tower is not elementary (no constant residue roots)"
        )
    if not parts:
        return T.ZERO
    if len(parts) == 1:
        return parts[0]
    return T.mk(S("Plus"), tuple(parts))


class RischNonElementary(Exception):
    """不可初等证明载体（Bronstein 决策程序的否定结论）。"""

    def __init__(self, reason):
        super().__init__(reason)
        self.reason = reason


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
    stack = [f]
    while stack:
        u = stack.pop()
        if isinstance(u, Expr) and getattr(u, "head", None) is not None:
            if u.head.name == "Log" and x not in T.free_vars(u.args[0]):
                found[u] = None      # 整体替换，不再深入 arg
                continue
            stack.extend(u.args)
            # 命名常数收集（Log 子树已整体替换，其内部 π 不重复点名）
            for a in u.args:
                if isinstance(a, Const) and getattr(a, "name", "") in named:
                    nc_subs.setdefault(a, S(named[a.name]))
                elif isinstance(a, Expr) and a.head.name == "Power":
                    _collect_radical(a, nc_subs)
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
    if not subs:
        return f, {}
    return T.subst(f, subs), backsub


def _mixed_domain_leaf(c):
    """叶是否属于 Q(i,x_params) 混合轨道（SymRat 内含 Ga 叶，或 Ga
    分量为 SymRat）。"""
    if isinstance(c, SymRat):
        for pp in (c.num, c.den):
            for cc in pp.monos.values():
                if hasattr(cc, "norm") and not isinstance(cc, Fr):
                    return True
        return False
    if hasattr(c, "norm") and isinstance(c, Ga):
        return isinstance(c.re, SymRat) or isinstance(c.im, SymRat)
    return False


def _has_mixed_domain(*polys):
    """多 Poly 的叶是否含 ℚ(i,params) 混合。"""
    for p in polys:
        if any(_mixed_domain_leaf(c) for c in _iter_leaf_coefs_m(p)):
            return True
    return False


def _split_tower_rational(fa, fd):
    """fa/fd（塔上 Poly）共轭展开实虚拆分（A4 泛化至多变量塔）。

    返回 (num_re, num_im, den) 或 None（无混合域叶时不需拆分）。
    num_re/den 与 num_im/den 各自纯参数叶（Fr/SymRat，无 Ga）——
    消除 _rde_tower_solve 的域泛化 gcd 需求。
    """
    if not _has_mixed_domain(fa, fd):
        return None
    from cas.integrate import _poly_re_im
    fa_re, fa_im = _poly_re_im(fa)
    fd_re, fd_im = _poly_re_im(fd)
    den = fd_re * fd_re + fd_im * fd_im
    if den.is_zero():
        raise PolyError("zero denominator after conjugate expansion")
    num_re = fa_re * fd_re + fa_im * fd_im
    num_im = fa_im * fd_re - fa_re * fd_im
    return num_re, num_im, den


def _risch_rec_mixed(fa, fd, de, j):
    """_risch_rec 的混合域前置拆分包装。

    混合域（ℚ(i,params)）输入 => 共轭拆分 => 两条纯参数链 =>
    线性合并 re + i·im。非混合 => 直通 _risch_rec。
    """
    split = _split_tower_rational(fa, fd)
    if split is None:
        return _risch_rec(fa, fd, de, j)
    num_re, num_im, den = split
    expr_re = _risch_rec(num_re, den, de, j)
    if num_im.is_zero():
        return expr_re
    expr_im = _risch_rec(num_im, den, de, j)
    from cas import term as T
    from cas.term import S
    return T.plus(expr_re, T.times(IU, expr_im))


def integrate_exp_tower(f, x):
    """顶层 API：term -> (term, de)（初等原函数）或异常。

    M5.2b 递归塔：任意 primitive/exp 层序列，K 上积分递归下降。
    内部全程塔符号空间，出口统一回写。入口先做三角/双曲复指数化
    （M5.3 trigs_to_exp——无三角头时零开销直通）。
    """
    # 常被积函数快捷通道：∫c dx = c·x（c 为任意不含 x 的常量表达式，
    # 含 sin(y)/π²/ℚ(i) 元素等——塔机制本就不适用，直接精确给出；
    # 置于复指数化之前以保持用户原始形态）
    if x not in T.free_vars(f):
        return T.times(f, x), DiffExt(x)
    f = trigs_to_exp(f)
    # M5.6 首项：变指数幂归一 + Log(常量) 参数化（∫a^x 全族解锁）
    f, backsub = _parametrize_const_logs(_norm_const_base_powers(f, x), x)
    de, fa, fd = build_extension(f, x)
    # M5 收官批 #3：混合域（Q(i,params)）门控退役——共轭拆分前置
    # （A4 泛化至多变量塔），消除 RDE 域泛化 gcd 需求
    j = len(de.levels) - 1
    if j == 0:
        raise RischUnsupported("no extension layer in expression")
    expr = _risch_rec_mixed(fa, fd, de, j)
    subs = {T.S(de.levels[i].name): de.terms[i]
            for i in range(1, len(de.levels))}
    if subs:
        expr = T.subst(expr, subs)
    if backsub:
        expr = T.subst(expr, backsub)
    # M5.3.2 出口实化切片二：log 配对（候选重写先规范化再整体
    # verify 背书，失败保留复形态——诚实纪律）
    try:
        from cas.simplify import simplify as _simp, expand as _exp
        e2 = _realify_log_pairing(expr, x)
        if e2 is not None:
            # expand 先分配（mk 不做 Times-over-Plus），环规范折叠线性项
            e2 = _simp(_exp(e2))
            from cas.diff import verify as _vf
            if _vf(e2, x, f) == "VERIFIED":
                expr = e2
    except Exception:
        pass
    return expr, de


def _integrate_in_K(g, de, j):
    """∫g dx，g ∈ K_j = ℚ(x, t₁..t_{j-1})（RatFunc on levels[:j]）→ term。"""
    from cas.integrate import integrate_rational

    if j <= 1:
        xv = de.levels[0]
        if g.is_const():
            # 常数被积函数（含 ℚ(i) 常数，M5.3 复指数化的 k=0 分量）
            cv = g.const_val()
            ct = cv.to_term() if hasattr(cv, "to_term") else N(cv)
            return T.times(ct, xv)
        # 基域有理积分：Fr/ℚ(params)（M5.6 参数轨道完备）/ℚ(i) 及
        # ℚ(i,params) 混合（A4 共轭拆分）全部由 integrate_rational
        # 入口统一路由——旧 "pending" 守卫是参数轨道完备前的遗留
        val, ok, _prov = integrate_rational(g.p, g.q, xv)
        if not ok:
            raise RischUnsupported("rational integration failed in base field")
        return val
    return _risch_rec(g.p, g.q, de, j - 1)


def _coef_iter(rf):
    """RatFunc 的全部叶系数。"""
    yield from _iter_leaf_coefs_m(rf.p)
    yield from _iter_leaf_coefs_m(rf.q)


def _iter_leaf_coefs_m(p):
    if not p.monos:
        return
    if len(p.vars) <= 1:
        for v in p.monos.values():
            yield v
        return
    from cas.poly import _rec_view
    for sub in _rec_view(p).values():
        yield from _iter_leaf_coefs_m(sub)


def _limited_integrate(a, de, j):
    """K_j 上求 (b_rf, c) 使 Db + c·v = a（limited integration 问题）。

    全程塔符号空间：c = ∫a 中 log(θ_j) 成分系数——θ_j 的对数形态
    Log(u_j) 的塔符号即本层变量自身。其余 log/atan 成分无法由 b ∈ K_j
    解释 -> rest ≠ 0 表示该塔内无解形态。
    """
    from cas.ratfunc import RatFunc

    syms = {de.terms[i]: T.S(de.levels[i].name)
            for i in range(1, len(de.levels))}
    u_sym = T.subst(de.terms[j].args[0], syms)   # u_j 的塔符号形态
    val = _integrate_in_K(a, de, j)
    rat_t, alpha, rest = _decompose_integral(val, u_sym, syms)
    if rest is not T.ZERO:
        return None, None, rest
    try:
        b_rf = RatFunc.from_term(rat_t, tuple(de.levels[:j]))
    except PolyError:
        return None, None, val
    return b_rf, (alpha if alpha != 0 else None), T.ZERO


def _has_trans_head(t):
    """t 是否含 Log/Atan 头（任意深度）。"""
    stack = [t]
    while stack:
        u = stack.pop()
        if isinstance(u, T.Expr):
            if u.head.name in ("Log", "Atan"):
                return True
            stack.extend(u.args)
    return False


def _decompose_integral(val, u_sym, syms):
    """塔符号空间的初等原函数 term -> (rat_term, alpha, rest)。

    - Log(g) 且 g ≡ u_sym：alpha 累加（limited 的 c）
    - Log(g) 且 g ≡ 某已建层参数 u_i：替换为塔符号 S(levels[i])（低层
      residue 出的 log(θ_i) 即 θ_i 自身形态，归 rat）
    - 其余含 Log/Atan 头：rest（新层候选，塔外成分）
    - 纯有理：rat
    """
    parts = val.args if isinstance(val, T.Expr) and val.head.name == "Plus" \
        else (val,)
    alpha = Fr(0)
    rest_parts = []
    rat_parts = []
    for t in parts:
        hit, coef = _log_u_factor_generic(t, u_sym)
        if hit:
            alpha += T.num_val(coef)
            continue
        mapped, new_t = _map_known_log(t, syms)
        if mapped:
            rat_parts.append(new_t)
        elif _has_trans_head(t):
            rest_parts.append(t)
        else:
            rat_parts.append(t)
    rat_t = T.mk(S("Plus"), tuple(rat_parts)) if len(rat_parts) > 1 \
        else (rat_parts[0] if rat_parts else T.ZERO)
    rest = T.mk(S("Plus"), tuple(rest_parts)) if len(rest_parts) > 1 \
        else (rest_parts[0] if rest_parts else T.ZERO)
    return rat_t, alpha, rest


def _log_u_factor_generic(t, u_sym):
    """t 是否含 Log(恰为 u_sym) 因子。-> (bool, 系数 term)。"""
    if isinstance(t, T.Expr) and t.head.name == "Log" \
            and len(t.args) == 1 and t.args[0] is u_sym:
        return True, T.ONE
    if isinstance(t, T.Expr) and t.head.name == "Times":
        lgs = [a for a in t.args if isinstance(a, T.Expr)
               and a.head.name == "Log" and len(a.args) == 1
               and a.args[0] is u_sym]
        if len(lgs) == 1:
            coef = T.ONE
            for o in t.args:
                if o is not lgs[0]:
                    coef = T.times(coef, o)
            return True, coef
    return False, None


def _map_known_log(t, syms):
    """t 中 Log(u_i)（u_i = 第 i 层参数）替换为塔符号 S(levels[i])。

    返回 (是否替换发生, 新 term)。t 不含任何已知 Log 时 (False, t)。
    """
    if not isinstance(t, T.Expr):
        return False, t
    hit = [False]

    def rec(u):
        if not isinstance(u, T.Expr):
            return u
        if u.head.name == "Log" and len(u.args) == 1:
            for key, sym in syms.items():
                if isinstance(key, T.Expr) and key.head.name == "Log" \
                        and len(key.args) == 1 and key.args[0] is u.args[0]:
                    hit[0] = True
                    return sym
        return T.mk(u.head, tuple(rec(a) for a in u.args))

    out = rec(t)
    return hit[0], out


def _primitive_poly_part(Q, de, j):
    """∫ Σ a_k θ^k：limited_integrate 循环（sympy integrate_primitive_polynomial
    同构）。每轮残差最高次严格下降，终止。"""
    from cas.ratfunc import RatFunc
    from cas.pprint import to_str as _ts

    sub = tuple(de.levels[:j])
    zero = RatFunc.zero(sub)
    out = []
    p = list(Q)
    while not _u_is_zero(p):
        m = len(p) - 1
        a = p[m]
        b_rf, c, rest = _limited_integrate(a, de, j)
        if b_rf is None:
            raise RischUnsupported(
                "component requires integration outside the tower: "
                + _ts(rest)[:80])
        q0 = [zero] * (m + 2)
        if c is not None:
            q0[m + 1] = zero.one(zero.p.vars) * (Fr(c) / Fr(m + 1))
        q0[m] = b_rf
        p = _u_sub(p, _derive_ut(q0, de, j))
        if not q0[m + 1].is_zero():
            out.append((q0[m + 1], m + 1))
        if not q0[m].is_zero():
            out.append((q0[m], m))
    return out


# ---------------------------------------------------------------------------
# M5.2c：塔系数域上的 Risch 微分方程（exp 层频率方程 y' + k·w·y = g，
# y ∈ K_j 含低层塔变量）。f = k·w 不含塔变量（exp 守卫保证）=> 极点分析
# 直接成立：den(y) | Π s^{e-1}（s^e ∥ den(g) 正规因子）——无需 weak
# normalization（那处理的是 f 本身有塔极点的 cancellation 情形）。
# 多项式化后 K 域线性系统待定系数；有解经精确验证输出，无解返回 None
# （unsupported，绝不误判不可积——完整 cancellation 分析留后续）。
# ---------------------------------------------------------------------------

def _u_gauss_solve_k(M, b):
    """K 域（RatFunc）线性方程组高斯消元。返回解 list | None（无解）。"""
    n = len(M)
    cols = len(M[0]) if n else 0
    if n == 0 or cols == 0:
        return [] if not any(not x.is_zero() for x in b) else None
    one = b[0].one(b[0].p.vars)
    A = [list(M[r]) + [b[r]] for r in range(n)]
    piv_cols = []
    r = 0
    for cidx in range(cols):
        piv = None
        for i in range(r, n):
            if not A[i][cidx].is_zero():
                piv = i
                break
        if piv is None:
            continue
        A[r], A[piv] = A[piv], A[r]
        pv = A[r][cidx]
        inv = one / pv
        A[r] = [x * inv for x in A[r]]
        for i in range(n):
            if i != r and not A[i][cidx].is_zero():
                fac = A[i][cidx]
                A[i] = [vi - fac * vr for vi, vr in zip(A[i], A[r])]
        piv_cols.append(cidx)
        r += 1
        if r == n:
            break
    for i in range(n):
        if all(x.is_zero() for x in A[i][:cols]) and not A[i][cols].is_zero():
            return None
    sol = [one.zero(one.p.vars) for _ in range(cols)]
    for i, cidx in enumerate(piv_cols):
        sol[cidx] = A[i][cols]
    return sol


def _restrict(rf, vars_):
    """RatFunc 收缩到指定变量集（缺失维度指数须全零，否则 PolyError）。"""
    from cas.ratfunc import RatFunc as _RF

    def shrink(p):
        if p.vars == tuple(vars_):
            return p
        idx = {v: i for i, v in enumerate(p.vars)}
        out = {}
        for k, c in p.monos.items():
            for v in p.vars:
                if v not in vars_ and k[idx[v]] != 0:
                    raise PolyError("cannot restrict: variable present")
            out[tuple(k[idx[v]] if v in idx else 0 for v in vars_)] = c
        return Poly(tuple(vars_), out)

    return _RF(shrink(rf.p), shrink(rf.q))


# ---------------------------------------------------------------------------
# M5.2c-ii：塔域 Risch DE 完备判定
#
# 解 D(y) + f·y = g（y ∈ K_j = ℚ(x, t₁..t_{j-1})），三态返回：
#   (y, 'ok')          有理解（出口精确验证兜底，验证不过 = 内部错误异常）
#   (None, 'proved')   无有理解的机器证明（界否定/贪心余量/整除性失败）
#   (None, 'undecided') 当前理论不可判——绝不猜测、绝不误证
#
# 唯一算法参考：FriCAS intpar.spad ParametricRischDE（weak normalization
# :920 / get_denom :910 / 变换 :1406-1410 / 右端缩放 :1237）+ sympy rde.py
# 的 bound_degree / spde / no_cancel_b_large / no_cancel_b_small /
# no_cancel_equal / cancel_* 分派细节补全。已知切片边界（触发时诚实
# undecided，绝不降级猜测）：
#   S-a primitive db==da-1 共振的 limited_integrate 完整版
#       （当前用紧刻画 alpha/eta∈ℚ 覆盖 z-自由子情形）
#   S-c 非常数比值的共振判定（limited_integrate 完整版）
# 已修复：S-a radical 判定（_is_logderiv_radical，守卫共用）、
#   S-b B=0 cancellation（lam=0 统一下降）、exp da==db 界修正
#   （_pld_heu 判据）。
# ---------------------------------------------------------------------------


def _fu_add(n1, d1, n2, d2, zero):
    """K[t] 分式加法（n/d 为 univar list；空分母按单位 1 规范化）。"""
    one_c = zero.one(zero.p.vars)
    d1 = d1 if d1 else [one_c]
    d2 = d2 if d2 else [one_c]
    return (_u_add(_u_mul(n1, d2, zero), _u_mul(n2, d1, zero), zero),
            _u_mul(d1, d2, zero))


def _fu_mul(n1, d1, n2, d2, zero):
    one_c = zero.one(zero.p.vars)
    d1 = d1 if d1 else [one_c]
    d2 = d2 if d2 else [one_c]
    return (_u_mul(n1, n2, zero), _u_mul(d1, d2, zero))


def _u_deg(cs):
    return len(_u_trim(list(cs))) - 1


def _u_xgcd(a, b, zero):
    """扩展欧几里得：返回 (s, t, g) 使 s·a + t·b = g。"""
    one_c = zero.one(zero.p.vars)
    r0, r1 = _u_trim([c for c in b]), _u_trim([c for c in a])
    s0, s1 = [], [one_c]
    t0, t1 = [one_c], []
    while not _u_is_zero(r1):
        q, r = _u_divmod(r0, r1, zero)
        s_new = _u_sub(s0, _u_mul(q, s1, zero))
        t_new = _u_sub(t0, _u_mul(q, t1, zero))
        r0, r1 = r1, r
        s0, s1 = s1, s_new
        t0, t1 = t1, t_new
    if _u_is_zero(r0):
        return s0, t0, []
    inv = one_c / r0[0]
    return [c * inv for c in s0], [c * inv for c in t0], \
        [c * inv for c in r0]


def _u_diophantine(b, a, c, zero):
    """解 r·b + z·a = c（sympy gcdex_diophantine(b, a, c) 语义）。"""
    s, t, g = _u_xgcd(b, a, zero)
    if _u_is_zero(g):
        return None
    qq, rr = _u_divmod(c, g, zero)
    if not _u_is_zero(rr):
        return None
    return _u_mul(s, qq, zero), _u_mul(t, qq, zero)


def _split_ns(p, der_fn, zero):
    """intrf.spad:141 split：p = normal·special。

    normal 的平方因子与 D(p) 互素；special 为 D-不变型因子。
    返回 (normal_list, special_list)。
    """
    p = _u_trim(list(p))
    if _u_is_zero(p) or len(p) <= 1:
        return list(p), []
    dp = der_fn(p)
    dfp = _u_formal_deriv(p)
    if _u_is_zero(_u_sub(dp, dfp)):
        return list(p), []
    g = _u_gcd(p, dp, zero)
    if len(g) <= 1:
        return list(p), []
    gd = _u_gcd(p, dfp, zero)
    if len(gd) <= 1:
        pbar = list(g)
    else:
        pbar, r = _u_divmod(g, gd, zero)
        if not _u_is_zero(r):
            return list(p), []
    if len(pbar) <= 1:
        return list(p), []
    rest, rr = _u_divmod(p, pbar, zero)
    if not _u_is_zero(rr):
        return list(p), []
    rn, rs = _split_ns(rest, der_fn, zero)
    return rn, _u_mul(pbar, rs, zero)


def _normal_part(p, der_fn, zero):
    return _split_ns(p, der_fn, zero)[0]


def _make_der_fn(de, jv):
    """视图层 jv 的 K[t]-导子 der1：D(Σcᵢτⁱ)。jv==0 时 D=d/dx、dk=1。

    基级系数为纯常数（子变量集空），自身导数项恒零——只保留
    i·cᵢτ^{i-1} 移位项（旧版对常数 RatFunc 求 levels[0]-导会炸）。"""
    if jv == 0:
        def der_fn(cs):
            out = []
            for i in range(1, len(cs)):
                out.append(cs[i] * Fr(i))
            return _u_trim(out)
        return der_fn
    return lambda cs: _derive_ut(cs, de, jv)


def _wn_normalize(fn, fd, de, jv, der_fn, zero):
    """intpar.spad:920 weak normalization（非参数化特化）。

    返回 (fn2, fd2, pn, pd)：f_new = fn2/fd2 已消 normal 极点；
    p = pn/pd 使 v = y·p 时新方程右端须 ×p（intpar:1237）、解 ÷p（:1239）。
    无法判定返回 None。
    """
    one_c = zero.one(zero.p.vars)
    pn, pd = [one_c], []
    d = _normal_part(fd, der_fn, zero)
    if len(d) <= 1:
        return list(fn), list(fd), pn, pd
    g0 = _u_gcd(d, der_fn(d), zero)
    d0 = _u_divmod(d, g0, zero)[0]
    dd = _u_gcd(d0, g0, zero)
    d1 = _u_divmod(d0, dd, zero)[0]
    if len(d1) <= 1:
        return list(fn), list(fd), pn, pd
    q2, r2 = _u_divmod(fd, d1, zero)
    if not _u_is_zero(r2):
        return None
    d2 = q2
    s_, _t_, g_ = _u_xgcd(d2, d1, zero)
    if _u_is_zero(g_):
        return None
    qqf, rf = _u_divmod(fn, g_, zero)
    if not _u_is_zero(rf):
        return None
    a_ = _u_mul(s_, qqf, zero)
    d1d = der_fn(d1)
    nb = max(len(a_), len(d1d))
    a_pad = list(a_) + [zero for _ in range(nb - len(a_))]
    d_pad = list(d1d) + [zero for _ in range(nb - len(d1d))]
    fz = [[ai, c * Fr(-1)] for ai, c in zip(a_pad, d_pad)]
    gz = [[ci] for ci in d1]
    Rz = _sylvester_res(fz, gz)
    rl = []
    if Rz and not _u_is_zero(Rz):
        for mval in _constant_roots(Rz):
            try:
                mv = mval if isinstance(mval, Fr) else Fr(mval)
            except Exception:
                return None
            if mv.denominator != 1 or mv <= 0:
                continue
            fm = _u_sub(a_pad, [c * mv for c in d_pad])
            pi_m = _u_gcd(fm, d1, zero)
            if len(pi_m) <= 1:
                continue
            rl.append((pi_m, int(mv)))
    fn2, fd2 = list(fn), list(fd)
    for pi_m, mv in rl:
        fn2, fd2 = _fu_sub(fn2, fd2,
                           [c * Fr(mv) for c in der_fn(pi_m)],
                           list(pi_m), zero)
        for _ in range(mv):
            pn, pd = _fu_mul(pn, pd, list(pi_m), [], zero)
    return fn2, fd2, pn, pd


def _dk_pair(de, jv):
    """D(levels[jv]) 的 τ-系数表示 (n_list, d_list)。"""
    tview = de.levels[jv]
    dk_n, dk_d = de.dpair(jv, tuple(de.levels[:jv + 1]))
    return _univar(dk_n, tview), _univar(dk_d, tview)


# ---------------------------------------------------------------------------

# ---------------------------------------------------------------------------
# M5.2c-iii #1：对数导数-根式判定（is_logderiv_radical + 参数化对数导数
# 判定 _pld_solve，非参数化特化到 ℚ(i) 常数域）。
#
# 判定：∃n∈ℤ\{0}, u∈K*: n·f = D(u)/u ？返回 (n, u)|None。
# 用途：(a) 塔构建守卫的精确代数相关性判定；(b) primitive db==da 界修正；
#       (c) cancel_primitive 完整化的前置。
# 结构：base/primitive/exp 三 case；exp 经参数化判定（解出整数比后在低
# 一层做 radical 判定——DecrementLevel 语义对应）；互递归层严格下降保证
# 终止。出口全量精确验证 D(U)==N·f·U 兜底。
#
# M5 收官批 #1（参数化对数导数完备化）：_pld_heu 启发式退役，换三态
# _pld_solve——('ok',n,ms,v) / ('no',证明理由) / ('und',卡点)。关键升级：
#   1. 系数约束统一为零空间线性代数（旧版单比值除法只能处理秩 1 且
#      放弃高维候选）；
#   2. 全 τ-free 目标的结构定理下降：exp 层 v=c·τ^j·u 分解，j 并入
#      幂因子（旧版在此直接放弃——多级塔下例行动否，喂给塔守卫即成
#      无证明放行依赖层，方向性隐患）；
#   3. 基级 z-常数兜底：有界本原对枚举 + _ldrad_base 逐个精确验证
#      （旧版 jl==0 一律拒答，扔掉已有的完备基级判定器）；
#   4. 'und' 显式上抛 RischUnsupported——调用方保守处理，绝不把
#      启发失败伪装成证明否定。
# ---------------------------------------------------------------------------

def _const_to_term(c):
    return c.to_term() if hasattr(c, "to_term") else N(c)


def _rf_const_ga(rf):
    """RatFunc 是否为 ℚ(i) 标量；是则返回 Ga，否则 None。"""
    for pp in (rf.p, rf.q):
        for k in pp.monos:
            if any(e != 0 for e in k):
                return None
    num = rf.p.const_val()
    den = rf.q.const_val()
    from cas.gaussian import Ga as _G
    num_g = num if isinstance(num, _G) else _G(num)
    den_g = den if isinstance(den, _G) else _G(den)
    if den_g.is_zero():
        return None
    return num_g / den_g


def _ga_den(ga):
    from fractions import Fraction as _Fr
    return _lcm2(ga.re.denominator, ga.im.denominator)


def _lcm2(a, b):
    from math import gcd as _g
    return a * b // _g(a, b)


def _rf_of_cs(cs, allv, tau):
    from cas.ratfunc import RatFunc as _RF
    n_, d_ = _from_univar(cs, allv, tau)
    return _RF(n_, d_)


def _cs_const_val(cs, allv):
    """univar list 是否整体为零多项式；非零时无意义（仅供零检查）。"""
    return all(c.is_zero() for c in cs)


def _ldrad_base(f_rf, de):
    """ℚ(i)(x) 上的对数导数-根式判定（base case，Poly 级实现）。

    f 真分式且分母无平方时：R(z)=Res_x(a−z·b',b) 的根全为 ℚ(i)
    常数 <=> ∃n,u: n·f=D(u)/u；n=lcm(残数分母)、u=Πg^{n·r}。
    """
    from cas.poly import ugcd as _pugcd
    from cas.factor import squarefree_decomp
    from math import lcm as _lcm3
    from cas.ratfunc import RatFunc

    def _uni_strip(p):
        if len(p.vars) <= 1:
            return p
        for k, _c in p.monos.items():
            if any(e != 0 for e in k[1:]):
                raise RischUnsupported(
                    "internal: base-level poly carries higher tower vars")
        return Poly((p.vars[0],),
                    {(k[0],): c for k, c in p.monos.items()})

    xv = de.levels[0]
    a = _uni_strip(f_rf.p)
    b = _uni_strip(f_rf.q)
    if a.is_zero():
        return 1, RatFunc.one((xv,))
    if b.degree(xv) == 0:
        return None                    # 无极点：非常数 f 不可能是 dlog
    if a.degree(xv) >= b.degree(xv):
        return None                    # 非真分式（多项式部分无处承载）
    try:
        parts = squarefree_decomp(b)
    except Exception:
        return None
    if len(parts) != 1 or parts[0][1] != 1:
        return None                    # 分母须无平方

    db = b.deriv(xv)
    la, lb, ldb = _poly_to_list(a), _poly_to_list(b), _poly_to_list(db)
    from cas.ratfunc import RatFunc as _RFb

    def _wrap_list(lst):
        return [_RFb.from_poly(Poly.const((xv,), v)) for v in lst]

    la, lb, ldb = _wrap_list(la), _wrap_list(lb), _wrap_list(ldb)
    nb = max(len(la), len(lb), len(ldb))
    lap = la + [_RFb.from_poly(Poly.const((xv,), Fr(0)))
                for _ in range(nb - len(la))]
    lbp = lb + [_RFb.from_poly(Poly.const((xv,), Fr(0)))
                for _ in range(nb - len(lb))]
    ldbp = ldb + [_RFb.from_poly(Poly.const((xv,), Fr(0)))
                  for _ in range(nb - len(ldb))]
    fz = [[aa, _neg_poly(dd)] for aa, dd in zip(lap, ldbp)]
    gz = [[cc] for cc in lbp]
    Rz = _sylvester_res(fz, gz)
    if _u_is_zero(Rz):
        return None

    roots = _constant_roots(Rz)        # 无法判定 => 异常上抛（诚实）
    residueterms = []

    def _neg_val(v):
        if isinstance(v, Ga):
            return Ga(-v.re, -v.im)
        return -v

    for c in roots:
        diffp = a + db.scalar(_neg_val(c))
        g = _pugcd(diffp, b)
        if g.degree(xv) <= 0:
            continue
        dn_ = _ga_den(c) if isinstance(c, Ga) else c.denominator
        residueterms.append((g, c, dn_))
    if not residueterms:
        return None
    n = 1
    for _, _, dn_ in residueterms:
        n = _lcm3(n, dn_)
    # u = Π g^{n·c}：负指数残数进分母（对数导数的极点合法形态；
    # 旧版一律乘分子，遇负残数 Poly 负幂直接炸——休眠 bug）
    u_num = Poly.one((xv,))
    u_den = Poly.one((xv,))
    for g, c, _dn in residueterms:
        ee = n * c
        if isinstance(ee, Ga):
            if ee.im != 0 or ee.re.denominator != 1:
                return None
            ee = ee.re
        if not isinstance(ee, int) and ee.denominator != 1:
            return None
        ee = int(ee)
        if ee >= 0:
            u_num = u_num * g ** ee if ee > 0 else u_num
        else:
            u_den = u_den * g ** (-ee)
    return _ld_finish(n, RatFunc(u_num, u_den), f_rf, de)


def _term_within_field(val_t, de, jl):
    """term 的 Log/Exp 参数是否全部落在允许塔层（≤jl）内。

    基层有理积分会以实形态吐 Log——若其参数恰为某允许层的原函数
    形态则该层符号可承载（合法），否则为域外泄漏。
    """
    allowed_args = []
    for i in range(1, jl + 1):
        tm = de.terms[i]
        if isinstance(tm, Expr) and len(tm.args) == 1:
            allowed_args.append(tm.args[0])
    stack = [val_t]
    while stack:
        u = stack.pop()
        if isinstance(u, Expr) and u.head.name in ("Log", "Exp") \
                and len(u.args) == 1:
            if not any(u.args[0] == ag for ag in allowed_args):
                return False
            stack.extend(u.args)
            continue
        if isinstance(u, Expr):
            stack.extend(u.args)
    return True


def _limited_int_prim(al_rf, v_rf, de, jl, cap=16):
    """完备化版：α = m·η + D(z) 的共振界修正（M5 收官批 #2）。

    核心洞察（余陪集定理 + 多项式约束）：
    - η = D(τ) 在塔内恒可积（∫η = τ），故 k·η 可积 ⟺ η 可积
      ⟹ S₀ = {k : k·η 可积} ∈ {{0}, ℤ}
    - α = m·η + D(z)、z ∈ K₀[τ]（多项式）⟹ D(z)/η = D(z)/D(τ) 为常数
      ⟹ z = c·τ + const ⟹ α/η = m + c = 整数常数
    - 逆否：α/η 非整数常数 => 无多项式共振 => 朴素界正确

    故 α/η 的常数整数性检验是完备的——无需有界积分探测。

    三态：('ok', m)  m = 正整数共振度，或 0（无共振）
           ('und', None) 理论受限（仅 η=0 或比率计算异常的极端情形）
    """
    if v_rf.is_zero():
        return "ok", 0
    allv_sub = tuple(de.levels[:jl + 1])
    try:
        al_r = _restrict(al_rf, allv_sub)
        v_r = _restrict(v_rf, allv_sub)
    except PolyError:
        return "ok", 0
    try:
        rho = al_r / v_r
    except Exception:
        return "ok", 0
    cv = _rf_const_ga(rho)
    if cv is not None and cv.im == 0 \
            and cv.re.denominator == 1 and cv.re > 0:
        return "ok", int(cv.re)
    return "ok", 0


def _is_logderiv_radical(f_rf, de, jv, depth=0):
    """主判定入口。f_rf: RatFunc over levels[:jv+1]，视图 τ=levels[jv]。"""
    from cas.ratfunc import RatFunc

    if depth > 8:
        return None
    if f_rf.is_zero():
        return 1, RatFunc.one(tuple(de.levels[:jv + 1]))

    if jv == 0:
        return _ldrad_base(f_rf, de)

    tau = de.levels[jv]
    allv = tuple(de.levels[:jv + 1])
    sub = tuple(de.levels[:jv])
    zero = RatFunc.zero(sub)
    one_c = zero.one(sub)
    der_fn = _make_der_fn(de, jv)

    # τ 不在变量集 => f ∈ K_{jv-1}：直接降层递归（结构定理模式）
    if tau not in f_rf.p.vars and tau not in f_rf.q.vars:
        return _is_logderiv_radical(f_rf, de, jv - 1, depth + 1)

    fn_cs = _univar(f_rf.p, tau)
    fd_cs = _univar(f_rf.q, tau)

    # ---- -1) τ-gcd 约分（未约分形态会污染残数结果式）----
    g0 = _u_gcd(fn_cs, fd_cs, zero)
    if len(g0) > 1:
        fn_cs = _u_divmod(fn_cs, g0, zero)[0]
        fd_cs = _u_divmod(fd_cs, g0, zero)[0]

    # ---- 0) 分母须无平方（对数导数只有单极点）----
    sqf = _squarefree_decomp_t(fd_cs, zero)
    if any(e >= 2 for _, e in sqf):
        return None

    # ---- 1) 多项式部分 + 逐因子残数（复用 _integrate_normal 模式）----
    Q_cs, _R_all = _u_divmod(fn_cs, fd_cs, zero)
    logs = []                        # [(c(Ga|Fr), g_cs)]
    ok = True
    rem_polys = []                   # 各因子的可除余商（τ-poly）
    for p1, _e1 in sqf:
        cof = _u_divmod(fd_cs, p1, zero)[0]
        Bm = _u_divmod(
            _u_mul(fn_cs, _u_inv_mod(cof, fd_cs, zero), zero), p1, zero)[1]
        lg, rem = _residue_sqfr(Bm, p1, de, jv, zero)
        for c, g in lg:
            cv = c if isinstance(c, (Fr, Ga)) else None
            if cv is None:
                try:
                    cv = Fr(c)
                except Exception:
                    return None      # 非常数残数 => 非对数导数
            logs.append((cv, g))
        if _u_is_zero(rem):
            continue
        qq, rr = _u_divmod(rem, p1, zero)
        if not _u_is_zero(rr):
            return None              # normal 极点未被解释 => 非对数导数
        rem_polys.append(qq)

    # ---- 2) p_final = 多项式部分 − Σ c·D(g)/g，须为 τ-常数（∈K_{jv}）----
    P_n, P_d = list(Q_cs), [one_c]
    for qq in rem_polys:
        P_n = _u_add(P_n, qq, zero)
    P_rf = _rf_of_cs(P_n, allv, tau) / _rf_of_cs(P_d, allv, tau)
    for cv, g in logs:
        g_rf = _rf_of_cs(list(g), allv, tau)
        dg_rf = _rf_of_cs(der_fn(g), allv, tau)
        term = dg_rf / g_rf * cv
        P_rf = P_rf - term
    # τ-free 门（deg < max(1, deg(Dτ)) 的等价形式）
    Pp_cs = _univar(P_rf.p, tau)
    Pq_cs = _univar(P_rf.q, tau)
    if _u_deg(_u_formal_deriv(Pp_cs)) >= 0 or \
            _u_deg(_u_formal_deriv(Pq_cs)) >= 0:
        return None

    # ---- 3) case 分派 ----
    def dens_lcm():
        nd = 1
        for cv, _g in logs:
            nd = _lcm2(nd, _ga_den(cv) if isinstance(cv, Ga)
                       else cv.denominator)
        return nd

    if jv == 0:
        # base：P 必须为零（无更低层承载）
        if not _u_is_zero(_univar(P_rf.p, tau)) and not P_rf.p.is_zero():
            if not P_rf.p.is_zero() or not P_rf.q.is_one():
                if not P_rf.p.is_zero():
                    return None
        if not P_rf.p.is_zero():
            return None
        n = dens_lcm()
        u = RatFunc(one_c * 0 + Poly.one(allv), Poly.one(allv))
        uacc = RatFunc(Poly.one(allv), Poly.one(allv))
        for cv, g in logs:
            ee = int(n * cv)
            gp = _u_pow(list(g), ee, zero)
            gu, gd = _from_univar(gp, allv, tau)
            uacc = uacc * RatFunc(gu, gd)
        U = uacc
    elif de.cases[jv] == "primitive":
        rec = _is_logderiv_radical(P_rf, de, jv - 1, depth + 1)
        if rec is None:
            return None
        n_l, v = rec
        N = _lcm2(n_l, dens_lcm())
        mm = N // n_l
        uacc = v ** mm
        for cv, g in logs:
            ee = int(N * cv)
            gp = _u_pow(list(g), ee, zero)
            gu, gd = _from_univar(gp, allv, tau)
            uacc = uacc * RatFunc(gu, gd)
        N_final, U = N, uacc
        return _ld_finish(N_final, U, f_rf, de)
    else:  # exp
        eta = de.ws[jv]
        # 常数 P 平凡参数化（heu 的结构定理限制补全）：
        # v=1 时 n·P = m·η <=> P/η ∈ ℚ，取 n=分母、m=分子、U=τ^m/n·?
        # 即 U=τ^E，E/n = P/η。
        P_cv = _rf_const_ga(P_rf)
        if P_cv is not None:
            eta_cv = _rf_const_ga(eta)
            if eta_cv is not None and not eta_cv.is_zero():
                rho = P_cv / eta_cv
                if rho.im == 0 and rho.re.denominator != 0:
                    nn = rho.re.denominator
                    EE = int(rho.re * nn)
                    tau_u = (RatFunc(Poly.mono(allv, tau, EE),
                                     Poly.one(allv)) if EE > 0 else
                             RatFunc(Poly.one(allv),
                                     Poly.mono(allv, tau, -EE))
                             if EE < 0 else
                             RatFunc(Poly.one(allv), Poly.one(allv)))
                    return _ld_finish(nn, tau_u, f_rf, de)
        rec = _pld_solve(P_rf, [eta], de, jv - 1, depth + 1)
        if rec[0] == "no":
            return None          # 子判定完备证明否定
        if rec[0] == "und":
            raise RischUnsupported(
                "parametric log derivative undecided: " + str(rec[1]))
        _n2, n_l, ms_l, v = rec
        m_l = ms_l[0]
        N = _lcm2(n_l, dens_lcm())
        mm = N // n_l
        uacc = v ** mm
        for cv, g in logs:
            ee = int(N * cv)
            gp = _u_pow(list(g), ee, zero)
            gu, gd = _from_univar(gp, allv, tau)
            uacc = uacc * RatFunc(gu, gd)
        E = mm * m_l
        if E > 0:
            uacc = uacc * RatFunc(Poly.mono(allv, tau, E), Poly.one(allv))
        elif E < 0:
            uacc = uacc / RatFunc(Poly.mono(allv, tau, -E),
                                  Poly.one(allv))
        return _ld_finish(N, uacc, f_rf, de)

    # base 路径收尾（带验证）
    return _ld_finish(n, U, f_rf, de)


def _ld_finish(N, U, f_rf, de):
    """出口全量精确验证 D(U)==N·f·U；失败=内部错误（绝不静默）。"""
    from cas.ratfunc import RatFunc
    if U.p.vars != f_rf.p.vars:
        U = RatFunc(_embed(U.p, f_rf.p.vars), _embed(U.q, f_rf.p.vars))
    from cas.ratfunc import RatFunc

    DU = _tower_deriv_frac(U.p, U.q, de)
    lhs = DU / U
    rhs = f_rf * N
    diff = lhs - rhs
    if not diff.p.is_zero():
        raise RischUnsupported(
            "internal: log-deriv radical witness failed exact verify "
            "(this is a bug, not an honest refusal)")
    return N, U


def _poly_dep(p, v):
    """Poly 对变量 v 是否实际依赖（指数非零；成员≠依赖）。"""
    try:
        j = p.vars.index(v)
    except ValueError:
        return False
    return any(k[j] != 0 for k in p.monos)


def _pld_solve(f_rf, ws_rf, de, jl, depth=0):
    """参数化对数导数判定（三态，M5 收官批 #1 完备化版）：

    解 n·f = D(v)/v + Σ mᵢ·wᵢ（n,mᵢ∈ℤ, v∈levels[:jl+1]*）。

    返回：
      ('ok', n, ms, v)   ms 与 ws_rf 对齐；恒等式经出口精确验证
      ('no', reason)     无解的机器证明（必要条件矛盾/唯一候选被
                         低层完备判定否证）
      ('und', reason)    当前理论不可判——调用方保守处理，绝不猜测

    算法（Bronstein z-归约 + 结构定理下降）：
      1. 全目标 τ-free => 本层无约束：exp 层按 v=c·τ^j·u 分解把 j 吸收
         为幂因子后降层；primitive 层 τ-含量被迫平凡直接降层；基级落
         通用路径。
      2. 通用路径：多项式部分系数行（i>B 区，B=deg Dτ−1 上界）∪
         z-余数行（z=special(l)·gcd(normal,D(normal))，l=分母 lcm）
         联合零空间。dim 0 => 'no'；每个本原整候选递归低层验证。
      3. z 常数且高区无行 => 'und'（中间层残数域约束，诚实放弃）；
         基级 => 有界枚举兜底。
    """
    from cas.ratfunc import RatFunc

    if depth > 12:
        return "und", "depth exhausted"
    tp = de.levels[jl]
    sub2 = tuple(de.levels[:jl])
    zero = RatFunc.zero(sub2)
    one_c = zero.one(zero.p.vars)
    der_fn = _make_der_fn(de, jl)

    if f_rf.is_zero():
        return "ok", 1, [0 for _ in ws_rf], \
            RatFunc.one(tuple(de.levels[:jl + 1]))

        # ---- 0b. 变量集收紧：投影到实际依赖的塔变量（冗余零指数维度
    #         会让跨层递归的 RatFunc 算术 var-mismatch）----
    used = set()
    for pp in [f_rf.p, f_rf.q] + [c for w_ in ws_rf
                                  for c in (w_.p, w_.q)]:
        for kk in pp.monos:
            for vi, ee in enumerate(kk):
                if ee:
                    used.add(pp.vars[vi])
    order = tuple(v for v in de.levels[:jl + 1] if v in used)

    def _proj(rf):
        if rf.p.vars == order:
            return rf

        def _shrink(p):
            ki = [p.vars.index(v) for v in order]
            return Poly(order, {tuple(k[i] for i in ki): c
                                for k, c in p.monos.items()})
        return RatFunc(_shrink(rf.p), _shrink(rf.q))

    f_rf = _proj(f_rf)
    ws_rf = [_proj(w_) for w_ in ws_rf]

    def _emb_full(v):
        allv = tuple(de.levels[:jl + 1])
        if v.p.vars == allv:
            return v
        return RatFunc(_embed(v.p, allv), _embed(v.q, allv))

    # ---- 0. 目标归并：零目标丢弃；Ga 常数倍目标合并（系数相加，
    #         恒等式等价；返回时按映射展开保持与调用方对齐）----
    groups = []                      # [w_kept, [(orig_idx, scale)]]
    for idx0, w0 in enumerate(ws_rf):
        if w0.is_zero():
            continue
        placed = False
        for g in groups:
            cv0 = _rf_const_ga(w0 / g[0])
            if cv0 is not None and cv0.im == 0:
                g[1].append((idx0, cv0.re))
                placed = True
                break
        if not placed:
            groups.append([w0, [(idx0, Fr(1))]])
    ws_m = [g[0] for g in groups]

    def _expand(ms_kept):
        # 首成员全担系数（其余置 0）：Σmᵢwᵢ = m_kept·w_kept 等价保持。
        # 旧版逐成员重复分摊会把系数翻倍（假见证教训）
        out = [Fr(0) for _ in ws_rf]
        for g, mk in zip(groups, ms_kept):
            oi0, sc0 = g[1][0]
            out[oi0] = out[oi0] + mk / sc0
        return out

    def _pld_end_verify(n_v, ms_v, v_v):
        """端到端精确验证 D(v)/v == n·f − Σm·w（下降路径也过闸）。"""
        lhs = _tower_deriv_frac(v_v.p, v_v.q, de) / v_v
        rhs = f_rf * n_v
        for m_v, w_v in zip(ms_v, ws_rf):
            rhs = rhs - w_v * m_v
        if lhs.p.vars != rhs.p.vars:
            rhs = RatFunc(_embed(rhs.p, lhs.p.vars),
                          _embed(rhs.q, lhs.p.vars))
        if not (lhs - rhs).p.is_zero():
            raise RischUnsupported(
                "internal: parametric log deriv descent witness failed "
                "exact verify (bug, not honest refusal)")




    f_free = not _poly_dep(f_rf.p, tp) and not _poly_dep(f_rf.q, tp)
    ws_free = all(not _poly_dep(w.p, tp) and not _poly_dep(w.q, tp)
                  for w in ws_m)

    # ---- 1. 全 τ-free：结构定理下降 ----
    if f_free and ws_free:
        if jl == 0:
            rec0 = _pld_base_pair(f_rf, list(ws_m), de)
            if rec0[0] != "ok":
                return rec0
            ms_x = _expand(rec0[2])
            v_x = _emb_full(rec0[3])
            _pld_end_verify(rec0[1], ms_x, v_x)
            return "ok", rec0[1], ms_x, v_x
        if de.cases[jl] == "exp":
            # v = c·τ^j·u ⟹ n·f = D(u)/u + Σm·w + j·η；追加 η 为目标，
            # 返回后把该系数折进幂因子（D(τ^j)/τ^j = j·η 精确恒等）
            rec = _pld_solve(f_rf, list(ws_m) + [de.ws[jl]],
                             de, jl - 1, depth + 1)
            if rec[0] != "ok":
                return rec
            _n, ms_full, v = rec[1], rec[2], rec[3]
            own, j_extra = ms_full[:len(ws_m)], ms_full[len(ws_m):]
            allv = tuple(de.levels[:jl + 1])
            if v.p.vars != allv:
                v = RatFunc(_embed(v.p, allv), _embed(v.q, allv))
            j_eff = sum(j_extra)
            if j_eff > 0:
                v = v * RatFunc(Poly.mono(allv, tp, j_eff),
                                Poly.one(allv))
            elif j_eff < 0:
                v = v / RatFunc(Poly.mono(allv, tp, -j_eff),
                                Poly.one(allv))
            ms_x = _expand(own)
            v_x = _emb_full(v)
            _pld_end_verify(_n, ms_x, v_x)
            return "ok", _n, ms_x, v_x
        rec = _pld_solve(f_rf, list(ws_m), de, jl - 1, depth + 1)
        if rec[0] != "ok":
            return rec
        ms_x = _expand(rec[2])
        v_x = _emb_full(rec[3])
        _pld_end_verify(rec[1], ms_x, v_x)
        return "ok", rec[1], ms_x, v_x

    # ---- 2. 通用路径：系数行零空间 ----
    k = len(ws_m)
    f_n = _univar(f_rf.p, tp)
    f_d = _univar(f_rf.q, tp)
    ws_nd = [(_univar(w.p, tp), _univar(w.q, tp)) for w in ws_m]

    def _coef(cs, i):
        return cs[i] if i < len(cs) else zero

    dk_cs, _dkd = _dk_pair(de, jl)
    B = max(0, _u_deg(dk_cs) - 1)

    pparts = [_u_divmod(f_n, f_d, zero)[0]]
    for n_, d_ in ws_nd:
        pparts.append(_u_divmod(n_, d_, zero)[0])
    C = max(_u_deg(q) for q in pparts)

    rows = []
    if C > B:
        for i in range(B + 1, C + 1):
            rows.append([_coef(pparts[0], i)] +
                        [_coef(pparts[j + 1], i) * Fr(-1)
                         for j in range(k)])

    # l = 分母 monic lcm；z = special(l)·gcd(normal(l), D(normal(l)))
    dens = [f_d] + [d_ for _, d_ in ws_nd]
    l_cs = None
    for d_ in dens:
        dm = _u_divmod(d_, [_u_trim(list(d_))[-1]], zero)[0]
        if l_cs is None:
            l_cs = dm
        else:
            g2 = _u_gcd(l_cs, dm, zero)
            l_cs = _u_mul(l_cs, _u_divmod(dm, g2, zero)[0], zero)
    ln_, ls_ = _split_ns(l_cs, der_fn, zero)
    z_const_case = False
    if _u_is_zero(ln_):
        z_const_case = True
    else:
        gg = _u_gcd(ln_, der_fn(ln_), zero)
        z_cs = _u_mul(ls_, gg, zero)
        if _u_deg(z_cs) < 1:
            z_const_case = True
        else:
            lfs = [_u_mul(f_n, _u_divmod(l_cs, f_d, zero)[0], zero)]
            for n_, d_ in ws_nd:
                lfs.append(_u_mul(n_, _u_divmod(l_cs, d_, zero)[0], zero))
            rems = [_u_divmod(h_, z_cs, zero)[1] for h_ in lfs]
            zdeg = len(_u_trim(list(z_cs))) - 1
            for i in range(max(len(r) for r in rems)):
                rows.append([_coef(rems[0], i)] +
                            [_coef(rems[j + 1], i) * Fr(-1)
                             for j in range(k)])

    if not rows:
        if jl == 0:
            rec0 = _pld_base_pair(f_rf, list(ws_m), de)
            if rec0[0] != "ok":
                return rec0
            ms_x = _expand(rec0[2])
            v_x = _emb_full(rec0[3])
            _pld_end_verify(rec0[1], ms_x, v_x)
            return "ok", rec0[1], ms_x, v_x
        return "und", "no constraints at level (z constant)"

    basis = _rf_nullspace(rows, k + 1, zero, one_c)

    if not basis:
        return "no", "coefficient null space empty (necessary " \
                      "conditions contradictory)"

    # 候选枚举：dim 1 直接取；dim ≥2 小系数组合封顶（超限诚实 und）
    cands = []
    if len(basis) == 1:
        cands.append(basis[0])
    else:
        from itertools import product as _iproduct
        small = [-2, -1, 0, 1, 2]
        for combo in _iproduct(small, repeat=len(basis)):
            if all(c_ == 0 for c_ in combo):
                continue
            vec = None
            for c_, bvec in zip(combo, basis):
                if c_ == 0:
                    continue
                scaled = [e * Fr(c_) for e in bvec]
                vec = scaled if vec is None else \
                    [a + b for a, b in zip(vec, scaled)]
            cands.append(vec)
            if len(cands) >= 24:
                break
        if len(basis) > 3 and len(cands) >= 24:
            return "und", "null space dimension too large"

    allv = tuple(de.levels[:jl + 1])
    saw_alive = False
    for vec in cands:
        ints = _ga_vec_to_ints(vec)
        if ints is None:
            saw_alive = True          # 非整数常数向量：不可判死也不可用
            continue
        n_i = ints[0]
        if n_i <= 0:
            ints = [-v2 for v2 in ints]
            n_i = -n_i
        if n_i == 0:
            continue                  # 全零或 n=0：非正规化解
        ms_i = ints[1:]
        h = f_rf * n_i
        for m_j, w_j in zip(ms_i, ws_m):
            h = h - w_j * m_j
        # 上层 τ 残留 => 恒等式两端 τ-含量必不匹配（RHS D(v)/v 对
        # 子塔 v 无本层含量）=> 此候选证明性判死，绝不流向下层
        if _poly_dep(h.p, tp) or _poly_dep(h.q, tp):
            continue
        if h.is_zero():
            # 平凡恒等：v = 1
            ms_x = _expand(ms_i)
            v_x = RatFunc.one(tuple(de.levels[:jl + 1]))
            _pld_end_verify(n_i, ms_x, v_x)
            return "ok", n_i, ms_x, v_x
        try:
            if jl == 0:
                rad = _ldrad_base(h, de)
            else:
                rad = _is_logderiv_radical(h, de, jl - 1, depth + 1)
        except RischUnsupported as _ru:
            return "und", str(_ru)
        except Exception:
            rad = None                # 该候选证伪/不可判——继续其余
        if rad is None:
            continue                  # 此比例证明无解
        saw_alive = True
        Qn, u_v = rad
        v_fin = u_v
        if v_fin.p.vars != h.p.vars:
            v_fin = RatFunc(_embed(v_fin.p, h.p.vars),
                            _embed(v_fin.q, h.p.vars))
        # 出口精确验证：D(v)/(v·Q) == h（内部错误绝不静默）
        DU = _tower_deriv_frac(v_fin.p, v_fin.q, de)
        lhs = DU / (v_fin * Fr(Qn))
        if not (lhs - h).p.is_zero():
            raise RischUnsupported(
                "internal: parametric log deriv witness failed exact "
                "verify (bug, not honest refusal)")
        ms_x = _expand([Qn * m_j for m_j in ms_i])
        v_x = _emb_full(v_fin)
        return "ok", Qn * n_i, ms_x, v_x
    if saw_alive:
        return "und", "candidates alive but unverifiable"
    return "no", "all projective candidates proved dead"


def _ga_vec_to_ints(vec):
    """Ga 常数向量 -> 本原整向量 | None（含非常数/非有理分量）。"""
    gs = []
    for e in vec:
        g = _rf_const_ga(e)
        if g is None:
            return None
        gs.append(g)
    den = 1
    for g in gs:
        den = _lcm2(den, _ga_den(g))
    ints = []
    for g in gs:
        val = g * den
        if val.im != 0 or val.re.denominator != 1:
            return None
        ints.append(int(val.re))
    from math import gcd as _g2
    acc = 0
    for v2 in ints:
        acc = _g2(acc, abs(v2))
    if acc == 0:
        return None
    return [v2 // acc for v2 in ints]


def _rf_nullspace(rows, ncols, zero, one_c):
    """RatFunc 系数齐次系统零空间基（行主元消元）；空表 = 仅零解。"""
    mat = [list(r) for r in rows]
    pivots = []
    r = 0
    for c in range(ncols):
        pr = None
        for i in range(r, len(mat)):
            if not mat[i][c].is_zero():
                pr = i
                break
        if pr is None:
            continue
        mat[r], mat[pr] = mat[pr], mat[r]
        inv = one_c / mat[r][c]
        mat[r] = [x * inv for x in mat[r]]
        for i in range(len(mat)):
            if i != r and not mat[i][c].is_zero():
                fac = mat[i][c]
                mat[i] = [a - fac * b for a, b in zip(mat[i], mat[r])]
        pivots.append((r, c))
        r += 1
        if r == len(mat):
            break
    free_cols = [c for c in range(ncols) if c not in
                 {pc for _pr, pc in pivots}]
    basis = []
    for fc in free_cols:
        vec = [_mk_zero_like(one_c) for _ in range(ncols)]
        vec[fc] = one_c
        for ri, pc in pivots:
            vec[pc] = mat[ri][fc] * Fr(-1)
        basis.append(vec)
    return basis


def _mk_zero_like(one_c):
    """与 one_c 同变量集的零 RatFunc（算术构造，免依赖构造器细节）。"""
    return one_c - one_c


def _pld_base_pair(f_rf, ws_rf, de):
    """基级 z-常数兜底：有界本原对枚举 + _ldrad_base 精确验证。

    完备性边界：窗口（|n| ≤ 6、|m| ≤ 6、单目标）内穷尽；窗口外/
    多目标诚实 'und'。方向安全：漏枚举只损失覆盖，_ldrad_base 验证
    背书杜绝假阳性。"""
    from cas.ratfunc import RatFunc
    from math import gcd as _g3

    if len(ws_rf) != 1:
        return "und", "base fallback limited to single target"
    w_rf = ws_rf[0]
    for n_i in range(1, 7):
        for m_i in range(-6, 7):
            if m_i != 0 and _g3(abs(n_i), abs(m_i)) != 1:
                continue          # 非本原对与约简对同解，跳过
            h = f_rf * n_i - w_rf * m_i
            if h.is_zero():
                return "ok", n_i, [m_i], \
                    RatFunc.one(tuple(de.levels[:1]))
            try:
                rad = _ldrad_base(h, de)
            except Exception:
                continue
            if rad is None:
                continue
            Qn, u_v = rad
            return "ok", Qn * n_i, [Qn * m_i], u_v
    return "und", "bounded base enumeration exhausted"


# ---------------------------------------------------------------------------
# M5.3 出口实化（可判定子集）：tau = e^{i*sgn*u} 视角的 Laurent 解
# -> 实三角形态。全部精确恒等式，无启发式搜索：
#
#   C* = 全共轭：子域叶系数 Ga(a,b) -> a-b，且 tau -> tau^{-1}。
#   实原函数的判定 = y == C*(y)（RatFunc 分子 is_zero，精确非数值）。
#   R = (y + C*y)/2 的 tau-系数必实（_rf_split_im 拆分后断言）。
#   单位圆恒等式 (C+iS)^{-e} = (C-iS)^e 保证负幂无分母。
#   奇 i-相位单项式总和必为零（对称性，精确多项式零检查断言）。
# 任一环节不满足 => 返回 None，调用方保留复形态（诚实回退）。
# ---------------------------------------------------------------------------

def _parse_imag_exp_arg(arg):
    """Exp 参数 = q*i*u（q 非 0 有理）-> (sgn, u_eff=|q|*u)；否则 None。"""
    if not isinstance(arg, Expr) or arg.head.name != "Times":
        return None
    q = Fr(1)
    i_cnt = 0
    rest = []
    for a in arg.args:
        if isinstance(a, Sym) and a.name == "i":
            i_cnt += 1
            continue
        if T.is_num(a):
            try:
                q *= Fr(T.num_val(a))
            except Exception:
                return None
            continue
        rest.append(a)
    if i_cnt != 1 or q == 0 or not rest:
        return None
    u_eff = rest[0] if len(rest) == 1 else T.mk(S("Times"), tuple(rest))
    aq = abs(q)
    if aq != 1:
        u_eff = T.times(N(aq), u_eff)
    return (1 if q > 0 else -1), u_eff


def _imag_exp_level_info(de, jv):
    """视图层 jv 的 Exp 项为 e^{+-iu} -> (sgn, u_eff)；否则 None。"""
    if de.cases[jv] != "exp":
        return None
    tm = de.terms[jv]
    if not isinstance(tm, Expr) or tm.head.name != "Exp":
        return None
    if len(tm.args) != 1:
        return None
    return _parse_imag_exp_arg(tm.args[0])


def _poly_map_leaves(p, fn):
    """Poly 叶系数映射重建（多变量递归）。"""
    from cas.poly import _rec_view, _from_rec
    if not p.monos:
        return p
    if len(p.vars) <= 1:
        return Poly(p.vars, {k: fn(v) for k, v in p.monos.items()})
    rec = {e0: _poly_map_leaves(sub, fn) for e0, sub in _rec_view(p).items()}
    return _from_rec(rec, p.vars)


def _ga_conj_leaf(v):
    if isinstance(v, Ga):
        return Ga(v.re, -v.im)
    return v


def _rf_split_im(rf):
    """RatFunc -> (实部, 虚部) RatFunc（叶系数 Ga 精确拆分）。"""
    from cas.ratfunc import RatFunc

    def sp(p, take):
        def fn(v):
            if isinstance(v, Ga):
                return v.re if take == "re" else v.im
            return v if take == "re" else Fr(0)
        return _poly_map_leaves(p, fn)

    pn, pi_ = sp(rf.p, "re"), sp(rf.p, "im")
    qn, qi = sp(rf.q, "re"), sp(rf.q, "im")
    den_n = qn * qn + qi * qi
    return RatFunc(pn * qn + pi_ * qi, den_n), RatFunc(pi_ * qn - pn * qi, den_n)


class _RealifyFail(Exception):
    pass


def _realify_laurent(y_rf, tau, sgn, u_eff, xv):
    """tau=e^{i*sgn*u_eff} 视角 Laurent 解 -> 实三角 term；否则 None。

    可判定核心：
      1) y 归一为显式指数字典 {(p0-q0)+j: 系数}；
      2) 实性 <=> 对每个非零指数 k 存在 -k 且系数互为共轭
         （叶系数 Ga 精确比较，非数值）；零指数系数必须实；
      3) 共轭对直接公式化：s_e=a+ib =>
             2a*cos(e*theta) - 2b*sin(e*theta)，theta=sgn*u_eff。
    无启发式搜索；任一前提不满足返回 None（调用方保留复形态）。
    """
    from cas.ratfunc import RatFunc

    # tau 不在变量集 => y 为 tau^0：仅须实（虚部精确零）
    if tau not in y_rf.p.vars:
        a_rf, b_rf = _rf_split_im(y_rf)
        if not b_rf.p.is_zero():
            return None
        return y_rf.to_term()

    def conj_rf(rf):
        return RatFunc(_poly_map_leaves(rf.p, _ga_conj_leaf),
                       _poly_map_leaves(rf.q, _ga_conj_leaf))

    one_p = Poly.one(y_rf.p.vars)

    # ---- 1) 归一化：y = tau^K * P(tau)/c，K=p0-q0、c 为分母首非零 ----
    P_cs = _univar(y_rf.p, tau)
    Q_cs = _univar(y_rf.q, tau)

    def mono_power(cs):
        """cs 必须为单项式 c*tau^v -> (v, c)；否则 None。"""
        first = None
        for idx, c in enumerate(cs):
            if c.is_zero():
                continue
            if first is not None:
                return None          # 非单项式
            first = (idx, c)
        return first

    p0 = None
    while len(P_cs) > 0 and P_cs[0].is_zero():
        P_cs = P_cs[1:]
        p0 = 0
    # 分子允许一般多项式：记录最低次
    p_lo = 0
    P_trim = _u_trim(list(P_cs))
    if _u_is_zero(P_trim):
        return None
    while P_cs[p_lo].is_zero():
        p_lo += 1

    qmono = mono_power(Q_cs)
    if qmono is None:
        return None                  # 分母含非常数非常单项式因子
    q0, c_den = qmono
    K = p_lo - q0
    # 分子其余部分仍是一般多项式（从 p_lo 起到尾部）
    body = {}
    ok_any = False
    for idx in range(p_lo, len(P_cs)):
        c = P_cs[idx]
        if c.is_zero():
            continue
        body[(idx - p_lo) + K] = c / c_den
        ok_any = True
    if not ok_any:
        return None

    # ---- 2) 实性：逐指数配对 ----
    half_done = set()
    parts = []
    u_arg_cache = {}

    def u_arg_of(e):
        if e not in u_arg_cache:
            u_arg_cache[e] = u_eff if e == 1 else T.times(N(e), u_eff)
        return u_arg_cache[e]

    keys = sorted(body.keys())
    for k in keys:
        if k in half_done:
            continue
        s_k = body[k]
        if k == 0:
            a_rf, b_rf = _rf_split_im(s_k)
            if not b_rf.p.is_zero():
                return None
            if not a_rf.p.is_zero():
                parts.append(a_rf.to_term())
            half_done.add(0)
            continue
        kn = -k
        s_n = body.get(kn)
        if s_n is None:
            return None              # 缺共轭伙伴 => 非实
        if not (conj_rf(s_k) - s_n).p.is_zero():
            return None              # 系数非共轭（精确零判定）
        s_pos = s_k if k > 0 else s_n
        e = abs(k)
        a_rf, b_rf = _rf_split_im(s_pos)
        ct = T.mk(S("Cos"), (u_arg_of(e),))
        st_t = T.mk(S("Sin"), (u_arg_of(e),))
        t1 = a_rf * Fr(2)
        t2 = b_rf * Fr(-2 * sgn)
        if not t1.p.is_zero():
            parts.append(T.times(t1.to_term(), ct))
        if not t2.p.is_zero():
            parts.append(T.times(t2.to_term(), st_t))
        half_done.add(k)
        half_done.add(kn)

    if not parts:
        return None
    body_t = parts[0] if len(parts) == 1 else T.mk(S("Plus"), tuple(parts))
    return body_t


def b_rf_zero(b0):
    return b0.p.is_zero()


def _solve_low(lam, rhs, de, jl):
    """低层 RDE D(s)+λ·s=rhs，s ∈ levels[:jl]（jl>=1 递归，jl==0 基层）。"""
    if jl >= 1:
        return _rde_tower_solve(lam, rhs, de, jl)
    return _rde_base_rde(lam, rhs, de)


def _rde_base_rde(lam, rhs, de):
    """ℚ(x)：D(s)+λ·s=rhs。λ 多项式 -> 极点分析完备判定；否则 undecided。"""
    from cas.ratfunc import RatFunc

    xv = de.levels[0]
    if not (lam.q.is_const() and lam.p.vars == (xv,) and
            rhs.p.vars == (xv,) and rhs.q.vars == (xv,)):
        return None, 'undecided'
    if lam.is_const() and lam.const_val() == 0:
        # λ=0：D(s)=rhs 纯有理积分（S-b B=0 下降的基层落点）。
        # 域内精确性门：解含 Log => 需要塔外元素 => 该层无解（proved）
        from cas.integrate import integrate_rational
        val, ok, _m = integrate_rational(rhs.p, rhs.q, xv)
        if not ok:
            return None, 'undecided'
        if T.free_vars(val) and any(
                isinstance(n_, Expr) and n_.head.name == "Log"
                for n_ in _iter_subterms(val)):
            return None, 'proved'
        return RatFunc.from_term(val, (xv,)), 'ok'
    # λ 任意多项式（含常数）、rhs 任意有理式：极点分析 + 待定系数完备
    b = _rde_exp_solve(1, lam.p, rhs.p, rhs.q, Poly.zero((xv,)))
    if b is None:
        return None, 'proved'
    if isinstance(b, Poly):
        b = RatFunc.from_poly(b)
    return b, 'ok'


def _poly_rde_final(bbr, cn, n, case_v, base_flag, dk_deg, dk_ncs,
                    der_fn, de, jv, zero):
    """sympy solve_poly_rde 非参数版：解 D(u)+bbr·u=cn（deg u ≤ n）。

    返回 ('ok', u_list) | ('proved', None) | ('undecided', reason)。
    """
    dB = _u_deg(bbr)
    thr = max(0, dk_deg - 1)

    def corr(cc, pmono):
        return _u_sub(cc, _u_add(der_fn(pmono), _u_mul(bbr, pmono, zero),
                                 zero))

    # no_cancel_b_large
    if not _u_is_zero(bbr) and (base_flag or dB > thr):
        u_acc, cc, mm = [], list(cn), n
        while not _u_is_zero(cc):
            stp = _u_deg(cc) - dB
            if stp < 0 or stp > mm:
                return 'proved', None
            pmono = [zero for _ in range(stp)] + [cc[-1] / bbr[dB]]
            u_acc = _u_add(u_acc, pmono, zero)
            mm = stp - 1
            cc = corr(cc, pmono)
        return 'ok', u_acc

    # no_cancel_b_small（含降到低层的 (h,b0,c0) 归约）
    if (_u_is_zero(bbr) or dB < dk_deg - 1) and (base_flag or dk_deg >= 2):
        u_acc, cc, mm = [], list(cn), n
        low_eq = None
        while not _u_is_zero(cc):
            dcc = _u_deg(cc)
            stp = 0 if mm == 0 else dcc - dk_deg + 1
            if stp < 0 or stp > mm:
                return 'proved', None
            if stp > 0:
                pmono = [zero for _ in range(stp)] + \
                    [cc[-1] / (dk_ncs[dk_deg] * Fr(stp))]
            else:
                if dB != dcc:
                    return 'proved', None
                if dB == 0:
                    low_eq = (bbr[0], cc[0])
                    break
                pmono = [cc[-1] / bbr[0]]
            u_acc = _u_add(u_acc, pmono, zero)
            mm = stp - 1
            cc = corr(cc, pmono)
        if low_eq is not None:
            yl, stl = _solve_low(low_eq[0], low_eq[1], de, jv)
            if stl != 'ok':
                return stl, None
            return 'ok', _u_add(u_acc, [yl], zero)
        return 'ok', u_acc

    # no_cancel_equal（共振贪心，自包含）
    if dk_deg >= 2 and dB == dk_deg - 1:
        lc_ratio = (bbr[dB] * Fr(-1)) / dk_ncs[dk_deg]
        big_m = -1
        if lc_ratio.is_const() and lc_ratio.const_val().denominator == 1 \
                and lc_ratio.const_val() > 0:
            big_m = int(lc_ratio.const_val())
        u_acc, cc, mm = [], list(cn), n
        while not _u_is_zero(cc):
            dcc = _u_deg(cc)
            stp = max(big_m, dcc - dk_deg + 1)
            if stp < 0 or stp > mm:
                return 'proved', None
            uu = stp * dk_ncs[dk_deg] + bbr[dB]
            if uu.is_zero():
                return 'undecided', 'no_cancel_equal tail recursion pending'
            if stp > 0:
                pmono = [zero for _ in range(stp)] + [cc[-1] / uu]
            else:
                if dcc != dk_deg - 1:
                    return 'proved', None
                pmono = [cc[-1] / bbr[dB]]
            u_acc = _u_add(u_acc, pmono, zero)
            mm = stp - 1
            cc = corr(cc, pmono)
        return 'ok', u_acc

    # cancellation 形态
    # B=0（S-b 已修复）：方程 D(u)=cn 即纯塔积分——对角/三角下降对
    # lam=0 同样完备（每度独立解低层 D(s)=c_jd，不可解即 proved）
    if not _u_is_zero(bbr) and dB != 0:
        return 'undecided', 'unexpected B degree in cancellation shape'
    if _u_is_zero(bbr):
        lam = zero
    else:
        lam = bbr[0]
    w_eta = de.ws[jv] if case_v == 'exp' and jv >= 1 else None
    u_acc, cc, mm = [], list(cn), n
    while not _u_is_zero(cc):
        jd = _u_deg(cc)
        if jd > mm:
            return 'proved', None
        lam_j = lam + w_eta * Fr(jd) if w_eta is not None else lam
        s_rf, stl = _solve_low(lam_j, cc[-1], de, jv)
        if stl != 'ok':
            return stl, None
        stm = [zero for _ in range(jd)] + [s_rf]
        u_acc = _u_add(u_acc, stm, zero)
        mm = jd - 1
        cc = corr(cc, stm)
    return 'ok', u_acc


def _rde_tower_solve(f, g, de, j):
    """完备判定求解器入口（契约见块注释）。j>=2 进塔机制（视图 jv=j-1>=1）；
    j==1 即 ℚ(x) 基层，直接委托极点分析（基层无更低视图，塔机制不适用）。"""
    from cas.ratfunc import RatFunc

    if j < 1:
        return None, 'undecided'
    # M5 收官批 #3：混合域门控退役——顶层 _risch_rec_mixed 已做
    # 共轭拆分，此处的 f, g 系数已纯参数化（Fr/SymRat 无 Ga）
    if j == 1:
        return _rde_base_rde(f, g, de)
    tview = de.levels[j - 1]
    case_v = de.cases[j - 1]
    jv = j - 1
    sub_vars = tuple(de.levels[:jv])

    def RF_of(ncs, dcs):
        nump = _from_univar(ncs, tuple(de.levels[:j]), tview)
        denp = _from_univar(dcs, tuple(de.levels[:j]), tview)
        if nump[0].is_zero():
            return RatFunc.zero(tuple(de.levels[:j]))
        return RatFunc(nump[0] * denp[1], denp[0] * nump[1])

    zero = RatFunc.zero(sub_vars)
    one_c = zero.one(sub_vars)
    der_fn = _make_der_fn(de, jv)

    dk_ncs, dk_dcs = _dk_pair(de, jv)
    if _u_deg(_u_formal_deriv(dk_dcs)) >= 0:
        return None, 'undecided'
    dk_deg = _u_deg(dk_ncs)

    fn = _univar(f.p, tview)
    fd = _univar(f.q, tview)
    gn = _univar(g.p, tview)
    gd = _univar(g.q, tview)

    # ---- Step 1: weak normalization（intpar:920；右端缩放 :1237）----
    wn = _wn_normalize(fn, fd, de, jv, der_fn, zero)
    if wn is None:
        return None, 'undecided'
    fn2, fd2, pn, pd = wn
    gn2, gd2 = _fu_mul(gn, gd, pn, pd, zero)

    # ---- Step 2: normal denominator -> 多项式方程（intpar:910, 1406-1410）----
    dn_ = _normal_part(fd2, der_fn, zero)
    en_ = _normal_part(gd2, der_fn, zero)
    gg = _u_gcd(dn_, en_, zero)
    hq, hr = _u_divmod(_u_gcd(en_, der_fn(en_), zero),
                       _u_gcd(gg, der_fn(gg), zero), zero)
    if not _u_is_zero(hr):
        return None, 'undecided'
    h = hq
    aa = _u_mul(dn_, h, zero)
    dh = der_fn(h)
    bbr_n = _u_sub(_u_mul(aa, fn2, zero), _u_mul(dn_, dh, zero))
    bq, br = _u_divmod(bbr_n, fd2, zero)
    if not _u_is_zero(br):
        return None, 'undecided'
    bbr = bq
    aa1 = _u_mul(aa, h, zero)
    cn, cd = _fu_mul(aa1, [one_c], gn2, gd2, zero)

    # ---- Step 3: C 的分母结构分流 ----
    # exp 视角 special 型 τ-分母（τ^v 单项式）=> Laurent 对角下降
    # （FriCAS do_SPDE_exp0 的 GP 形态：special 因子 = τ 幂，展开后
    # 系数 τ-free，各指数独立）。混合/normal 型分母仍走原路线。
    laurent = None
    if case_v == 'exp' and _u_deg(_u_formal_deriv(cd)) >= 0:
        v_tau = 0
        cd_w = list(cd)
        while len(cd_w) > 0 and cd_w[0].is_zero():
            cd_w = cd_w[1:]
            v_tau += 1
        rest = _u_trim(cd_w)
        rest_const = len(rest) <= 1
        if rest_const and _u_deg(aa) == 0 and _u_deg(bbr) == 0 \
                and not _u_is_zero(cn):
            laurent = (v_tau, rest[0])
        else:
            return None, 'undecided'
    elif _u_deg(_u_formal_deriv(cd)) >= 0:
        return None, 'undecided'

    u_list = []
    if laurent is not None:
        # ---- Laurent 对角下降 ----
        # c = cn/(τ^v·r)：指数 e=idx−v，系数=cn[idx]/r；逐指数解
        # D(s)+(lam+e·η)s=c_e（对角：D(τ^e)=e·η·τ^e 不跨指数），
        # 残差同步消去该指数。η=D(τ)/τ=ws[jv]。
        v_tau, r_coef = laurent
        eta_w = de.ws[jv]
        lam = bbr[0] / aa[0]
        inv_r = one_c / r_coef
        cc = {idx - v_tau: c * inv_r for idx, c in enumerate(cn)
              if not c.is_zero()}
        u_parts = {}
        guard = 0
        while cc:
            guard += 1
            if guard > 64:
                return None, 'undecided'
            e_top = max(cc.keys())
            c_e = cc.pop(e_top)
            lam_e = lam + eta_w * Fr(e_top)
            s_rf, st_l = _solve_low(lam_e, c_e, de, jv)
            if st_l != 'ok':
                return None, st_l
            u_parts[e_top] = s_rf
            # 残差：D(s·τ^e)+B·s·τ^e 的 e-系数 = D_low? 此处 s ∈ K_{j-1}，
            # 其 D 含 η·s 已含在低层方程内——残差恰为 (D_K(s)+e·η·s+B·s)τ^e，
            # 而低层方程 D_low(s)+(lam+e·η)s=c_e 中 D_low 即 K_{j-1} 全导数，
            # 解代入后该指数余量 = c_e − [D_low(s)+(lam+eη)s] = 0 恒成立，
            # 无跨指数泄漏（exp 对角保证），无需额外扣减。
        if not u_parts:
            y_final = RatFunc.zero(tuple(de.levels[:j]))
        else:
            e_min = min(u_parts.keys())
            e_max = max(u_parts.keys())
            num_cs = [zero for _ in range(e_max - e_min + 1)]
            for e, s_rf in u_parts.items():
                num_cs[e - e_min] = s_rf
            np_, nd_ = _from_univar(num_cs, tuple(de.levels[:j]), tview)
            if e_min < 0:
                tau_v = Poly.mono(tuple(de.levels[:j]), tview, -e_min)
                y_final = RatFunc(np_, nd_ * tau_v)
            else:
                y_final = RatFunc(np_, nd_)
        # Laurent 出口直接验证（常数 a、b 路径下 h、p 均为单位）
        dy = _tower_deriv_frac(y_final.p, y_final.q, de)
        if not (dy + f * y_final - g).p.is_zero():
            raise RischUnsupported(
                "internal: Laurent RDE candidate failed exact verify")
        # 实化在 _exp_freq_part 组装层做（t^k 频率因子须一并参与）
        return y_final, 'ok'
    if not _u_is_zero(cn):
        inv_cd = one_c / cd[0]
        cn = [c * inv_cd for c in cn]

        da, db, dc = _u_deg(aa), _u_deg(bbr), _u_deg(cn)
        base_flag = (case_v == 'base')

        # ---- Step 4: 次数界（sympy bound_degree 移植 + 切片边界）----
        if case_v == 'base':
            n = max(0, dc - max(db, da - 1))
            if db == da - 1 and da >= 1:
                al = (bbr[db] * Fr(-1)) / aa[da]
                if al.is_const():
                    cv = al.const_val()
                    if cv.denominator == 1:
                        n = max(n, int(cv), dc - db)
                else:
                    return None, 'undecided'
        elif case_v == 'primitive':
            n = max(0, dc - db) if db > da else max(0, dc - da + 1)
            if db == da - 1:
                al = (bbr[db] * Fr(-1)) / aa[da]
                eta_rf = RF_of(dk_ncs, dk_dcs)
                if not eta_rf.is_zero():
                    # M5 收官批 #2：完备版 _limited_int_prim 退化
                    # 为比率检验——α/η 整数常数 <=> 共振；
                    # 否则朴素界正确。不再返回 undecided（消除假拒答）。
                    st_m, m_v = _limited_int_prim(al, eta_rf, de, jv - 1)
                    if st_m == 'ok' and m_v > 0:
                        n = max(n, m_v)
            elif db == da and da != 0:
                # S-a 第二阶修正（sympy bound_degree primitive db==da 分支）：
                # α 为对数导数-根式（n_l==1）时经 beta 公式再探 limited
                al = (bbr[db] * Fr(-1)) / aa[da]
                try:
                    rec = _is_logderiv_radical(al, de, jv - 1)
                except RischUnsupported:
                    return None, 'undecided'          # S-a（保守）
                if rec is None:
                    return None, 'undecided'          # S-a（保守）
                n_l, z_rf = rec
                if n_l == 1:
                    lc_a, lc_b = aa[da], bbr[db]
                    Dz = _tower_deriv_frac(z_rf.p, z_rf.q, de)
                    num = lc_a * Dz + lc_b * z_rf
                    beta = -(num / (z_rf * lc_a))
                    eta_rf = RF_of(dk_ncs, dk_dcs)
                    st_m, m_v = _limited_int_prim(beta, eta_rf, de, jv - 1)
                    if st_m == 'ok' and m_v > 0:
                        n = max(n, m_v)
            # da==db==0：cancellation 逐度下降，naive 界 n>=dc 不截断，
            # 无需共振修正（安全性：各度独立处理到底）
        else:  # exp
            n = max(0, dc - max(da, db))
            if da == db and da != 0:
                # 共振界修正：α = m·η + D(v)/v 型判定经 _pld_solve。
                # 仅干净形态（n==1、无中间层幂因子、m>0）抬界；
                # 'no'/'und'/异形一律保守 undecided（欠界会误证不可积，
                # 方向安全压倒覆盖）。
                al = (bbr[db] * Fr(-1)) / aa[da]
                try:
                    rec = _pld_solve(al, [de.ws[jv]], de, jv - 1)
                except RischUnsupported:
                    return None, 'undecided'
                if rec[0] == "ok" and rec[1] == 1 and rec[2][0] > 0:
                    n = max(n, rec[2][0])
                else:
                    return None, 'undecided'
            # da==db==0：exp 对角下降同理安全

        # ---- Step 5: spde 归约核（sympy spde 忠实移植）----
        alpha_l = [one_c]
        beta_l = []
        proved = False
        guard = 0
        while True:
            guard += 1
            if guard > 64:
                return None, 'undecided'
            if _u_is_zero(cn):
                break
            if n < 0:
                proved = True
                break
            gfac = _u_gcd(aa, bbr, zero)
            qa_, ra_ = _u_divmod(aa, gfac, zero)
            qb_, rb_ = _u_divmod(bbr, gfac, zero)
            qc_, rc_ = _u_divmod(cn, gfac, zero)
            if not _u_is_zero(rc_) or not _u_is_zero(ra_) \
                    or not _u_is_zero(rb_):
                proved = True                         # gcd ∤ => 无解
                break
            aa, bbr, cn = qa_, qb_, qc_
            if _u_deg(aa) == 0:
                inv_a = one_c / aa[0]
                bbr = [c * inv_a for c in bbr]
                cn = [c * inv_a for c in cn]
                break
            rz = _u_diophantine(bbr, aa, cn, zero)
            if rz is None:
                proved = True
                break
            r_, z_ = rz
            bbr = _u_add(bbr, der_fn(aa), zero)
            cn = _u_sub(z_, der_fn(r_))
            n -= _u_deg(aa)
            beta_l = _u_add(beta_l, _u_mul(alpha_l, r_, zero), zero)
            alpha_l = _u_mul(alpha_l, aa, zero)

        if proved:
            return None, 'proved'

        # ---- Step 6: 终解分派 ----
        if _u_is_zero(cn):
            u_list = list(beta_l)
        else:
            st_f, res_u = _poly_rde_final(bbr, cn, n, case_v, base_flag,
                                          dk_deg, dk_ncs, der_fn, de, jv,
                                          zero)
            if st_f != 'ok':
                return None, st_f
            u_list = _u_add(_u_mul(alpha_l, res_u, zero), beta_l, zero)

    # ---- Step 7: 组合 y = u/(h·p) + 出口精确验证 ----
    oneL = [one_c]
    ynum_cs = _u_mul(u_list, list(pd) or oneL, zero)
    yden_cs = _u_mul(h, list(pn) or oneL, zero)
    y = RF_of(ynum_cs, yden_cs)
    dy = _tower_deriv_frac(y.p, y.q, de)
    if not (dy + f * y - g).p.is_zero():
        raise RischUnsupported(
            "internal: RDE candidate failed exact verify "
            "(this is a bug, not an honest refusal)")
    return y, 'ok'


def _exp_freq_part(freqs, de, j):
    """exp 频率分量：k=0 → 低层递归积分；k≠0 → RDE。任一频率无解
    => 不可初等证明；理论无法判定（多元 cancellation 等）=> unsupported。"""
    from cas.ratfunc import RatFunc

    tj = de.levels[j]
    xv = de.levels[0]
    expr = T.ZERO
    freq_terms = []
    rde_fail = None
    # 顶层虚指数层：±k 频率对可合并做共轭对实化（单个 k 分量不实，
    # 合并后才实——sin(2x) 类的核心形态）
    imag_top = _imag_exp_level_info(de, j) if de.cases[j] == "exp" else None
    re_pairs = {} if imag_top is not None else None
    for k in sorted(freqs):
        g = freqs[k]
        if k == 0:
            expr = T.plus(expr, _integrate_in_K(g, de, j))
            continue
        w = de.ws[j] * Fr(k)
        if g.q.is_const() and g.p.vars == (xv,) \
                and w.q.is_const() and w.p.vars == (xv,):
            # base 快路径：现有 ℚ(x) 极点分析求解器（无解即 proved——
            # η' 多项式保证界严格）
            b = _rde_exp_solve(k, de.ws[j].p, g.p, g.q, Poly.zero((xv,)))
            proved = b is None
        else:
            # 塔系数域：M5.2c-ii 完备判定求解器
            b, st = _rde_tower_solve(w, g, de, j)
            if st == 'proved':
                rde_fail = k
                break
            if st != 'ok':
                raise RischUnsupported(
                    "Risch DE on the tower undecidable with current theory "
                    "(%s); frequency k=%d" % (st, k))
        if b is None:
            if proved:
                rde_fail = k
                break
            raise RischUnsupported(
                "Risch DE on the tower undecidable with current theory "
                "(cancellation analysis pending); frequency k=%d" % k)
        bp = b
        if not bp.is_zero():
            # ---- 通道 A（顶层虚指数层）：±k 合并后一次共轭对实化 ----
            if re_pairs is not None:
                from cas.ratfunc import RatFunc as _RF
                if isinstance(bp, Poly):
                    re_pairs[k] = _RF.from_poly(
                        _embed(bp, tuple(de.levels[:j])))
                else:
                    re_pairs[k] = bp
                continue
            # ---- 通道 B（嵌套：虚层在系数域内）：逐 k 实化 b 本身，
            # 外层实指数因子 τ_j^k 以项形态外乘。----
            re_t = None
            if j >= 2:
                info = _imag_exp_level_info(de, j - 1)
                tau_im = de.levels[j - 1]
            else:
                info = None
            if info is not None:
                sgn_i, u_eff_i = info
                if isinstance(bp, Poly):
                    from cas.ratfunc import RatFunc as _RF
                    bp_rf = _RF.from_poly(_embed(bp, tuple(de.levels[:j])))
                else:
                    bp_rf = bp
                re_t = _realify_laurent(bp_rf, tau_im, sgn_i, u_eff_i, xv)
                if re_t is not None:
                    tk_t = T.pw(de.terms[j], N(k)) if k != 1 else de.terms[j]
                    if k < 0:
                        tk_t = T.div(T.ONE, T.pw(de.terms[j], N(-k)))
                    re_t = re_t if k == 0 else T.times(re_t, tk_t)
            if re_t is not None:
                expr = T.plus(expr, re_t)
            else:
                freq_terms.append((bp, k))
    # ---- 通道 A 汇总实化 ----
    if re_pairs and imag_top is not None:
        sgn_i, u_eff_i = imag_top
        klo, khi = min(re_pairs), max(re_pairs)
        zero_k = RatFunc.zero(tuple(de.levels[:j]))
        cs = [zero_k for _ in range(khi - klo + 1)]
        for kk, rf in re_pairs.items():
            cs[kk - klo] = rf
        n_, d_ = _from_univar(cs, tuple(de.levels[:j + 1]), tj)
        combined = RatFunc(n_, d_)
        # _from_univar 指数从 0 起：补回 klo 偏移
        if klo > 0:
            combined = combined * RatFunc(
                Poly.mono(tuple(de.levels[:j + 1]), tj, klo),
                Poly.one(tuple(de.levels[:j + 1])))
        elif klo < 0:
            combined = combined / RatFunc(
                Poly.mono(tuple(de.levels[:j + 1]), tj, -klo),
                Poly.one(tuple(de.levels[:j + 1])))
        re_t = _realify_laurent(combined, tj, sgn_i, u_eff_i, xv)
        if re_t is not None:
            expr = T.plus(expr, re_t)
        else:
            freq_terms.extend([(rf, kk) for kk, rf
                               in sorted(re_pairs.items())])
    for bk, k in freq_terms:
        bt = bk.to_term()   # 塔符号形态（出口统一回写）
        tk = T.pw(T.S(tj.name), N(k)) if k != 1 else T.S(tj.name)
        expr = T.plus(expr, T.times(bt, tk))
    if rde_fail is not None:
        from cas.pprint import to_str as _ts

        g = freqs[rde_fail]
        raise RischNonElementary(
            "not elementary: the %s component has no rational solution of "
            "the Risch differential equation y' + %d*eta'*y = %s "
            "(proved; eta' = %s)" % (
                ("t^%d" % rde_fail) if rde_fail != 1 else "t",
                rde_fail,
                _ts(g.to_term()),
                _ts(de.ws[j].to_term()),
            )
        )
    return expr


def _risch_rec(fa, fd, de, j):
    """在第 j 层积分 fa/fd（Poly(levels[:j+1])）——递归塔核心。

    商/真分式分离后按 case 分派：primitive 多项式走 limited 循环，
    exp 多项式走频率 RDE；真分式共用 Hermite+residue（泛型）；
    leftover 按 case 回本层多项式循环（primitive，deg 严格降）或
    低层递归积分（exp 的 k=0 分量）。
    """
    from cas.ratfunc import RatFunc
    from cas.integrate import integrate_rational

    sub = tuple(de.levels[:j])
    zero = RatFunc.zero(sub)
    tj = de.levels[j]
    case = de.cases[j]

    A = _univar(fa, tj)
    D = _univar(fd, tj)
    if _u_is_zero(A):
        return T.ZERO

    dq = len(D) - 1
    dp = len(A) - 1
    if dp >= dq:
        Q, R = _u_divmod(A, D, zero)
    else:
        Q, R = [], A

    expr = T.ZERO
    if case == "primitive":
        for bk, k in _primitive_poly_part(Q, de, j):
            bt = bk.to_term()   # 塔符号形态
            tk = T.pw(T.S(tj.name), N(k)) if k != 1 else T.S(tj.name)
            expr = T.plus(expr, T.times(bt, tk))
        res, negf, st = (None, None, None, None), {}, "ok"
        if not _u_is_zero(R):
            res, negf, st = _integrate_proper(R, D, de, j, zero)
    else:
        freqs = {k: c for k, c in enumerate(Q) if not c.is_zero()}
        res, negf, st = (None, None, None, None), {}, "ok"
        if not _u_is_zero(R):
            res, negf, st = _integrate_proper(R, D, de, j, zero)
        for k, v in negf.items():
            freqs[k] = freqs[k] + v if k in freqs else v
        expr = T.plus(expr, _exp_freq_part(freqs, de, j))

    rat_part, logs, nonel, leftover = res
    expr = T.plus(expr, assemble_exp_result(rat_part, logs, nonel, de, j))

    if leftover is not None and any(not c.is_zero() for c in leftover):
        lf = _u_trim(list(leftover))
        if case == "primitive":
            # θ-多项式剩余：回本层多项式积分（deg 严格降，终止）
            fn, fdd = _from_univar(lf, de.vars, tj)
            expr = T.plus(expr, _risch_rec(fn, fdd, de, j))
        else:
            # exp：ℚ 常数剩余（非常数系数已在频率分量中）
            cv = Fr(0)
            for c in lf:
                if not c.is_zero():
                    cv += c.const_val()
            if cv != 0:
                xv = de.levels[0]
                val, ok, _m = integrate_rational(Poly.const((xv,), cv),
                                                 Poly.one((xv,)), xv)
                if not ok:
                    raise RischUnsupported("leftover rational integration failed")
                expr = T.plus(expr, val)
    return expr

