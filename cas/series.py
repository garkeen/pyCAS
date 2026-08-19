"""Taylor 级数引擎（M3，纯符号，截断幂级数表示）。

表示：(k0, [c0, c1, ..., cn]) = Σ c_i·u^(k0+i)，系数为 Fraction，u = x−a。
定位：limits 的首阶分析、defint 的端点行为、未来的渐近展开。
已知系数表（sin/cos/exp/log 等）为声明式知识；未知解析函数走
"d 逐次求导取系数"兜底（导数表来自 FunctionSpec，不另硬编码）。
"""

from fractions import Fraction as Fr

from cas import term as T
from cas.term import Expr, Int, Rat, Sym, Const


class SeriesError(Exception):
    pass


def series(t, x, a, n=8):
    """t 在 x=a 的 Taylor 展开（截断到 n 阶）-> (k0, coeffs)。

    a 为精确数值（Int/Rat 项或裸 Fraction）；无法展开（如 e^(1/x) 在 0 的孤立奇点）抛 SeriesError。
    """
    if T.is_num(a):
        a = T.num_val(a)
    if not isinstance(a, Fr):
        raise SeriesError("expansion point must be numeric")
    u = Sym("_series_u")
    sh = T.subst(t, {x: T.plus(u, T.N(a))})
    return _series0(sh, u, n)


def _series0(t, u, n):
    """在 u=0 展开（内部核心，t 已平移）。"""
    if T.is_num(t):
        return (0, [T.num_val(t)] + [Fr(0)] * n)
    if isinstance(t, Const):
        raise SeriesError(f"constant {t.name} not expandable")
    if isinstance(t, Sym):
        if t is u:
            return (1, [Fr(1)] + [Fr(0)] * n)
        raise SeriesError(f"foreign symbol {t.name} in series")
    if not isinstance(t, Expr):
        raise SeriesError("not expandable")
    name = t.head.name
    if name == "Plus":
        return _s_add([_series0(a, u, n) for a in t.args])
    if name == "Times":
        acc = (0, [Fr(1)] + [Fr(0)] * n)
        for a in t.args:
            acc = _s_mul(acc, _series0(a, u, n), n)
        return acc
    if name == "Power":
        b, e = t.args
        bs = _series0(b, u, n)
        if isinstance(e, Int):
            if e.v >= 0:
                acc = (0, [Fr(1)] + [Fr(0)] * n)
                for _ in range(e.v):
                    acc = _s_mul(acc, bs, n)
                return acc
            # 负幂：极点因子 u^{k·|e|} 提出，正则部分取逆；
            # (v·u^k)^e = v^e · u^{k·e} · (reg)^e，v^e 符号因子不可丢
            k, v = _lead(bs)
            if v is None:
                raise SeriesError("zero base to negative power")
            k0, cs = bs
            reg = _trim(0, [c / v for c in cs[k - k0:]])
            inv = _s_div_reg((0, [Fr(1)]), reg, n)
            return _trim(-k * (-e.v), _s_scale(inv, v ** e.v, n)[1])
        if isinstance(e, Rat) and bs[0] == 0 and bs[1][0] != 0:
            # (c·u^k + ...)^r 首阶已知，但分数幂级数展开未建——诚实拒答
            raise SeriesError("fractional power series not implemented")
        raise SeriesError("power not expandable")
    if name in ("Sin", "Cos", "Exp", "Sinh", "Cosh", "Log", "Atan") and len(t.args) == 1:
        try:
            return _known(name, t.args[0], u, n)
        except SeriesError:
            # 表路径拒答（一般形复合等）时逐次求导兑底；本性奇点仍会拒答
            return _via_diff(t, u, n)
    return _via_diff(t, u, n)


def _known(name, arg, u, n):
    """已知函数系数表：arg = a + r(u) 时 r 必须是单项式 c·u^j（纯符号通道不引入
    sin(a)/e^a 等不可精确表示的常数），否则回退逐次求导。"""
    a, rs = _split_const(arg, u, n)
    if name == "Exp":
        base = _s_table_exp(n)
        return _compose(base, rs, u, n) if rs is not None else base
    if name in ("Sin", "Cos", "Sinh", "Cosh"):
        base = _s_table_trig(name, n)
        return _compose(base, rs, u, n) if rs is not None else base
    if name == "Log":
        if a == 0:
            raise SeriesError("log(0) singular")
        # log(a + r) = log(a) + log(1 + r/a)
        inner = _s_scale(rs, Fr(1) / a, n)
        if inner[0] != 1:
            raise SeriesError("log composition leading order != 1")
        return _s_add([(0, [_log_exact(a)] + [Fr(0)] * n), _s_compose_log(inner, n)])
    if name == "Atan":
        if a != 0:
            raise SeriesError("atan away from 0 not implemented")
        return _compose(_s_table_atan0(n), rs, u, n) if rs is not None else _s_table_atan0(n)
    raise SeriesError(f"no series table for {name}")


def _compose(table, rs, u, n):
    """已知系数表 ∘ rs：rs = c·u^j 单项式时代入（系数 c^i 缩放，精确有理）；
    极点复合（本性奇点，如 e^(1/x)）与一般形诚实拒答。"""
    if rs is None:
        return table
    k, v = _lead(rs)
    if v is None:
        return table   # arg 为常数，表在 0 取值
    if k < 0:
        raise SeriesError("pole in composition (essential singularity)")
    k0r, cs = rs
    if any(cc != 0 for cc in cs[k - k0r + 1:]):
        raise SeriesError("general composition not implemented")
    k0, tc = table
    out = [Fr(0)] * (n + 1)
    for i, c in enumerate(tc):
        e = k0 + i
        if e < 0:
            if c != 0:
                raise SeriesError("negative order in composition")
            continue
        if c == 0:
            continue
        pos = e * k
        if pos <= n:
            out[pos] += c * (v ** e)
    return _trim(0, out)


def _split_const(arg, u, n):
    """arg -> (常数部分 a: Fr, 余项级数 rs)；无余项时 rs=None。"""
    c = T.ZERO
    rest = []
    if isinstance(arg, Expr) and arg.head.name == "Plus":
        for a_ in arg.args:
            if T.is_num(a_):
                c = T.plus(c, a_)
            else:
                rest.append(a_)
        r = T.plus(*rest) if rest else T.ZERO
    else:
        r = arg
    aval = T.num_val(c) if T.is_num(c) else Fr(0)
    if r is T.ZERO:
        return aval, None
    rs = _series0(r, u, n)
    if rs[0] == 0 and rs[1][0] != 0:
        raise SeriesError("composition needs vanishing inner part")
    return aval, rs


def _s_compose_log(inner, n):
    """log(1 + v)（v 的级数，v(0)=0）：Σ (−1)^{k+1} v^k / k。"""
    acc = (0, [Fr(0)] * (n + 1))
    vk = (0, [Fr(1)] + [Fr(0)] * n)
    for k in range(1, n + 1):
        vk = _s_mul(vk, inner, n)
        sign = Fr(1) if k % 2 else Fr(-1)
        acc = _s_add([acc, _s_scale(vk, sign / k, n)])
    return acc


def _log_exact(a):
    """纯符号通道只认 log(1)=0；其余精确值不可表示 -> 诚实拒答。"""
    if a == 1:
        return Fr(0)
    raise SeriesError(f"log({a}) not exactly known")


def _s_table_exp(n):
    c, f = [], Fr(1)
    for k in range(n + 1):
        if k:
            f *= k
        c.append(Fr(1) / f)
    return (0, c)


def _s_table_log1p(n):
    return (1, [Fr(1) if k % 2 else Fr(-1) for k in range(1, n + 2)])


def _s_table_atan0(n):
    c = []
    for k in range(n + 1):
        j = 2 * k + 1
        c.append((Fr(1) if k % 2 == 0 else Fr(-1)) / j)
    return (1, c)


def _s_table_trig(name, n):
    """sin/cos/sinh/cosh 的截断级数（按奇偶项）。"""
    c = []
    for m in range(n + 1):
        if name in ("Sin", "Sinh") and m % 2 == 0:
            c.append(Fr(0))
            continue
        if name in ("Cos", "Cosh") and m % 2 == 1:
            c.append(Fr(0))
            continue
        f = Fr(1)
        for k in range(1, m + 1):
            f *= k
        neg = (m // 2) % 2 == 1 and name in ("Sin", "Cos")
        c.append(Fr(-1) / f if neg else Fr(1) / f)
    return (0, c)


def _s_add(lst):
    k0 = min(s[0] for s in lst)
    ln = max(s[0] + len(s[1]) for s in lst) - k0
    out = [Fr(0)] * ln
    for k, cs in lst:
        for i, v in enumerate(cs):
            out[k - k0 + i] += v
    return _trim(k0, out)


def _s_mul(a, b, n):
    ka, ca = a
    kb, cb = b
    out = [Fr(0)] * (n + 1)
    for i, x in enumerate(ca):
        if x == 0:
            continue
        for j, y in enumerate(cb):
            if i + j > n or y == 0:
                continue
            out[i + j] += x * y
    return _trim(ka + kb, out)


def _s_div_reg(num, den, n):
    """num/den：要求 den 首系数非零（正则分母；极点因子由调用方提出）。

    商阶 = 分子阶 − 分母阶；系数递推，截断到 n 项。
    """
    kn, cn = num
    kd, cd = den
    j0, b0 = _lead(den)
    if b0 is None:
        raise SeriesError("division by zero series")
    db = cd[j0:]
    q = [Fr(0)] * (n + 1)
    for m in range(n + 1):
        acc = cn[m] if m < len(cn) else Fr(0)
        for i in range(1, m + 1):
            if i < len(db):
                acc -= q[m - i] * db[i]
        q[m] = acc / b0
    return _trim(kn - (kd + j0), q)


def _s_scale(s, c, n):
    k0, cs = s
    return _trim(k0, [v * c for v in cs[: n + 1]])


def _trim(k0, cs):
    while len(cs) > 1 and cs[-1] == 0:
        cs.pop()
    if all(v == 0 for v in cs):
        return (0, [Fr(0)])
    return (k0, cs)


def _lead(s):
    """首非零项 (阶, 系数)；零级数 -> (None, None)。"""
    k0, cs = s
    for i, v in enumerate(cs):
        if v != 0:
            return k0 + i, v
    return None, None


def leading_term(t, x, a, n=10):
    """t 在 x->a 的首阶行为 -> (阶 k, 首系数 c, 尾部级数)，无法分析抛 SeriesError。

    尾部 = t/(c·u^k) − 1 在 u=0 的展开，供首系数符号判定（limits 消费）；
    截断耗尽时尾部为空（符号不可判 -> limits 回退其它通道）。
    """
    u = Sym("_series_u")
    sh = T.subst(t, {x: T.plus(u, T.N(a))})
    s = _series0(sh, u, n)
    k, c = _lead(s)
    if k is None:
        return (0, Fr(0), (0, [Fr(0)]))
    k0, cs = s
    if k == k0:
        norm = (0, [v / c for v in cs])
    elif k > k0:
        # 尾部切片：阶差为正时直接平移（无需除法）
        norm = (0, [Fr(0)] * (k - k0) + [v / c for v in cs])
    else:
        # 极点：t/u^k = (t 的系数左移 |k|)；超出截断部分为未知 -> 尾部为空
        shift = -k
        norm = (0, [v / c for v in cs[shift:]]) if shift < len(cs) else (0, [Fr(1)])
    tail = _trim(0, [Fr(0)] + norm[1][1:])    # 减 1 后去掉常数项
    return (k, c, tail)


def _via_diff(t, u, n):
    """兜底：d 逐次求导取 Taylor 系数（导数表来自 FunctionSpec）。"""
    from cas.diff import d
    from cas.simplify import simplify

    coeffs = []
    cur = t
    fact = Fr(1)
    for k in range(n + 1):
        v = simplify(T.subst(cur, {u: T.ZERO}))
        if not T.is_num(v):
            raise SeriesError(f"coefficient {k} not numeric at 0")
        coeffs.append(T.num_val(v) / fact)
        cur = simplify(d(cur, u))
        fact *= k + 1
    return _trim(0, coeffs)
