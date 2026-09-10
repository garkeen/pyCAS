# -*- coding: utf-8 -*-
"""战术层：求解/化简的具体招法（与验证器完全独立）。

架构总纲：验证器不重跑求解算法。战术层交出"证书"（解、标准形），
工作流验证器只按推导类型做独立判定（回代判官、域判等）。
战术失败抛 TacticsError——诚实拒答，不降级猜测。
"""

from fractions import Fraction as Fr

from cas.syntax import term as T
from cas.syntax.term import Sym
from cas.errors import TacticsError
from cas.math.project import project, zero_of, is_zero
from cas.math.domains.poly import Poly
from cas.math.domains.ratfunc import RatFunc, rf_reduce


def _lin_core(diff, var: Sym):
    """方程差值的线性分类：在投影标准形上裁决——语义判据，非形状判据。

    谁含 var 不是看原始项的形状（x+1 与 x 的差值形状上含 x、语义上是
    常数），而是看投影后的域元素。返回：
    ("zero", None)     差值恒为零（零多项式/零有理式/ℚ 零）——恒等式
    ("nonzero", None)  差值与 var 无关且可证非零——永不成零
    ("linear", 项)     关于 var 恰一次——唯一候选解（证书项）
    ("refuse", 理由)   其余：非线性/含其他变元/域外——完备性无法保证
    """
    hit = project(diff)
    if hit is None:
        return ("refuse", "差值不在 ℚ/多项式/有理函数域内")
    if hit.element is None:
        # ℚ 常数格：恒等或矛盾，与 var 无关
        return ("zero", None) if is_zero(hit) else ("nonzero", None)
    ring = hit.domain.ring
    el = hit.element
    if isinstance(el, RatFunc):
        red = rf_reduce(ring, el)
        if red.num.is_zero():
            return ("zero", None)            # num ≡ 0 ⟺ 分式 ≡ 0（den≠0 归守卫）
        el = red.num
    if not isinstance(el, Poly):
        return ("refuse", "投影元素非多项式")
    if el.is_zero():
        return ("zero", None)
    if any(v is not var for v in el.vars):
        return ("refuse", "含其他变元：当前仅支持单变量线性")
    if var not in el.vars:
        return ("nonzero", None)             # 与 var 无关的非零常数多项式
    i = el.vars.index(var)
    coefs = {k[i]: c for k, c in el.monos}
    deg = max(coefs)
    if deg == 0:
        return ("nonzero", None)             # var 次数为 0：非零常数
    if deg != 1:
        return ("refuse", f"{deg} 次方程，当前战术仅支持线性")
    a = coefs[1]
    b = coefs.get(0, ring.from_int(0))
    return ("linear", T.N(-b / a))


def solve_linear(content, var: Sym):
    """线性求解战术：等式 -> 解项（证书）。

    差值经 `_lin_core` 在投影标准形上分类——恰一次方程给出 -b/a 证书；
    恒等（解集全域）/矛盾（无解）/非线性按语义拒答。验证由工作流
    回代判官独立完成，本函数不重复。"""
    if not (isinstance(content, T.Expr) and content.head.name == "Eq"):
        raise TacticsError("solve 需要等式")
    lhs, rhs = content.args
    kind, payload = _lin_core(T.plus(lhs, T.neg(rhs)), var)
    if kind == "linear":
        return payload
    if kind == "zero":
        raise TacticsError("恒等式：解集为全域，无唯一解")
    if kind == "nonzero":
        raise TacticsError("矛盾等式：与该变元无关且永不成零，无解")
    raise TacticsError(payload)


# ---------------------------------------------------------------------------
# 丢番图碎片（ℤ 是可判定碎片的宿主；一般情形是定理级拒答，架构 7.3）
# ---------------------------------------------------------------------------

def solve_diophantine_linear(a: int, b: int, c: int):
    """ax + by = c 的整数解（扩展欧几里得）。

    返回 ((x0, y0), (dx, dy))：特解与周期——全部解为
    (x0 + dx·t, y0 + dy·t), t ∈ ℤ。gcd(a,b) ∤ c 时无解，抛拒答。
    """
    from cas.math.domains.z import Z_RING
    g, s, t = Z_RING.xgcd(a, b)
    if g == 0:
        if c != 0:
            raise TacticsError("0 = c ≠ 0：无解")
        return ((0, 0), (1, 0))            # 0 = 0：全平面，给平凡参数化
    if c % g != 0:
        raise TacticsError(f"无整数解：gcd({a},{b})={g} 不整除 {c}")
    m = c // g
    return ((s * m, t * m), (b // g, -a // g))


def integer_roots(p, var):
    """整系数单变量多项式的全部整数根（有理根定理）。

    整数根必整除常数项——完备有限候选集，逐个 Horner 精确验证。
    返回升序列表。系数含非整数抛拒答（片段外）。
    """
    if var not in p.vars:
        return []
    i = p.vars.index(var)
    others = [j for j in range(len(p.vars)) if j != i]
    coefs = {}
    for k, c in p.monos:
        if any(k[j] for j in others):
            raise TacticsError("含其他变元：当前仅支持单变量")
        if getattr(c, "denominator", 1) != 1:
            raise TacticsError("系数非整数：整数根定理片段外")
        coefs[k[i]] = int(c)
    if not coefs:
        return []
    roots = []
    while coefs.get(0, 0) == 0:            # x | p：0 是根，逐个降阶
        roots.append(0)
        coefs = {e - 1: c for e, c in coefs.items() if e > 0}
        if not coefs:
            return roots
    deg = max(coefs)
    a0 = coefs[0]
    from cas.math.realroot import divisors
    cands = set()
    for d in divisors(a0):                 # 整数根 ⟹ d | a₀，O(√|a₀|) 枚举
        cands.update((d, -d))
    for r in sorted(cands):
        acc = coefs[deg]
        for e in range(deg - 1, -1, -1):   # Horner
            acc = acc * r + coefs.get(e, 0)
        if acc == 0:
            roots.append(r)
    return sorted(set(roots))


def solve_piecewise(f, x: Sym, target):
    """解分段方程 pw(...)=target：逐支求解 + 分支条件成员判定。

    每支取支方程差值 d = v − target（折叠）后两步分类：
    · d 不含自由变元 x（闭式）：判零通道裁决——恒零 → 整支区域为解，
      可证非零 → 无贡献，判不动 → 记条件解；
    · d 含 x：交 `_lin_core` 在投影标准形上分类（x+1≡x+1 的差值形状
      含 x、投影后恒零，照样给区域解；x+1 与 x 的差值投影后是常数，
      照样无贡献）——线性得候选，代入分支条件经判定管线裁决（成立收、
      不成立弃、未决记条件）。
    任一支超出线性片段即拒——漏掉它可能丢解，完备性无法保证，诚实拒答。

    返回 {"points": [点解], "regions": [区域条件], "conditional": [(解,条件)]}。"""
    from cas.math.piecewise import fold_nested, branches, is_piecewise
    from cas.math.decide import decide
    from cas.kernel.context import Context
    from cas.kernel.verdict import YES, NO
    from cas.math.qarith import fold
    if not is_piecewise(f):
        raise TacticsError("solve_piecewise 需分段函数")
    f = fold_nested(f)
    points, regions, conditional = [], [], []
    for v, c in branches(f):
        d = fold(T.plus(v, T.neg(target)))
        if x not in T.free_vars(d):
            z = zero_of(d)
            if z is True:
                regions.append(c)                 # 支方程恒成立 → 整支区域为解
            elif z is None:
                conditional.append((None, c))     # 是否恒等未决
            continue
        kind, payload = _lin_core(d, x)
        if kind == "zero":
            regions.append(c)                     # 投影后恒零（如 v ≡ target）
            continue
        if kind == "nonzero":
            continue                              # 支方程永不成零，无贡献
        if kind == "refuse":
            raise TacticsError(f"分支方程超出线性片段，完备性无法保证：{payload}")
        verdict = decide(fold(T.subst(c, {x: payload})), Context())
        if verdict is YES:
            points.append(payload)
        elif verdict is NO:
            continue
        else:
            conditional.append((payload, c))
    return {"points": points, "regions": regions, "conditional": conditional}
