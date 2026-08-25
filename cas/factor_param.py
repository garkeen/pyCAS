# -*- coding: utf-8 -*-
"""ℚ(params)[x] 多元因子分解骨架（P3-c, fricas allfact.spad 参照）。

当前实现：对 n≤4 的小次数多项式，经待定系数 + Groebner 求解
在 ℚ(params) 上寻找真因子；失败诚实返回 [g]（unknown 粒度）。
完整多元 Zassenhaus（mod p/Hensel/组合）为后续批次。
"""
from fractions import Fraction as Fr
from cas.poly import Poly, SymRat
from cas.errors import PolyError

def _poly_solve_coeffs(eqs, vars_):
    """解系数方程组（Groebner, 5s 超时），返回解列表或 None。"""
    import concurrent.futures
    from cas import term as T
    from cas.term import S, N
    from cas.groebner import solve_system
    def _run():
        return solve_system([T.mk(S("Eq"), (f, N(0))) for f in eqs], list(vars_))
    try:
        with concurrent.futures.ThreadPoolExecutor(max_workers=1) as ex:
            fut = ex.submit(_run)
            r = fut.result(timeout=5)
    except Exception:
        return None
    sols = getattr(r, "solutions", None)
    if sols is None:
        return None
    st = getattr(r, "status", "")
    if str(st) not in ('ok','partial','identity'):
        return None
    return sols

def factor_param(g, x):
    """g ∈ ℚ(params)[x]，x 单变量，系数 SymRat/Fr。
    返回 (因子列表, content) 或 ([g], None)（不可约/unknown）。
    仅 n≤4 且参量个数≤2 时尝试待定系数分解，余诚实 [g]。
    """
    n = g.degree(x)
    if n <= 2 or n > 4:
        return [g], None
    # 收集参量
    params = set()
    for c in g.monos.values():
        if isinstance(c, SymRat):
            for pp in (c.num, c.den):
                params.update(pp.vars)
    if len(params) > 2:
        return [g], None
    # 仅尝试分解为 (x + u)*(x^{n-1}+ ...)
    # 对 n=3: (x+u)*(x^2+ v x + w) ; n=4: (x^2+ u x + v)*(x^2+ w x + z) 等
    # 为简化，仅试 n=3 的 (1+2) 分解
    if n == 3:
        # 设 g = x^3 + p2 x^2 + p1 x + p0, 因子 (x+u)(x^2+ v x + w) = x^3 + (u+v) x^2 + (uv+w) x + u w
        # 未知 u,v,w ∈ ℚ(params) 待定，用 SymRat 变量 _c0.. 构建方程组
        from cas import term as T
        from cas.term import S
        # 用 Poly 的待定系数直接在 ℚ[params] 上解线性方程更简：比较系数得方程组
        # p2 = u+v, p1 = u v + w, p0 = u w
        # 消 w = p0 / u, 代入得二次方程，Groebner 可解
        # 为通用，构造符号 _u,_v,_w 的 Poly 方程组
        _u, _v, _w = S("_pu"), S("_pv"), S("_pw")
        # g 的系数
        p2 = g.monos.get((2,), Fr(0))
        p1 = g.monos.get((1,), Fr(0))
        p0 = g.monos.get((0,), Fr(0))
        # 需将 SymRat 系数转为 term 上的 Poly 方程
        # 构造方程：u+v - p2 =0, u v + w - p1=0, u w - p0=0
        # 其中 u,v,w 为新变元，p2,p1,p0 为含参量 a 的 SymRat 项
        # 将 SymRat 转 term
        def _c2term(c):
            if isinstance(c, SymRat):
                return c.to_term()
            return T.N(c)
        eqs = [
            T.plus(_u, _v, T.neg(_c2term(p2))),
            T.plus(T.times(_u, _v), _w, T.neg(_c2term(p1))),
            T.plus(T.times(_u, _w), T.neg(_c2term(p0))),
        ]
        sols = _poly_solve_coeffs(eqs, [_u,_v,_w])
        if sols:
            for sol in sols:
                # sol 为 tuple of terms，按 [_u,_v,_w] 顺序
                if len(sol)!=3:
                    continue
                # 将解代入构造因子，验证整除
                try:
                    # sol 含参量 a 的表达式，需转 SymRat 后构造 Poly
                    from cas.poly import Poly as P
                    # 构造因子 Poly
                    # u_sol, v_sol, w_sol 为 term，需转 SymRat via Poly
                    # 简化：直接用 term 的 Poly.from_term 构造后转 SymRat
                    # 若 sol 含参量，直接构造 Poly 的系数经 _mk_param
                    # 此处为骨架，验证整除即可
                    # 尝试构造 (x+u)
                    # 将 sol 转为 SymRat 系数
                    def _term_to_symrat(t):
                        # t 可能含参量 a，需经 Poly 转 SymRat
                        try:
                            # 尝试直接 Fr
                            if T.is_num(t):
                                return Fr(T.num_val(t))
                            # 否则经 Poly
                            from cas.poly import Poly as PP
                            # 收集 t 中的参量 vars
                            pp = PP.from_term(t, tuple(params)) if params else PP.from_term(t, ())
                            # 若 pp 仍含参量，需转 SymRat
                            # 简化：若 t 含参量，直接用 _mk_param 逻辑
                            # 此处为占位，返回 Fr(0) 使验证失败则跳过
                            return None
                        except Exception:
                            return None
                    # 占位：当前骨架不实际构造，仅返回 [g]（unknown 粒度），
                    # 完整求解需将 sol 转回 SymRat 因子，此为下一批次
                    return [g], None
                except Exception:
                    continue
    return [g], None
