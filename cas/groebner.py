"""Gröbner 基：单项式序 + 多变元除法 + Buchberger + 消元求解（Cox-Little-O'Shea 标准路线）。

分层纪律：本模块是内核算法（过程不是改写规则），正确性由结构定理背书——
归零验证（解代回 ideal 成员检验）与消元性质（lex 下 G ∩ k[vars[k:]] 生成
消元理想）是数学定理，不需要逐步证书。朴素 Buchberger 够支撑低次方程组；
F4/F5 级效率不在承诺范围（规模超限诚实报 unsupported）。
"""

from fractions import Fraction as Fr

from cas import term as T
from cas.poly import Poly
from cas.errors import BudgetExceeded, PolyError


# ---------------------------------------------------------------------------
# 单项式序（良序，保证除法终止）
# ---------------------------------------------------------------------------

def lex_key(e):
    """字典序：vars[0] 最优先（消元序）。"""
    return e


def grevlex_key(e):
    """分级反字典序：总次数优先；同次时最右不同位置指数小者大（计算默认）。"""
    return (sum(e), tuple(-i for i in reversed(e)))


ORDERS = {"lex": lex_key, "grevlex": grevlex_key}


def _lm(p, key):
    """leading monomial 指数元组。"""
    return max(p.monos, key=key)


def _divides(a, b):
    """单项式指数元组 a 是否整除 b。"""
    return all(x >= y for x, y in zip(a, b))


def _mono_poly(vars_, e, c):
    return Poly(vars_, {tuple(e): c})


# ---------------------------------------------------------------------------
# 多变元除法（完全归约：所有可被 G 的首单项式整除的项都消去）
# ---------------------------------------------------------------------------

def _reduce(f, G, key):
    r = Poly.zero(f.vars)
    h = f
    while not h.is_zero():
        lm = _lm(h, key)
        for g in G:
            if g.is_zero():
                continue
            lg = _lm(g, key)
            if _divides(lm, lg):
                qe = tuple(a - b for a, b in zip(lm, lg))
                m = _mono_poly(h.vars, qe, h.monos[lm] / g.monos[lg])
                h = h - m * g
                break
        else:
            mv = h.monos[lm]
            r = r + _mono_poly(h.vars, lm, mv)
            h = h - _mono_poly(h.vars, lm, mv)
    return r


def _spoly(f, g, key):
    """S-多项式：lcm(lt_f, lt_g) 的交叉消去组合。"""
    lf, lg = _lm(f, key), _lm(g, key)
    l = tuple(max(a, b) for a, b in zip(lf, lg))
    mf = _mono_poly(f.vars, tuple(a - b for a, b in zip(l, lf)), Fr(1) / f.monos[lf])
    mg = _mono_poly(g.vars, tuple(a - b for a, b in zip(l, lg)), Fr(1) / g.monos[lg])
    return mf * f - mg * g


def _monic(p):
    if p.is_zero():
        return p
    return p.scalar(Fr(1) / p.monos[_lm(p, lex_key)])


# ---------------------------------------------------------------------------
# Buchberger（朴素版 + 第一判则剪枝）
# ---------------------------------------------------------------------------

_MAX_PAIRS = 20000
_MAX_BASIS = 200


def groebner(fs, order="grevlex"):
    """理想 <fs> 的 Groebner 基（list[Poly]，同 vars；零多项式剔除）。

    order: "grevlex"（计算默认）/ "lex"（消元）。互素首单项式对跳过
    （Buchberger 第一判则）；规模护栏超限抛 PolyError（诚实拒绝）。
    """
    key = ORDERS[order]
    G = []
    for f in fs:
        if f.is_zero():
            continue
        r = _reduce(f, G, key)
        if not r.is_zero():
            G.append(_monic(r))
    pairs = [(i, j) for i in range(len(G)) for j in range(i + 1, len(G))]
    while pairs:
        if len(pairs) > _MAX_PAIRS or len(G) > _MAX_BASIS:
            raise BudgetExceeded("groebner: computation budget exceeded")
        i, j = pairs.pop(0)
        li, lj = _lm(G[i], key), _lm(G[j], key)
        # 第一判则：首单项式互素 -> S-poly 必归零
        if all(max(a, b) == a + b for a, b in zip(li, lj)):
            continue
        r = _reduce(_spoly(G[i], G[j], key), G, key)
        if not r.is_zero():
            G.append(_monic(r))
            for k in range(len(G) - 1):
                pairs.append((k, len(G) - 1))
    return G


def reduced_basis(G, order="grevlex"):
    """reduced Groebner 基：成员互相完全归约 + monic（固定序下唯一）。

    成员被其余成员完全消去时直接删除（g ∈ <G\\{g}> ⟺ 理想不变）。
    """
    key = ORDERS[order]
    H = [_monic(g) for g in G if not g.is_zero()]
    rounds = 0
    changed = True
    while changed and H:
        changed = False
        rounds += 1
        if rounds > 50:
            raise BudgetExceeded("groebner: autoreduce budget exceeded")
        newH = []
        for h in H:
            rest = [u for u in H if u is not h]
            r = _reduce(h, rest, key)
            if r.is_zero():
                changed = True
                continue
            nr = _monic(r)
            if nr.monos != h.monos:
                changed = True
            newH.append(nr)
        H = newH
    return H


# ---------------------------------------------------------------------------
# 消元求解（零维优先；正维/非有理解分支诚实报告）
# ---------------------------------------------------------------------------

_MAX_BRANCH = 256


class SolveSysResult:
    def __init__(self, solutions, status, note=""):
        self.solutions = solutions   # list[tuple(term)]（按 vars 顺序）
        self.status = status         # ok / contradiction / positive-dim / partial / unsupported
        self.note = note


def _poly_in_vars(p, sub_vars):
    """p 是否只含 sub_vars（exps 在其余变量位全零）。"""
    idxs = [p.vars.index(v) for v in p.vars if v not in sub_vars]
    return all(all(k[i] == 0 for i in idxs) for k in p.monos)


def solve_system(fs, vars_, order="lex"):
    """零维多项式方程组 fs=0 的全部解（lex 消元 + 逐变量回代）。

    vars_ 顺序即 lex 优先级（vars_[0] 最先消去、最后解出）。策略：
    从最末变量开始，取 G 中只含它的基元素（消元定理保证零维时存在）
    解一元（复用 _poly_solve 全套：有理根/二次根式/RootOf），有理数解
    代入回代向上；根式/RootOf 解停止深入该分支（Poly 系数域是 Q，
    RootOf 系数多项式不支持——部分解如实标注 partial）。
    """
    from cas.solve import _poly_solve

    vars_ = tuple(vars_)
    if len(set(id(v) for v in vars_)) != len(vars_):
        return SolveSysResult([], "unsupported", "duplicate variables")
    polys = []
    for f in fs:
        if isinstance(f, T.Expr) and f.head.name == "Eq":
            # f = g 形态归一为 f - g（term 层入口友好）
            from cas.simplify import simplify, expand
            f = simplify(expand(T.plus(f.args[0], T.neg(f.args[1]))))
        try:
            p = Poly.from_term(f, vars_)
        except PolyError as ex:
            return SolveSysResult([], "unsupported", f"not polynomial: {ex}")
        if not p.is_zero():
            polys.append(p)
    if not polys:
        return SolveSysResult([], "identity", "all equations trivial")
    try:
        G = groebner(polys, order)
        G = reduced_basis(G, order)
    except (PolyError, BudgetExceeded) as ex:
        return SolveSysResult([], "unsupported", str(ex))
    if any(g.is_const() for g in G):
        return SolveSysResult([], "contradiction", "1 in ideal: no common zero")
    # 正维检测：最末变量没有只含它的基元素 -> 解集无穷（诚实拒答通解）。
    # lex 消元定理只保证 G ∩ k[vars_[-1]] 非空 ⟺ 消元到最末变量成功；
    # 前面变量的一元多项式在回代中自然出现，不在此要求。
    vlast = vars_[-1]
    if not any(_only_in(g, vlast, vars_[:-1]) for g in G):
        return SolveSysResult(
            [], "positive-dim",
            f"solution set is infinite (no univariate polynomial in {vlast.name}); "
            "general parametrization not supported",
        )
    sols, truncated = _solve_elim(G, list(vars_), {}, [], vars_)
    if truncated and not sols:
        return SolveSysResult([], "partial", "; ".join(sorted(set(truncated))))
    note = "; ".join(sorted(set(truncated))) if truncated else ""
    return SolveSysResult(sols, "ok" if not truncated else "partial", note)


def _project_univariate(g, v):
    """把只含 v 的多元 Poly 投影为一元 Poly（_poly_solve 只认 1 维指数）。"""
    vi = g.vars.index(v)
    return Poly((v,), {(k[vi],): c for k, c in g.monos.items()})


def _solve_elim(G, pending, assign, out, all_vars):
    """回代递归：pending = 尚未定值的变量（尾部对齐 lex 消元方向）。

    返回 (solutions[list[tuple]], truncations[list[str]])。
    """
    from cas.solve import _poly_solve
    from cas import term as T

    if len(out) >= _MAX_BRANCH:
        return out, ["branch limit exceeded"]
    if not pending:
        out.append(tuple(assign[v] for v in all_vars))
        return out, []
    v = pending[-1]          # 最末未定变量最先解（lex 消元方向）
    cands = [g for g in G if _only_in(g, v, pending[:-1])]
    if not cands:
        return out, [f"no elimination polynomial for {v.name}"]
    # 取含 v 的最低次基元素做一元求解（小规模下足够；gcd 合并是优化项）
    best = _project_univariate(min(cands, key=lambda g: g.degree(v)), v)
    r = _poly_solve(best, v)
    if r.status == "identity":
        # 该变量自由（正维漏检防御）——不应到达
        return out, [f"{v.name} unconstrained"]
    if r.status != "ok":
        return out, [f"{v.name}: {r.note or r.status}"]
    trunc = []
    for sol in r.solutions:
        if T.is_num(sol):
            val = T.num_val(sol)
            newG = [_subst_const(g, v, val) for g in G]
            newG = [g for g in newG if not g.is_zero()]
            if any(g.is_const() for g in newG):
                continue   # 该分支矛盾（解不满足其余方程）
            assign[v] = sol
            _solve_elim(newG, pending[:-1], dict(assign), out, all_vars)
        else:
            # 根式/RootOf 解：Q 系数域无法继续回代——分支截断（诚实）
            from cas.pprint import to_str
            trunc.append(
                f"back-substitution stopped at {v.name} = {to_str(sol)} "
                "(non-rational root; algebraic-coefficient extension not supported)"
            )
    return out, trunc


def _idx(p, v):
    return p.vars.index(v)


def _only_in(g, v, exclude):
    """g 是只含 v 的一元多项式（exclude 中变量位全零；常数项允许）。"""
    ex_idx = [_idx(g, u) for u in exclude]
    vi = _idx(g, v)
    seen_v = False
    for k in g.monos:
        if any(k[i] != 0 for i in ex_idx):
            return False
        if k[vi] != 0:
            seen_v = True
    return seen_v


def _subst_const(g, v, val):
    """把变量 v 替换为有理常数 val（重排 monos：去掉 v 维度）。"""
    vi = _idx(g, v)
    nv = tuple(u for u in g.vars if u is not v)
    out = {}
    for k, c in g.monos.items():
        e = val ** k[vi]
        nk = tuple(x for i, x in enumerate(k) if i != vi)
        acc = c * e
        old = out.get(nk)
        out[nk] = acc if old is None else old + acc
    return Poly(nv, {k: v2 for k, v2 in out.items() if v2 != 0})
