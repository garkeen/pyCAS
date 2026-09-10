# -*- coding: utf-8 -*-
"""阶段4/5 压力台架：分段求导 + 分段解方程 + REPL 通道端到端（全部自证）。

  P36 分段求导          随机分段多项式：逐支导数 == 域层导数（p_deriv 独立
                        重建，两条通道）；分段点胞腔集合 == 分界点集合
  P37 分段解方程        随机分段线性函数 = target：点解 == 独立参照
                        （逐支 -b/a 候选 + 分支条件有理比较筛选）；
                        区域解（常值支恒等）/条件解/非线性支拒答
  P38 工作流端到端      Claim(分段方程) → Solve 点解全部入账且验证通过
                        （回代判官走分段选支）；Claim(分段) → Diff 步骤
                        经逐支域层交叉验证通过；伪解（条件不满足的候选）
                        被判官否决为 dead

用法：python stress/stress_stage45.py [轮数] [种子]
"""

import sys
import random
from fractions import Fraction as Fr

sys.path.insert(0, ".")

import library
library.load_all()

import cas.syntax.term as T
from cas.syntax.term import S
from cas.frontend.parser import parse
from cas.frontend.pprint import to_str
from cas.math.qarith import fold
from cas.math.diff import differentiate_piecewise
from cas.math.tactics import solve_piecewise, TacticsError
from cas.errors import DiffError, CadError
from cas.math.domains.q import Q_RING
from cas.math.domains.poly import from_term, p_deriv, to_term
from cas.math.piecewise import piecewise, fold_nested, branches
from cas.workflow.workflow import Workflow, Claim, Solve, Diff

X = S("x")


def fail(msg, seed, *extra):
    print(f"FAIL [{msg}] seed={seed}")
    for e in extra:
        print("  ", e)
    sys.exit(1)


def rand_lin(rng):
    """随机线性函数 a·x + b（a≠0），返回 (项, a, b)。"""
    a = Fr(rng.randint(-5, 5), rng.choice((1, 1, 2)))
    while a == 0:
        a = Fr(rng.randint(-5, 5), 2)
    b = Fr(rng.randint(-6, 6), rng.choice((1, 1, 3)))
    t = T.plus(T.times(T.N(a), X), T.N(b))
    return fold(t), a, b


def _num(t):
    f = fold(t)
    if not T.is_num(f):
        return None
    return T.num_val(f)


# ---------------------------------------------------------------------------
# P36：分段求导——逐支两条通道交叉 + 分段点定位
# ---------------------------------------------------------------------------

def prop_piecewise_diff(rounds, rng):
    for i in range(rounds):
        r = Fr(rng.randint(-4, 4), rng.choice((1, 1, 2)))
        p1, _, _ = rand_lin(rng)
        p2, _, _ = rand_lin(rng)
        pw = piecewise([(p1, parse(f"x <= {r}")), (p2, parse(f"x > {r}"))])
        try:
            deriv, bounds = differentiate_piecewise(pw, X)
        except (DiffError, CadError) as e:
            fail("P36 分段求导拒答", i, to_str(pw), e)
        bs = branches(fold_nested(deriv))
        if len(bs) != 2:
            fail("P36 导数分支数", i, to_str(deriv))
        # 逐支：项层结果 vs 域层导数（p_deriv 独立重建）
        for (v, c), src in zip(bs, (p1, p2)):
            p = from_term(Q_RING, src, (X,))
            expect = to_term(Q_RING, p_deriv(Q_RING, p, 0))
            got = fold(v)
            if _num(T.plus(got, T.neg(expect))) != 0:
                fail("P36 逐支导数与域层不符", i, to_str(src),
                     to_str(got), to_str(expect))
        # 分段点胞腔集合 == 分界点集合
        pts = [c.iso[0] for c in bounds if c.iso[0] == c.iso[1]]
        if pts != [r]:
            fail("P36 分段点集合", i, r, pts)


# ---------------------------------------------------------------------------
# P37：分段解方程——独立参照（算术直算，不走判定管线）
# ---------------------------------------------------------------------------

def ref_solve(pairs, target):
    """参照通道：逐支 -b/a 候选 + 分支条件直接有理比较筛选。"""
    out = []
    for (a, b, lo, hi, lo_open, hi_open) in pairs:
        cand = (target - b) / a
        if lo is not None and (cand <= lo if lo_open else cand < lo):
            continue
        if hi is not None and (cand >= hi if hi_open else cand > hi):
            continue
        out.append(cand)
    return sorted(out)


def prop_piecewise_solve(rounds, rng):
    for i in range(rounds):
        r = Fr(rng.randint(-4, 4), 1)
        t1, a1, b1 = rand_lin(rng)
        t2, a2, b2 = rand_lin(rng)
        pw = piecewise([(t1, parse(f"x <= {r}")), (t2, parse(f"x > {r}"))])
        target = Fr(rng.randint(-6, 6), 1)
        try:
            res = solve_piecewise(pw, X, T.N(target))
        except TacticsError as e:
            fail("P37 线性分段被拒", i, to_str(pw), e)
        got = sorted(T.num_val(s) for s in res["points"])
        want = ref_solve([(a1, b1, None, r, True, False),
                          (a2, b2, r, None, True, True)], target)
        if got != want:
            fail("P37 点解与参照不符", i, to_str(pw), target, got, want)
        if res["regions"] or res["conditional"]:
            fail("P37 线性分段不应有区域/条件解", i, res)
        # 常值支恒等 → 区域解
        c_pw = piecewise([(T.N(target), parse(f"x < {r}")),
                          (T.N(target + 1), parse(f"x >= {r}"))])
        res2 = solve_piecewise(c_pw, X, T.N(target))
        if len(res2["regions"]) != 1 or res2["points"]:
            fail("P37 区域解缺失", i, res2)
        # 非线性支 → 诚实拒答
        nl = piecewise([(parse("x*x"), parse(f"x <= {r}")),
                        (t2, parse(f"x > {r}"))])
        try:
            solve_piecewise(nl, X, T.N(target))
            fail("P37 非线性支未拒答", i)
        except TacticsError:
            pass
        # 含 x 的目标：常值支方程 k1 = m·x+b 的解不得因分支分类丢失；
        # 退化支（恒等→区域解、矛盾→无贡献）不得误拒。参照为直算算术。
        k1 = Fr(rng.randint(-5, 5), 1)
        m = Fr(rng.randint(-4, 4), rng.choice((1, 1, 2)))
        while m == 0:
            m = Fr(rng.randint(-4, 4), 2)
        b = Fr(rng.randint(-5, 5), 1)
        a2v = Fr(rng.randint(-4, 4), rng.choice((1, 1, 2)))
        while a2v == m:                    # 同斜率退化单独测（见下）
            a2v = Fr(rng.randint(-4, 4), 2)
        b2v = Fr(rng.randint(-5, 5), 1)
        tgt = fold(T.plus(T.times(T.N(m), X), T.N(b)))
        pw3 = piecewise([(T.N(k1), parse(f"x <= {r}")),
                         (fold(T.plus(T.times(T.N(a2v), X), T.N(b2v))),
                          parse(f"x > {r}"))])
        res3 = solve_piecewise(pw3, X, tgt)
        want3 = []
        x1 = (k1 - b) / m                  # k1 = m·x + b
        if x1 <= r:
            want3.append(x1)
        x2 = (b - b2v) / (a2v - m)         # a2·x + b2 = m·x + b
        if x2 > r:
            want3.append(x2)
        got3 = sorted(T.num_val(s) for s in res3["points"])
        if got3 != sorted(want3) or res3["regions"] or res3["conditional"]:
            fail("P37 含x目标丢解/多解", i, k1, m, b, a2v, b2v, r,
                 got3, sorted(want3), res3)
        # 恒等支（v ≡ target，差值形状含 x、投影后恒零）→ 区域解
        id_pw = piecewise([(tgt, parse(f"x <= {r}")),
                           (T.N(k1), parse(f"x > {r}"))])
        res4 = solve_piecewise(id_pw, X, tgt)
        want4 = [x1] if x1 > r else []
        got4 = sorted(T.num_val(s) for s in res4["points"])
        if len(res4["regions"]) != 1 or got4 != sorted(want4) \
                or res4["conditional"]:
            fail("P37 恒等支未给区域解", i, k1, m, b, r, res4, want4)
        # 矛盾支（v = target+1，差值投影后非零常数）→ 无贡献
        con_pw = piecewise([(fold(T.plus(tgt, T.N(1))), parse(f"x <= {r}")),
                            (T.N(k1), parse(f"x > {r}"))])
        res5 = solve_piecewise(con_pw, X, tgt)
        want5 = [x1] if x1 > r else []
        got5 = sorted(T.num_val(s) for s in res5["points"])
        if got5 != sorted(want5) or res5["regions"] or res5["conditional"]:
            fail("P37 矛盾支未静默无贡献", i, k1, m, b, r, res5, want5)


# ---------------------------------------------------------------------------
# P38：工作流端到端（阶段5 REPL 通道的引擎层）
# ---------------------------------------------------------------------------

def prop_workflow(rounds, rng):
    for i in range(rounds):
        r = Fr(rng.randint(-4, 4), 1)
        t1, a1, b1 = rand_lin(rng)
        t2, a2, b2 = rand_lin(rng)
        target = Fr(rng.randint(-6, 6), 1)
        wf = Workflow()
        s0 = wf.add(T.eq(piecewise([(t1, parse(f"x <= {r}")),
                                    (t2, parse(f"x > {r}"))]),
                         T.N(target)), Claim())
        want = ref_solve([(a1, b1, None, r, True, False),
                          (a2, b2, r, None, True, True)], target)
        for xv in want:
            s = wf.add(T.eq(X, T.N(xv)), Solve(pred=s0.id, var=X,
                                               solution=T.N(xv)))
            if s.status == "dead":
                fail("P38 真解被回代判官否决", i, r, target, xv, s.note)
        # 伪解：另一支的候选（条件不满足）必须被判官否决
        wrong = ref_solve([(a1, b1, r, None, True, True)], target)  # 强制右区
        for xv in wrong:
            if xv in want:
                continue
            s = wf.add(T.eq(X, T.N(xv)), Solve(pred=s0.id, var=X,
                                               solution=T.N(xv)))
            if s.status != "dead":
                fail("P38 伪解未被否决", i, r, target, xv)
        # 分段求导步骤：逐支域层交叉验证须通过
        s1 = wf.add(piecewise([(t1, parse(f"x <= {r}")),
                               (t2, parse(f"x > {r}"))]), Claim())
        d, _b = differentiate_piecewise(s1.content, X)
        s2 = wf.add(d, Diff(pred=s1.id, var=X))
        if s2.status == "dead":
            fail("P38 分段 Diff 被交叉验证否决", i, to_str(s1.content),
                 to_str(d), s2.note)


if __name__ == "__main__":
    rounds = int(sys.argv[1]) if len(sys.argv) > 1 else 500
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 20260828
    print(f"== 阶段4/5 压力台架：rounds={rounds} seed={seed} ==")
    rng = random.Random(seed)
    prop_piecewise_diff(rounds, rng)
    print(f"P36 分段求导两通道交叉 {rounds} 轮通过")
    prop_piecewise_solve(rounds, rng)
    print(f"P37 分段解方程独立参照 {rounds} 轮通过")
    prop_workflow(rounds, rng)
    print(f"P38 工作流端到端验证   {rounds} 轮通过")
    print("== 全部通过 ==")
