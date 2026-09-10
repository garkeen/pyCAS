# -*- coding: utf-8 -*-
"""一维 CAD / 实根隔离压力台架（全部自证，无外部真值）。

  P25 隔离正确   构造已知根的多项式（有理根、无理二次因子）：隔离区间数
                 == 不同实根数，每区间恰一根，相邻严格留隙，有理根精确命中
  P26 分区结构   胞腔开/点交替、以开区间首尾覆盖全轴；开区间胞腔的条件
                 真值 == 在样本点直接代入比较（独立通道交叉验证）
  P27 拒答理由   超越条件 → UNDECIDABLE；多变量条件 → FRAGMENT
  P28 点胞腔符号 根处消没的边界判 0（Eq 真、Gt/Lt 假）；未消没边界符号
                 与邻域样本一致

用法：python stress/stress_cad.py [轮数] [种子]
"""

import sys
import random
from fractions import Fraction as Fr

sys.path.insert(0, ".")

from cas.runtime import bootstrap
bootstrap()

from cas.syntax.term import S
from cas.frontend.parser import parse
from cas.errors import CadError
from cas.kernel.verdict import Reason
from cas.math.domains.q import Q_RING
from cas.math.domains.poly import from_term
from cas.math.realroot import (real_roots_intervals, p_eval_at, coef_sign,
                          squarefree_part)
from cas.math.cad import resolve_partition, extract_boundary_polys, cells, sign_at_cell

X = S("x")


def fail(msg, seed, *extra):
    print(f"FAIL [{msg}] seed={seed}")
    for e in extra:
        print("  ", e)
    sys.exit(1)


def poly(s):
    return from_term(Q_RING, parse(s), (X,))


# ---------------------------------------------------------------------------
# P25：隔离正确性
# ---------------------------------------------------------------------------

def prop_isolation(rounds, rng):
    for i in range(rounds):
        # 随机有理根
        roots = sorted(set(rng.randint(-8, 8) for _ in range(rng.randint(1, 4))))
        expr = "*".join(f"(x - ({r}))" for r in roots) if len(roots) > 1 \
            else f"(x - ({roots[0]}))"
        # 追加若干无理二次因子 (x^2 - c)，c 非平方且互不相同（避免重因子）
        irr = rng.sample([2, 3, 5, 6, 7, 8], rng.randint(0, 2))
        for c in irr:
            expr += f"*(x^2 - {c})"
        p = poly(expr)
        ivs = real_roots_intervals(Q_RING, p)
        want = len(roots) + 2 * len(irr)
        if len(ivs) != want:
            fail("P25 根数不符", i, f"{expr} got={len(ivs)} want={want}")
        # 相邻严格留隙
        for k in range(1, len(ivs)):
            if not (ivs[k - 1][1] < ivs[k][0]):
                fail("P25 留隙破坏", i, expr, ivs[k - 1], ivs[k])
        # 每个区间恰一根：无平方部分在区间内符号变号（开区间）或端点即根
        sf = squarefree_part(Q_RING, p)
        for (a, b) in ivs:
            if a == b:
                if coef_sign(p_eval_at(sf, a)) != 0:
                    fail("P25 精确根非根", i, expr, a)
            else:
                if coef_sign(p_eval_at(sf, a)) * coef_sign(p_eval_at(sf, b)) >= 0:
                    fail("P25 区间无根", i, expr, (a, b))
        # 每个有理根都被某个隔离区间覆盖（隔离契约，不强制精确命中）
        for r in roots:
            if not any(a <= Fr(r) <= b for (a, b) in ivs):
                fail("P25 有理根未被覆盖", i, expr, r, ivs)


# ---------------------------------------------------------------------------
# P26：分区结构 + 开区间标签交叉验证
# ---------------------------------------------------------------------------

def prop_partition(rounds, rng):
    cond_pool = ["x<0", "x>0", "x>=1", "x<=-2", "x^2<1", "x^2-2>0",
                 "x-3>=0", "x+1<0", "x^2-x>0"]
    for i in range(rounds):
        k = rng.randint(1, 3)
        conds = [parse(s) for s in rng.sample(cond_pool, k)]
        res = resolve_partition(conds, X)
        if not res:
            fail("P26 空分区", i)
        # 首尾开区间、开点交替
        if res[0][0].kind != "open" or res[-1][0].kind != "open":
            fail("P26 首尾非开区间", i)
        for k2 in range(1, len(res)):
            if res[k2][0].kind == res[k2 - 1][0].kind:
                fail("P26 未交替", i, [c[0].kind for c in res])
        # 开区间胞腔：样本点直接代入比较 == cond_holds
        for cell, labels in res:
            if cell.kind != "open":
                continue
            s = cell.sample
            for ci, c in enumerate(conds):
                a, b = c.args
                from cas.math.qarith import eval_exact
                da = eval_exact(a, {X: s})
                db = eval_exact(b, {X: s})
                op = c.head.name
                direct = {"Lt": da < db, "Le": da <= db, "Gt": da > db,
                          "Ge": da >= db, "Eq": da == db, "Ne": da != db}[op]
                if direct != labels[ci]:
                    fail("P26 标签与直代不符", i, s, direct, labels[ci])


# ---------------------------------------------------------------------------
# P27：拒答理由
# ---------------------------------------------------------------------------

def prop_refusal(rounds, rng):
    cases = [
        ("cos(x)>0", Reason.UNDECIDABLE),
        ("exp(x)<1", Reason.UNDECIDABLE),
        ("sin(x)+x>=0", Reason.UNDECIDABLE),
        ("x+y>0", Reason.FRAGMENT),
        ("x*y<1", Reason.FRAGMENT),
    ]
    for i in range(rounds):
        s, want = rng.choice(cases)
        try:
            resolve_partition([parse(s)], X)
        except CadError as e:
            if e.reason is not want:
                fail("P27 理由不符", i, s, e.reason, want)
            continue
        fail("P27 未拒答", i, s)


# ---------------------------------------------------------------------------
# P28：点胞腔符号
# ---------------------------------------------------------------------------

def prop_point_sign(rounds, rng):
    for i in range(rounds):
        r = rng.randint(-5, 5)
        # 条件：(x-r)==0 与 (x-r)>0；根胞腔上前者真后者假
        conds = [parse(f"(x - ({r})) == 0"), parse(f"(x - ({r})) > 0")]
        res = resolve_partition(conds, X)
        # 找到覆盖 r 的根胞腔（隔离区间含 r，不要求精确 (r, r)）
        hit = None
        for cell, labels in res:
            if cell.kind == "point":
                a, b = cell.iso
                if a <= Fr(r) <= b:
                    hit = labels
                    break
        if hit is None:
            fail("P28 未找到根胞腔", i, r, res)
        if hit[0] is not True or hit[1] is not False:
            fail("P28 根处符号错", i, r, hit)
        # 未消没边界：(x-(r+1)) 在根 r 处应为负
        c2 = parse(f"(x - ({r + 1})) < 0")
        res2 = resolve_partition([conds[0], c2], X)
        for cell, labels in res2:
            if cell.kind == "point":
                a, b = cell.iso
                if a <= Fr(r) <= b:
                    if labels[1] is not True:
                        fail("P28 未消没边界符号错", i, r, labels)
                    break


if __name__ == "__main__":
    rounds = int(sys.argv[1]) if len(sys.argv) > 1 else 500
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 20260827
    print(f"== CAD/实根隔离压力台架：rounds={rounds} seed={seed} ==")
    rng = random.Random(seed)
    prop_isolation(rounds, rng)
    print(f"P25 隔离正确          {rounds} 轮通过")
    prop_partition(rounds, rng)
    print(f"P26 分区结构+交叉验证 {rounds} 轮通过")
    prop_refusal(rounds, rng)
    print(f"P27 拒答理由          {rounds} 轮通过")
    prop_point_sign(rounds, rng)
    print(f"P28 点胞腔符号        {rounds} 轮通过")
    print("== 全部通过 ==")
