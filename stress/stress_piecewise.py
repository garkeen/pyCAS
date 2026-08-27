# -*- coding: utf-8 -*-
"""分段容器随机压力台架。

四条性质，全部自证、无需外部真值：
  P21 投影独立   分支体各自投影到自己的宿主域，无共享宿主要求——
                 逐分支 project 与独立 project 逐位一致，多项式与有理
                 函数分支（乃至片段外分支）在同一容器内共存不报错
  P22 选支语义   select 命中"首个真分支且其前皆假"：以账本事实
                 （假设该支条件、否决其前条件）强制唯一命中 → 返回该支值
  P23 运算逐支   lift(op, p, q) 笛卡尔展开：分支数 = 积、条件 = 合取；
                 且在唯一命中的上下文里 select(lift) == op(select p, select q)
  P24 守卫条件化 dom_condition 对分段：每支体约束条件化为 ¬cond ∨ 约束，
                 与逐支独立提取再条件化一致；重叠一致性 conflicts 对可证
                 空重叠给 YES、可证不等常量重叠给 NO

用法：python stress/stress_piecewise.py [轮数] [种子]
"""

import sys
import random

sys.path.insert(0, ".")

import library
library.load_all()

from cas import term as T
from cas.term import S, N, mk, plus, times, pw
from cas.parser import parse
from cas.pprint import to_str
from cas.context import Context
from cas.project import project
from cas.verdict import YES, NO
from cas.domcond import dom_condition
from cas.piecewise import (piecewise, branches, project_pw, select, coverage,
                           conflicts, lift, is_piecewise)

X = S("x")


def fail(msg, seed, *extra):
    print(f"FAIL [{msg}] seed={seed}")
    for e in extra:
        print("  ", e)
    sys.exit(1)


def rand_cmp(rng):
    """x 与常量的严格比较，作为分支条件。"""
    op = rng.choice(("Gt", "Lt", "Ge", "Le"))
    k = rng.randint(-5, 5)
    return mk(S(op), (X, N(k)))


_COND_POOL = [mk(S(op), (X, N(k)))
              for op in ("Gt", "Lt", "Ge", "Le") for k in range(-5, 6)]


def rand_pw(rng, nvals, minb=2, maxb=4):
    """随机分段容器：分支条件互异（无重复），末尾 TRUE 兜底保证覆盖。"""
    nb = rng.randint(minb, maxb)
    conds = rng.sample(_COND_POOL, nb - 1)         # 互不相同的比较
    pairs = [(rng.choice(nvals), c) for c in conds]
    pairs.append((rng.choice(nvals), T.TRUE))
    return piecewise(pairs)


def at_ctx(a):
    """x = a 的具体点上下文（比较式数值可判）。"""
    ctx = Context()
    ctx.assume(mk(S("Eq"), (X, N(a))), origin="_pt")
    return ctx


def eval_at(c, a) -> bool:
    if c is T.TRUE:
        return True
    op = c.head.name
    b = T.num_val(c.args[1])
    return {"Gt": a > b, "Lt": a < b, "Ge": a >= b, "Le": a <= b}[op]


def ref_first(t, a):
    """参照扫描：x=a 时首个命中分支的值（真值定义，独立于 select）。"""
    for v, c in branches(t):
        if eval_at(c, a):
            return v
    return None


# ---------------------------------------------------------------------------
# P21：分支投影独立
# ---------------------------------------------------------------------------

def prop_projection(rounds, rng):
    het = [pw(X, N(2)),                            # K[x]
           parse("1/x"),                           # K(x)
           parse("(x^2+1)/(x-3)"),                 # K(x)
           X,                                      # K[x]
           parse("sin(x)")]                        # 片段外（无塔）→ None
    for i in range(rounds):
        nb = rng.randint(2, 5)
        picks = [rng.choice(het) for _ in range(nb)]
        conds = [rand_cmp(rng) for _ in range(nb - 1)] + [T.TRUE]
        t = piecewise(list(zip(picks, conds)))
        proj = project_pw(t)
        if len(proj) != len(branches(t)):
            fail("P21 分支数不符", i)
        for k, (v, c, hit) in enumerate(proj):
            solo = project(v)                       # 独立投影
            a = hit.name if hit else None
            b = solo.name if solo else None
            if a != b:
                fail("P21 投影非逐支独立", i, f"branch={k} v={to_str(v)}",
                     f"pw={a} solo={b}")
        # 关键裁定：异质宿主共存（多项式支 + 有理支 + 片段外支）不要求共同宿主
        names = [h.name if h else None for _v, _c, h in proj]
        if "K[x]" in names and "K(x)" in names and not is_piecewise(t):
            fail("P21 误判非分段", i)


# ---------------------------------------------------------------------------
# P22：选支语义（首个真支且其前皆假 → 唯一命中）
# ---------------------------------------------------------------------------

def prop_select(rounds, rng):
    vals = [N(k) for k in range(1, 6)]
    for i in range(rounds):
        t = rand_pw(rng, vals)
        for a in range(-7, 8):
            want = ref_first(t, a)
            st, payload = select(t, at_ctx(a))
            if want is None:
                if st == "value":
                    fail("P22 无命中的假命中", i, f"a={a}", to_str(t))
                continue
            if st != "value":
                fail("P22 具体点未坍缩", i, f"a={a}", f"t={to_str(t)}",
                     f"payload={payload}")
            if payload is not want:
                fail("P22 选错支", i, f"a={a} want={to_str(want)} "
                     f"got={to_str(payload)} t={to_str(t)}")
        # 末支 TRUE 恒覆盖——空上下文下不得谎报空隙（NO）
        if coverage(t, Context()) is NO:
            fail("P22 覆盖误判", i, to_str(t))


# ---------------------------------------------------------------------------
# P23：运算逐分支提升
# ---------------------------------------------------------------------------

def prop_lift(rounds, rng):
    vals = [N(k) for k in range(-4, 5)]
    for i in range(rounds):
        p = rand_pw(rng, vals, minb=2, maxb=3)
        q = rand_pw(rng, vals, minb=2, maxb=3)
        m = lift(T.plus, p, q)
        bp, bq = branches(p), branches(q)
        if len(branches(m)) != len(bp) * len(bq):
            fail("P23 展开分支数", i,
                 f"{len(branches(m))} != {len(bp)}*{len(bq)}")
        # 逐点一致：x=a 处 select(lift(plus,p,q)) == plus(select p, select q)
        for a in range(-7, 8):
            ctx = at_ctx(a)
            _, vp = select(p, ctx)
            _, vq = select(q, ctx)
            st_m, vm = select(m, ctx)
            if st_m != "value":
                fail("P23 提升后未命中", i, f"a={a}")
            if plus(vp, vq) is not vm:
                fail("P23 逐点不一致", i, f"a={a} "
                     f"plus({to_str(vp)},{to_str(vq)})={to_str(plus(vp,vq))} "
                     f"vs {to_str(vm)}")


# ---------------------------------------------------------------------------
# P24：守卫条件化 + 重叠一致性
# ---------------------------------------------------------------------------

def prop_guards(rounds, rng):
    bodies = [T.sqrt(X), parse("log(x)"), pw(X, N(-1)),
              T.sqrt(plus(pw(X, N(2)), N(1)))]
    for i in range(rounds):
        nb = rng.randint(2, 4)
        pairs = []
        conds = [rand_cmp(rng) for _ in range(nb - 1)] + [T.TRUE]
        for k in range(nb):
            pairs.append((rng.choice(bodies), conds[k]))
        t = piecewise(pairs)
        got = dom_condition(t)
        # 期望：每支体自身约束条件化为 ¬cond ∨ g（TRUE 支免条件化）
        want = []
        for v, c in branches(t):
            solo = dom_condition(v)
            neg = T.FALSE if c is T.TRUE else mk(S("Not"), (c,))
            for g in solo:
                want.append(mk(S("Or"), (neg, g)))
        if sorted(x._h for x in got) != sorted(x._h for x in want):
            fail("P24 守卫条件化不符", i,
                 f"got={[to_str(x) for x in got]}",
                 f"want={[to_str(x) for x in want]}")
        # 重叠一致性：常量支、可证空重叠 → 全 YES；可证不等常量重叠 → NO
        disjoint = piecewise([(N(1), mk(S("Gt"), (X, N(0)))),
                              (N(2), mk(S("Lt"), (X, N(0))))])
        for _a, _b, verdict in conflicts(disjoint, Context()):
            if verdict is not YES:
                fail("P24 空重叠误判", i, verdict)
        clash = piecewise([(N(1), mk(S("Gt"), (X, N(0)))),
                           (N(2), mk(S("Gt"), (X, N(0))))])
        vs = [verdict for _a, _b, verdict in conflicts(clash, Context())]
        if not any(v is NO for v in vs):
            fail("P24 常量冲突未检出", i, vs)


if __name__ == "__main__":
    rounds = int(sys.argv[1]) if len(sys.argv) > 1 else 500
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 20260827
    print(f"== 分段容器压力台架：rounds={rounds} seed={seed} ==")
    rng = random.Random(seed)
    prop_projection(rounds, rng)
    print(f"P21 投影独立          {rounds} 轮通过")
    prop_select(rounds, rng)
    print(f"P22 选支语义          {rounds} 轮通过")
    prop_lift(min(rounds, 200), rng)
    print(f"P23 运算逐支          {min(rounds,200)} 轮通过")
    prop_guards(rounds, rng)
    print(f"P24 守卫条件化+重叠   {rounds} 轮通过")
    print("== 全部通过 ==")
