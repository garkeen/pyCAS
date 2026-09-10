"""随机压力台架（cas_v3_arch.md 九 验收方法论：生成验证，非手写案例）。

四条性质，全部自证、无需外部真值：
  P1 折叠保真    eval_exact(t, env) == eval_exact(fold(t), env)
  P2 幂等指针    fold(fold(t)) is fold(t)   （内容寻址 ⇒ 结构同 ⇒ 指针同）
  P3 区间通道    假设 x>k 后，查询 x>j 的三值真值表
  P4 回代判官    预埋根的方程展开后逐根回代必须精确为 0，
                 非根样本必须非 0 —— 未来战术层的验收原型

用法：python stress/stress_qarith.py [轮数] [种子]
任一失败打印最小反例与种子，退出码 1。
"""

import sys
import random
from fractions import Fraction as Fr

sys.path.insert(0, ".")

from cas.syntax.term import S, N, mk, plus, times, pw, neg, Expr, Int
from cas.math.qarith import fold, eval_exact, EvalNumError
from cas.kernel.scope import Assumptions
from cas.math.decide import decide, branch
from cas.kernel.verdict import YES, Unknown
from cas.math.simplify import expand

from cas.runtime import bootstrap
bootstrap()

X, Y = S("x"), S("y")


# ---------------------------------------------------------------------------
# 生成器：随机环层项（深度有界，字面量小分母）
# ---------------------------------------------------------------------------

def gen_lit(rng):
    n = rng.randint(-9, 9)
    if rng.random() < 0.3:
        return N(Fr(n, rng.choice((2, 3, 4, 5, 7))))
    return N(n)


def gen(d, rng):
    if d == 0:
        r = rng.random()
        if r < 0.45:
            return gen_lit(rng)
        return X if rng.random() < 0.7 else Y
    r = rng.random()
    if r < 0.40:
        return plus(*(gen(d - 1, rng) for _ in range(rng.randint(2, 3))))
    if r < 0.80:
        return times(*(gen(d - 1, rng) for _ in range(rng.randint(2, 3))))
    # 整数幂：指数 0..3 安全（负指数由 gen_safe 处理）
    b = gen(d - 1, rng)
    return pw(b, N(rng.randint(0, 3)))


def gen_safe(d, rng):
    """gen 的保守版：负指数仅作用于非零字面底（避开未定义域争议）。"""
    t = gen(d, rng)

    def fix(u):
        if not isinstance(u, Expr):
            return u
        if u.head.name == "Power":
            b, e = u.args
            b2 = fix(b)
            ev = e.v if isinstance(e, Int) else None
            if ev is not None and ev < 0:
                if isinstance(b2, Int) and b2.v != 0:
                    return pw(b2, e)
                return b2                      # 弃负指数，保底数
            return mk(u.head, (b2, e))
        return mk(u.head, tuple(fix(a) for a in u.args))

    return fix(t)


def fail(msg, seed, t=None):
    print(f"FAIL [{msg}] seed={seed}")
    if t is not None:
        print("  term:", t)
    sys.exit(1)


# ---------------------------------------------------------------------------
# P1/P2：折叠保真与幂等
# ---------------------------------------------------------------------------

def prop_fold(rounds, rng):
    envs = [{X: Fr(a, b), Y: Fr(c, e)}
            for a, b, c, e in [(1, 3, -2, 5), (7, 2, 1, 1), (-4, 9, 5, 3),
                               (0, 1, 11, 6), (13, 4, -7, 8)]]
    for i in range(rounds):
        t = gen_safe(rng.randint(1, 4), rng)
        ft = fold(t)
        if fold(ft) is not ft:
            fail("P2 幂等指针", rng.seed if hasattr(rng, "seed") else "?", t)
        for env in envs:
            try:
                v1 = eval_exact(t, env)
                v2 = eval_exact(ft, env)
            except EvalNumError:
                continue
            if v1 != v2:
                fail(f"P1 保真 env={env}", i, t)


# ---------------------------------------------------------------------------
# P3：区间通道三值真值表
# ---------------------------------------------------------------------------

def prop_interval(rounds, rng):
    for _ in range(rounds):
        k = rng.randint(-5, 5)
        assumptions = Assumptions().extended(mk(S("Gt"), (X, N(k))))
        for j in range(-7, 8):
            got = decide(mk(S("Gt"), (X, N(j))), assumptions)
            if j <= k:
                ok = got is YES
            else:
                ok = isinstance(got, Unknown)
            if not ok:
                fail(f"P3 区间 assume x>{k} 查 x>{j}: got {got}", k)
        _cond, b_assumptions, _st = branch(
            assumptions, mk(S("Lt"), (X, N(k + 10))))[0]
        got = decide(mk(S("Lt"), (X, N(k + 100))), b_assumptions)
        if got is not YES:
            fail(f"P3 分支帧继承", k)


# ---------------------------------------------------------------------------
# P4：回代判官（预埋根 -> 展开 -> 精确回代）
# ---------------------------------------------------------------------------

def _rand_root(rng):
    return Fr(rng.randint(-6, 6), rng.choice((1, 1, 1, 2, 3)))


def prop_backsub(rounds, rng):
    for i in range(rounds):
        roots = [_rand_root(rng) for _ in range(rng.randint(1, 3))]
        p = N(1)
        for r in roots:
            p = times(p, plus(X, neg(N(r))))
        expanded = expand(p)
        folded = fold(expanded)
        for r in roots:
            if eval_exact(folded, {X: r}) != 0:
                fail(f"P4 根回代非零 r={r}", i, expanded)
        for _ in range(4):
            bad = Fr(rng.randint(-9, 9), rng.choice((1, 2)))
            if bad in roots:
                continue
            if eval_exact(folded, {X: bad}) == 0:
                fail(f"P4 非根误判零 bad={bad}", i, expanded)


if __name__ == "__main__":
    rounds = int(sys.argv[1]) if len(sys.argv) > 1 else 2000
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 20260826
    print(f"== 压力台架：rounds={rounds} seed={seed} ==")
    rng = random.Random(seed)
    prop_fold(rounds, rng)
    print(f"P1+P2 折叠保真/幂等   {rounds} 轮通过")
    prop_interval(200, rng)
    print(f"P3 区间通道           200×15 查询通过")
    prop_backsub(min(rounds, 500), rng)
    print(f"P4 回代判官           {min(rounds, 500)} 轮通过")
    print("== 全部通过 ==")
