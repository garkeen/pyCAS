# -*- coding: utf-8 -*-
"""回代判官：验证系统的原子（docs/cas_v3_arch.md 七.2）。

"某个候选值是不是解"的唯一权威在这里：代入 → 折叠 → 判零。判零走
域投影标准形（cas/project.zero_of）；含分段项时先按有序首中点塌缩
再判（数值点至多落一支，取值唯一，判零无歧义）。

架构条款的落地位置：
· 验证器与求解器是两套独立实现（1.4）——本模块是验证器，只回代，
  不重跑求解公式。求解器在 cas/tactics，二者不共享代码路径。
· 未决不是通过（1.5）：判不动返回 None，调用方据此诚实回未决，
  绝不把 None 当真或当假使用。
· 定义域外**不是未决而是非解**：塌缩出 Undefined 的点等式无值，
  这是有证据的否证，返回 False 而非 None。

职责收拢说明：本判官曾分散在两处——workflow._piecewise_aware_zero
（私有）与 repl.cmd_check 内的内联实现，两处的通道顺序已经分叉
（repl 先试 eval_exact、失败才落分段判零；workflow 只走后者）。
裁决权威现归本模块一处：判零一律走 zero_of（覆盖严格广于环层
eval_exact），eval_exact 只用于取展示值，不参与裁决。
"""

from dataclasses import dataclass

from cas import term as T
from cas.term import Expr
from cas.verdict import Verdict, YES, NO, unknown
from cas.qarith import fold, eval_exact, EvalNumError
from cas.project import zero_of


# ---------------------------------------------------------------------------
# 结构探测
# ---------------------------------------------------------------------------

def has_piecewise(t) -> bool:
    """项中是否含分段子项（决定是否走点塌缩通道）。"""
    from cas.piecewise import is_piecewise
    if is_piecewise(t):
        return True
    if isinstance(t, Expr):
        return any(has_piecewise(a) for a in t.args)
    return False


def has_undef(t) -> bool:
    """项中是否出现 Undefined（该点不在定义域内）。"""
    if t is T.SP("Undefined"):
        return True
    if isinstance(t, Expr):
        return any(has_undef(a) for a in t.args)
    return False


# ---------------------------------------------------------------------------
# 判零
# ---------------------------------------------------------------------------

def is_zero(t) -> bool | None:
    """分段感知判零：普通项走域标准形判零；含分段项先点塌缩再判。

    返回 True / False / None（None 为判不动，调用方必须诚实回未决）。
    塌缩出 Undefined 的点不在定义域内，等式在此点无值——不是解，
    返回 False。
    """
    if not has_piecewise(t):
        return zero_of(t)
    from cas.piecewise import collapse        # 延迟：piecewise 消费判定层
    from cas.context import Context
    c = collapse(t, Context())
    if c is None:
        return None                           # 选支未决：条件判不动
    if has_undef(c):
        return False                          # 定义域外：等式无值，非解
    return zero_of(fold(c))


# ---------------------------------------------------------------------------
# 回代
# ---------------------------------------------------------------------------

@dataclass(frozen=True, slots=True)
class BackSub:
    """回代结果。

    · diff  代入并折叠后的两侧差值（展示与取证用）
    · zero  裁决：True 是解 / False 非解 / None 判不动
    · exact 差值的精确有理值，仅在环层可求时非 None（展示用，不参与裁决）
    """
    diff: object
    zero: bool | None
    exact: object | None


def back_substitute(eq, var, value) -> BackSub:
    """把 var := value 代入等式 eq，返回差值与判零裁决。

    只依赖 eq 两侧做差，不重跑任何求解公式。判零权威是 is_zero
    （域标准形），exact 仅供展示——两者都是精确算术，不存在浮点。
    """
    lhs, rhs = eq.args
    diff = fold(T.plus(T.subst(lhs, {var: value}),
                       T.neg(T.subst(rhs, {var: value}))))
    try:
        v = eval_exact(diff, {})
    except EvalNumError:
        v = None
    return BackSub(diff=diff, zero=is_zero(diff), exact=v)


# ---------------------------------------------------------------------------
# 守卫
# ---------------------------------------------------------------------------

@dataclass(frozen=True, slots=True)
class GuardCheck:
    """单条守卫的回代裁决结果。"""
    guard: object       # 原守卫项
    subst: object       # 代入后的守卫项
    verdict: Verdict    # 判定管线的裁决


def guard_report(guards, var, value, ctx=None) -> tuple[GuardCheck, ...]:
    """守卫逐条回代后交判定管线裁决（全谓词头 + 复合命题，不白名单）。

    守卫不是可选的附加检查：解只在守卫成立处是解。任一守卫 No 或未决，
    整体都不能判定为验证通过。
    """
    from cas.decide import decide
    from cas.context import Context
    if ctx is None:
        ctx = Context()
    out = []
    for g in guards:
        gsub = fold(T.subst(g, {var: value}))
        out.append(GuardCheck(guard=g, subst=gsub, verdict=decide(gsub, ctx)))
    return tuple(out)


def verify_solution(eq, var, value, guards=(), ctx=None) -> Verdict:
    """完整判定：回代判零 + 守卫全部成立，两者皆过才是解。

    三个出口与架构 1.5 对齐：
    · 判零为 False，或任一守卫 No            -> NO（携带证据的否证）
    · 判零为 None，或任一守卫未决             -> Unknown（诚实未决）
    · 判零为 True 且守卫全 Yes                -> YES
    """
    bs = back_substitute(eq, var, value)
    if bs.zero is False:
        return NO
    checks = guard_report(guards, var, value, ctx)
    if any(c.verdict is NO for c in checks):
        return NO
    if bs.zero is None or any(c.verdict is not YES for c in checks):
        return unknown()
    return YES
