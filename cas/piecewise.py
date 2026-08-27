# -*- coding: utf-8 -*-
"""分段函数容器：Piecewise 是语法容器，不是新数值域（架构五·边界裁定）。

结构：`Piecewise(v1, c1, v2, c2, ...)`——值 / 条件成对，驻留项。

三条裁定落地：

· 分支体不要求同一宿主结构——每个分支独立投影（`project_pw`），
  域是分支局部的，找不到共同宿主不是失败。
· 条件可以是任意命题——交判定管线，判得动给真值，判不动以 GUARDED
  未决传播（`select` / `coverage`）。
· 唯一被约束处是重叠区——两分支条件同时可满足时其值必须一致，
  能检出冲突就标注（`conflicts`）；覆盖完全性是使用者声明，可判时标注。

运算提升（`lift`）：域内运算逐分支进行，分支间互斥性由条件的合取保证。
"""

from cas import term as T
from cas.term import S, Expr
from cas.project import project
from cas.verdict import YES, NO, unknown, Reason


# ---------------------------------------------------------------------------
# 构造与拆解
# ---------------------------------------------------------------------------

_HEAD = "Piecewise"


def is_piecewise(t) -> bool:
    return isinstance(t, Expr) and t.head.name == _HEAD \
        and len(t.args) % 2 == 0


def piecewise(pairs) -> object:
    """(值, 条件) 序列 → 驻留 Piecewise。

    句法规范化（无数义判定）：丢条件为 FALSE 的分支、条件为 TRUE 者截断
    其后（首中即定，后不可达）、空容器坍缩为 Undefined、单真分支坍缩为值。
    """
    kept = []
    for v, c in pairs:
        if c is T.FALSE:
            continue
        kept.append((v, c))
        if c is T.TRUE:
            break                        # TRUE 之后的分支永不达
    if not kept:
        return T.SP("Undefined")
    if len(kept) == 1 and kept[0][1] is T.TRUE:
        return kept[0][0]
    flat = []
    for v, c in kept:
        flat.append(v)
        flat.append(c)
    return T.mk(S(_HEAD), tuple(flat))


def branches(t):
    """驻留 Piecewise → [(值, 条件)]。非分段项 → [(t, TRUE)]（平凡覆盖）。"""
    if not is_piecewise(t):
        return [(t, T.TRUE)]
    a = t.args
    return [(a[i], a[i + 1]) for i in range(0, len(a), 2)]


def conditions(t):
    return [c for _v, c in branches(t)]


def values(t):
    return [v for v, _c in branches(t)]


# ---------------------------------------------------------------------------
# 分支独立投影（架构核心裁定：无共享宿主）
# ---------------------------------------------------------------------------

def project_pw(t):
    """每分支投影到自己的宿主域——互不牵制。

    返回 [(值, 条件, Projected|None)]。Projected 为 None 表示该分支落在
    当前投影阶梯之外（ℚ / K[x] / K(x) 皆非成员），上层据此诚实处理。"""
    return [(v, c, project(v)) for v, c in branches(t)]


# ---------------------------------------------------------------------------
# 条件语义：判定管线消费
# ---------------------------------------------------------------------------

def select(t, ctx):
    """在上下文 ctx 下选分支。

    返回 (状态, 载荷)：
    · ("value", v)     恰有一分支被证明命中且其前皆假 → 坍缩为该值
    · ("residual", (pw, undecided))
                       无法唯一选定；pw 为已剔除可证假分支的剩余分段，
                       undecided 为该次判定传播的未决理由（首个 Unknown）
    """
    bs = branches(t)
    survivors = []
    first_unknown = None
    for v, c in bs:
        if c is T.TRUE:
            if not survivors:                       # 恒真且为分支 0：直接命中
                return ("value", v)
            survivors.append((v, c))
            break
        verdict = ctx.decide(c)
        if verdict is NO:
            continue                                # 恒假分支永不命中，剔除
        if verdict is YES:
            if not survivors:                       # 首个真分支且其前皆假
                return ("value", v)
            survivors.append((v, c))                # 重叠：先中优先，保留待标
            continue
        if first_unknown is None:
            first_unknown = verdict.reason
        survivors.append((v, c))
    if not survivors:
        return ("residual", (T.SP("Undefined"), Reason.FRAGMENT))
    return ("residual", (piecewise(survivors),
                         first_unknown or Reason.FRAGMENT))


def coverage(t, ctx):
    """分支条件之析取是否覆盖全空间（完全性是使用者声明，此处可判则判）。

    YES 完全覆盖；NO 存在可证空隙（所有条件皆假的地方无定义）；
    Unknown(GUARDED) 有条件未决，覆盖随之未决。"""
    conds = conditions(t)
    guarded = False
    for c in conds:
        if c is T.TRUE:
            return YES
        v = ctx.decide(c)
        if v is YES:
            return YES
        if v is NO:
            continue
        guarded = True
    return unknown(Reason.GUARDED) if guarded else NO


def conflicts(t, ctx, budget=100000):
    """重叠一致性：条件可同时成立处两值是否相等。

    逐对检测（不判覆盖，只看重叠是否良定义）。返回 [(i, j, Verdict)]——
    Verdict 是"此重叠区良定义"的判定：
    · YES 空重叠，或重叠处值恒等（良性 / 天然良定义）
    · NO 检出不一致：重叠可满足且两值在重叠处不等
    · Unknown 判定力所不及（GUARDED/FRAGMENT/UNDECIDABLE/BUDGET）

    判定失败绝不伪装成一致。"""
    from cas.decide import satisfiable
    bs = branches(t)
    out = []
    n = len(bs)
    for i in range(n):
        vi, ci = bs[i]
        for j in range(i + 1, n):
            vj, cj = bs[j]
            sat = satisfiable([ci, cj], ctx)      # 重叠区是否可满足
            if sat is NO:
                out.append((i, j, YES))            # 空重叠，天然良定义
                continue
            out.append((i, j, _agree(vi, vj, (ci, cj), ctx, budget)))
    return out


def _agree(vi, vj, conds, ctx, budget):
    """两值在重叠条件 conds 下是否相等：临时上下文注入条件后判等。"""
    if vi is vj:
        return YES
    tmp = ctx.clone()
    for c in conds:
        if c is not T.TRUE:
            tmp.assume(c, origin="_overlap", kind="guard")
    from cas.decide import equivalent
    return equivalent(vi, vj, tmp, budget)


# ---------------------------------------------------------------------------
# 逐分支运算提升
# ---------------------------------------------------------------------------

def lift(op, *terms, prune=True):
    """把 n 元运算 op 逐分支提升到 Piecewise 参数上（笛卡尔展开）。

    op 接收驻留项返回驻留项（如 T.plus / T.times）。非 Piecewise 参数视作
    恒真单分支。结果按 `piecewise` 规范化；prune=True 时丢弃合取条件可判
    为恒假的分支。"""
    if not any(is_piecewise(x) for x in terms):
        return op(*terms)
    exps = [branches(x) for x in terms]
    combos = [[]]
    for ex in exps:
        combos = [c + [b] for c in combos for b in ex]
    pairs = []
    for combo in combos:
        vals = [v for v, _c in combo]
        conds = [c for _v, c in combo]
        conj = _and_all(conds)
        if prune and conj is T.FALSE:
            continue
        pairs.append((op(*vals), conj))
    return piecewise(pairs)


def _and_all(conds):
    keep = []
    for c in conds:
        if c is T.FALSE:
            return T.FALSE
        if c is T.TRUE:
            continue
        if isinstance(c, Expr) and c.head.name == "And":
            keep.extend(c.args)
        else:
            keep.append(c)
    if not keep:
        return T.TRUE
    return T.and_(*keep)
