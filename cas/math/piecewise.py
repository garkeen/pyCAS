# -*- coding: utf-8 -*-
"""分段函数容器：Piecewise 是语法容器，不是新数值域（架构五·边界裁定）。

结构：`Piecewise(v1, c1, v2, c2, ...)`——值 / 条件成对，驻留项。

求值语义（唯一，全模块一致）：**有序首中**（if / elif / else，标准 Piecewise）。
某点的值 = 声明序中第一个条件成立的分支之值；`c=⊤` 即"否则"支（仅在此前
各支都不成立处生效）。因每点至多落在一支上，取值**天然唯一**——不存在、
也绝不允许求值层面的语义冲突。三条落地裁定：

· 分支体不要求同一宿主结构——每个分支独立投影（`project_pw`），
  域是分支局部的，找不到共同宿主不是失败。
· 条件可以是任意命题——交判定管线，判得动给真值，判不动以 GUARDED
  未决传播（`select` 取值、`coverage` 覆盖）。
· `conflicts` 是**顺序无关性 lint**（非求值闸）：若两支区域交叠处值不相等，
  则该处取值取决于声明顺序——提示作者收紧为互斥守卫。判定不动即 Unknown，
  绝不谎报良定义。覆盖完全性是使用者声明，可判则判，不擅自补全。

运算提升（`lift`）：分段参与运算按点定义 `(f⊕g)(x)=f(x)⊕g(x)`，逐支笛卡尔
展开，条件取合取。注意：分段函数的**求导与积分在分段点须另行校验连续性
与单侧极限**，非逐支可交——审慎通道见 cas/diff.py 的 `differentiate_piecewise`
（分段点显式未验证）与 cas/integrate.py 的分段定积分（缺口/点洞拒答）。
"""

from cas.syntax import term as T
from cas.syntax.term import S, Expr
from cas.math.project import project
from cas.kernel.verdict import YES, NO, unknown, Reason


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

def select(t, assumptions):
    """分段函数在 assumptions 下取值——有序首中（if/elif/else）：第一个可证成立的条件。

    自顶向下扫：可证假的支跳过；可证真的支，若其前无非假支（首中）则定值。
    每点至多落一支 → 取值唯一，无求值层冲突。`c=⊤` 为"否则"支。

    返回 (状态, 载荷)：
    · ("value", v)          唯一命中；或所有支可证不成立 → v = Undefined
    · ("residual", (pw, r)) 有更早的支条件未决，遮蔽关系待定；pw 为残段，
                            r 为该次判定的未决理由
    """
    bs = branches(t)
    survivors = []              # 首中未定前需保留的更靠后候选
    first_unknown = None
    for v, c in bs:
        if c is T.TRUE:
            if not survivors:                   # 否则支，且其前皆已判假 → 命中
                return ("value", v)
            survivors.append((v, c))            # 其前有未决支，遮蔽待定 → 残段
            break
        verdict = decide(c, assumptions)
        if verdict is NO:
            continue                            # 此支不成立，看下一支
        if verdict is YES:
            if not survivors:                   # 首个真支且其前皆假 → 命中
                return ("value", v)
            survivors.append((v, c))
            continue
        if first_unknown is None:               # 未决支：可能成立，遮蔽后续
            first_unknown = verdict.reason
        survivors.append((v, c))
    if not survivors:
        return ("value", T.SP("Undefined"))     # 全支可证不成立：此点无定义
    return ("residual", (piecewise(survivors),
                         first_unknown or Reason.FRAGMENT))


def coverage(t, assumptions):
    """分支条件之析取是否覆盖全空间（完全性是使用者声明，此处可判则判）。

    YES 完全覆盖；NO 存在可证空隙（所有条件皆假的地方无定义）；
    Unknown(GUARDED) 有条件未决，覆盖随之未决。"""
    conds = conditions(t)
    guarded = False
    for c in conds:
        if c is T.TRUE:
            return YES
        v = decide(c, assumptions)
        if v is YES:
            return YES
        if v is NO:
            continue
        guarded = True
    return unknown(Reason.GUARDED) if guarded else NO


def collapse(t, assumptions):
    """点塌缩：把项中每个 Piecewise 子项替换为其在 assumptions 下的选支值。

    数值点回代判定的公共通道——条件在 assumptions 下可判时，每个分段按有序
    首中塌缩为单一支值，逐层外推后整项成为普通项，可走域判零/求值。
    任一分段选支未决（条件判不动）则整体 None（诚实未决，不猜测）。

    分段可出现在运算的任意深度（如 `pw(...) + 2`）；条件位置出现
    分段是病态结构（fold_nested 已拒），此处不会遇到。"""
    if is_piecewise(t):
        status, load = select(t, assumptions)
        if status != "value":
            return None                        # 选支未决：遮蔽关系定不了
        return collapse(load, assumptions)             # 支值仍含分段则继续塌缩
    if not isinstance(t, Expr) or not t.args:
        return t
    new_args = []
    changed = False
    for a in t.args:
        na = collapse(a, assumptions)
        if na is None:
            return None
        changed = changed or (na is not a)
        new_args.append(na)
    return T.mk(t.head, tuple(new_args)) if changed else t


def conflicts(t, assumptions):
    """顺序无关性 lint（非求值闸）：交叠处值不等 → 该点取值依赖声明顺序。

    求值走 `select` 的有序首中，永不歧义。本函数是**作者体检**：若两支区域
    可同时成立（`ci ∧ cj` 可满足）而值不等，则调换声明顺序会改变该处结果——
    提示作者把守卫写成互斥。返回 [(i, j, Verdict)]，Verdict 是"此重叠良定义
    （顺序无关）"的判定：
    · YES 空重叠，或重叠处值恒等
    · NO  重叠可满足且两值不等——顺序敏感，作者应收紧守卫
    · Unknown 判定力所不及（GUARDED/FRAGMENT/UNDECIDABLE/BUDGET）

    判不动绝不伪装成一致。"""
    from cas.math.decide import satisfiable
    bs = branches(t)
    out = []
    n = len(bs)
    for i in range(n):
        vi, ci = bs[i]
        for j in range(i + 1, n):
            vj, cj = bs[j]
            sat = satisfiable([ci, cj], assumptions)      # 重叠区是否可满足
            if sat is NO:
                out.append((i, j, YES))            # 空重叠，天然顺序无关
                continue
            out.append((i, j, _agree(vi, vj, (ci, cj), assumptions)))
    return out


def _agree(vi, vj, conds, assumptions):
    """两值在重叠条件 conds 下是否相等：临时**扩充**假设集后判等。

    假设集不可变，所以这里是 `extended`（产生新对象）而非就地写入——
    重叠区分析不该污染调用方的假设。
    """
    if vi is vj:
        return YES
    tmp = assumptions.extended(*[c for c in conds if c is not T.TRUE])
    from cas.math.decide import equivalent
    return equivalent(vi, vj, tmp)


# ---------------------------------------------------------------------------
# 逐分支运算提升
# ---------------------------------------------------------------------------

def lift(op, *terms):
    """把 n 元运算 op 逐分支提升到 Piecewise 参数上（笛卡尔展开）。

    语义依据：分段函数参与运算按点定义——`(f⊕g)(x) = f(x)⊕g(x)`。故每个
    (p-支, q-支…) 组合产出一新支，值取 op(各支值)，条件取各支条件的合取；
    合取可证恒假的组合（两支不能同时成立）天然空重叠，直接丢弃。
    op 接收驻留项返回驻留项（如 T.plus / T.times）。非 Piecewise 参数视作
    恒真单分支。结果按 `piecewise` 规范化。"""
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
        if conj is T.FALSE:                 # 空组合：条件不能同时成立
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


# ---------------------------------------------------------------------------
# 嵌套展平 + 域提取（消费 cas/cad 胞腔，分段求导/积分/解方程的前置）
# ---------------------------------------------------------------------------

from dataclasses import dataclass          # noqa: E402
from cas.errors import PiecewiseError       # noqa: E402
from cas.math.decide import decide          # noqa: E402
from cas.math.cad import resolve_partition       # noqa: E402

_UNDEF = T.SP("Undefined")


def _conj(a, b):
    if a is T.FALSE or b is T.FALSE:
        return T.FALSE
    if a is T.TRUE:
        return b
    if b is T.TRUE:
        return a
    return T.and_(a, b)


def fold_nested(t):
    """嵌套分段展平为单层：值是分段的，用合取分配进外层条件。

    `pw(pw(a,ca,b,cb), c) → pw(a, ca∧c, b, cb∧c)`。结构重写，非特判；
    展平后一切算法只面对单层分区。条件位置出现分段是病态结构，拒答。"""
    if not is_piecewise(t):
        return t
    pairs = []
    for v, c in branches(t):
        if is_piecewise(c):
            raise PiecewiseError("条件位置不允许分段值")
        fv = fold_nested(v)
        if is_piecewise(fv):
            for iv, ic in branches(fv):
                pairs.append((iv, _conj(ic, c)))
        else:
            pairs.append((fv, c))
    return piecewise(pairs)


def domain_cells(t, x):
    """分段函数关于 x 的定义域胞腔分解。

    返回 [(Cell, 值|Undefined)]：每个胞腔上按有序首中取第一个条件成立的
    分支值；无条件成立则为 Undefined（该胞腔不在定义域内）。条件含超越/
    多变量分区时透传 cad.CadError（UNDECIDABLE / FRAGMENT）。"""
    t = fold_nested(t)
    bs = branches(t)
    conds = [c for _v, c in bs]
    out = []
    for cell, labels in resolve_partition(conds, x):
        val = _UNDEF
        for (v, _c), holds in zip(bs, labels):
            if holds:
                val = v
                break
        out.append((cell, val))
    return out


@dataclass(frozen=True, slots=True)
class Component:
    """定义域的一个连通分量。

    cells：分量内的 (Cell, 值) 序列；
    lo / hi：下/上界根的隔离区间，None 为无界；
    lo_closed / hi_closed：对应端点是否包含（开区间端点不含，点胞腔含）。"""
    cells: tuple
    lo: object
    lo_closed: bool
    hi: object
    hi_closed: bool


def _mk_component(run):
    first_cell = run[0][0]
    last_cell = run[-1][0]
    if first_cell.kind == "point":
        lo, lo_closed = first_cell.iso, True
    else:
        lo, lo_closed = first_cell.lo, False      # 开胞腔左端不含；None 为 −∞
    if last_cell.kind == "point":
        hi, hi_closed = last_cell.iso, True
    else:
        hi, hi_closed = last_cell.hi, False       # 开胞腔右端不含；None 为 +∞
    return Component(tuple(run), lo, lo_closed, hi, hi_closed)


def connected_components(domain):
    """把 `domain_cells` 的已定义胞腔并成极大连通分量。

    未定义胞腔（Undefined）切断连通性——不定积分独立常数、定积分分段
    求和都以连通分量为单位，绝不把缺口两侧的分支当作一体。"""
    comps = []
    run = []
    for cell, val in domain:
        if val is _UNDEF:
            if run:
                comps.append(_mk_component(run))
                run = []
        else:
            run.append((cell, val))
    if run:
        comps.append(_mk_component(run))
    return comps

