# cad.md — 完整 CAD 所需地基的执行报告

本文件回答一个问题：**为了完成完整 CAD，pyCAS 必须实现哪些地基。**

与 `risch.md` 同一界分：这里只列**工具**（可独立实现、可独立测试、被 CAD 消费的可复用模块），CAD 主循环自身内联的逻辑**不算**工具（界分见 §0）。本文件**不含计划、阶段划分、优先级与顺序裁定**。

主要取证对象是 **REDUCE / REDLOG**（作者 A. Dolzmann、A. Seidl、T. Sturm、M. Kosta），它被公认为 CAD 实现最完整的参考之一：`packages/redlog/ofsf/ofsfcad.red` 是其 CAD 主循环，由 Dolzmann / Seidl / Sturm 于 2000–2017 年持续实现，含 Collins / Hong / McCallum 多种投影算子与符号不变性支持。

使用时遵守 `reference.md` 的既有纪律：**抄语义不抄代码**；本系统裁定（`cas_v4_arch.md` + `AGENTS.md`）高于参考实现行为。参考实现自身的缺口如实记录在 §16。


报告只列**工具**（可独立实现、可独立测试、被 CAD 消费的可复用模块），CAD 主循环自身内联的逻辑**不算**工具（界分见 §0）。本文件**不含计划、阶段划分、优先级与顺序裁定**。
---

## §0 界分：什么算工具，什么不算

**不算工具（属于 CAD 主循环本体）：**

- 逐层下降的循环：第 r 层投影 → 构造第 j 层胞腔 → 逐层递归到叶
- 投影相 / 延拓相 / 收尾相三段的调用顺序
- partial tree 与 full tree 两种模式的分支
- 提前求值（trial evaluation）的插入位置
- truth 值从叶向上传播的规则
- 「本层全为白胞腔则该子树已完成」的剪枝判断

**算工具（必须独立成模块）：** 下列 §1–§14 各项。

---

## §1 逻辑与量化层

| 工具 | 功能 | 参考路径 |
|---|---|---|
| 公式规范形 | 原子化、否定内移、析取合取范式、量词作用域规范 | Reduce `packages/redlog/rl/redlog.red`；`packages/redlog/cl/clnf.red`（Common logic normal forms） |
| 范式前缀 | 把公式化为「量词前缀 + 无量词公式」，并抽出约束变量表 | 同上 |
| 变量/量词抽象 | 约束变量与自由变量的区分、变量重命名、局部变量作用域 | 同上 |
| 布尔合取分解 | 公式拆成约束的合取（CAD 按合取项分别投影） | Reduce `packages/redlog/ofsf/ofsfqe.red` |
| 子句化 | 转为子句形式（阳性服务 `cl` 层的入口） | Reduce `packages/redlog/rl/rlservices.red` |
| 变量顺序与变量选择 | 投影顺序的选择、等价类内的变量选择、维数约减 | Reduce `packages/redlog/ofsf/ofsfqe.red`（变量选择与约减族） |

## §2 有序域标准形层

| 工具 | 功能 | 参考路径 |
|---|---|---|
| 标准形表示 | 有序域上的元素标准化：加法/乘法/幂的规范排列，变系数与变参数化处理 | Reduce `packages/redlog/ofsf/ofsf.red`；`packages/redlog/rltools/sfto.red` |
| 分式运算 | 标准形上的加乘除与约分 | 同上 |
| 整系数化 | 清除分母、去除内容与首一化 | 同上 |
| 代数系数的表示与运算 | 系数取在代数扩张上的标准形（REDLOG 特有） | Reduce `packages/redlog/ofsf/ofsfexfr.red`（代数点、代数扩张、跨度的构造与运算，约 109 个过程） |
| 公式 ↔ 标准形的双向转换 | 把逻辑原子转成标准形算术式 | 同上 |

## §3 投影算子

| 工具 | 功能 | 参考路径 |
|---|---|---|
| 系数子结式 | 取各系数（及其导数、幂）的子结式 | Reduce `packages/redlog/ofsf/ofsfqe.red`（`ofsf_qesubcr*` 族）；`packages/redlog/rltools/sftoresultant.red`（标准形子结式） |
| 表达式子结式 | 取两个表达式的子结式 | 同上（`ofsf_qesubrat` 族） |
| 判别式 | 取表达式的判别式 | 同上（`ofsf_qesubreq` 族） |
| 无平方投影 | 把投影多项式集无平方化并取不可约部分 | 同上；投影因子的两两互素归一见 `ofsfcad.red`（`aex_tgpairwiseprime`） |
| 定向良好投影（McCallum） | 只投影到定向良好子集：单调性、约束多项式、零维位置的判定 | Reduce `packages/redlog/ofsf/ofsfcad.red`（McCallum 投影开关默认开启） |
| Hong 投影 | 带不可约性条件的投影 | 同上 |
| 符号不变性支持 | 额外投影「在胞腔上不变」的符号恒真的多项式 | Reduce `packages/redlog/ofsf/ofsfgs.red`（标准形 Gröbner 化简器，约 34 个过程）；`packages/redlog/ofsf/ofsftfc.red`（Type Formula Construction，约 36 个过程） |
| 投影集归一 | 内容、首一、去重、排序、可约性标记 | Reduce `packages/redlog/ofsf/ofsfcad.red` |
| 投影数目估计 | 估计各层投影因子个数、树节点数 | 同上（部分树 / 满树节点计数） |

## §4 实根隔离与代数数

| 工具 | 功能 | 参考路径 |
|---|---|---|
| 一元实根隔离 | 把实根表示为「不可约因子 + 隔离区间」，区间内无其它根且不含有理根 | Reduce `packages/redlog/ofsf/ofsfdpep.red`（区间隔离与精化，约 56 个过程）；`packages/redlog/ofsf/ofsfexfr.red`（代数数/代数点的构造） |
| 区间精化 | 按需收窄隔离区间 | 同上 |
| 符号判定（样本点上） | 判定多项式/标准形在样本点处的符号 | 同上（符号代入与签名族）；样本点签名见 `ofsfcad.red` |
| 有理根分离 | 把有理根从无理根中剥离 | 同上 |
| Cauchy 界与根的分离性检查 | 隔离正确性的自检 | pyCAS 已有：`cas/math/realroot.py`（Cauchy 界） |

## §5 胞腔与样本点

| 工具 | 功能 | 参考路径 |
|---|---|---|
| 胞腔数据结构 | 索引、样本点、真值、描述、标签（`Acell`） | Reduce `packages/redlog/ofsf/ofsfcad.red` |
| 样本点构造 | 给定低维胞腔与本层投影根，构造高维胞腔与样本点 | 同上（扇区构造与右界搜索族） |
| 扇区与相邻关系 | 一维上由投影根切分出的扇区序列；点胞腔索引为奇数、扇区为偶数 | 同上 |
| 样本点数据传递 | 隔离区间信息在层间的继承与更新 | 同上 |
| 胞腔树 | 树的构造、子节点设置、按层取子节点、叶集合、深度 | 同上（`Atree` 族） |
| 白胞腔判定 | 判定一个胞腔是否「全维」（CAD 剪枝与 truth 求值的前提） | 同上 |
| 树的裁剪 | 删除假叶、只保留有效子树 | 同上 |
| 树的输出 | CAD 树导出为图格式（可视化） | 同上（dot / tgf / gml 导出） |

## §6 真值求值

| 工具 | 功能 | 参考路径 |
|---|---|---|
| 无量词公式求值 | 在给定样本点处求一个无量词公式的真值 | Reduce `packages/redlog/ofsf/ofsfcad.red` |
| 符号代入 | 把表达式中的代数数替换为其在样本点处的符号 | 同上 |
| 签名 | 由原子公式的符号构造样本点的签名，用于去重 | 同上 |
| 提前求值 | 逐点代入，若结论已定则提前结束 | 同上 |
| 不可判定时的位置追踪 | 若代入失败，说明是哪个原子、哪个根序导致的 | 同上 |

## §7 量词消去与解公式

| 工具 | 功能 | 参考路径 |
|---|---|---|
| 量词消去驱动 | 把带量词公式化为无量词公式 | Reduce `packages/redlog/ofsf/ofsfqe.red`（约 175 个过程） |
| 局部量词消去 | 对变量序中一段连续量词作局部消去 | 同上 |
| **解公式** | 把 CAD 上的解集压成**不含 CAD** 的公式（CAD 只作为中间步骤） | Reduce `packages/redlog/ofsf/ofsfcad.red`（solution formula 构造族） |
| 真值定理 | 产出「某组不等式 蕴含 原公式」的形式化陈述 | 同上（收尾相） |
| 复杂度递减估计 | 估计消去后的判定难度 | Reduce `packages/redlog/ofsf/ofsfdecdeg.red` |
| 公式化简（最终态） | 用解公式与真值定理化简原公式 | Reduce `packages/redlog/cl/clsimpl.red`（`cl_simpl` 族） |

## §8 多项式代数（投影算子依赖）

| 工具 | 功能 | 参考路径 |
|---|---|---|
| 一元 / 多元 gcd | 投影因子两两互素化的底座 | Reduce `packages/groebner/groebner.rlg`；pyCAS 部分已有：`cas/math/domains/poly.py`（一元 gcd） |
| 无平方分解 | 投影算子的强制步骤 | pyCAS 已有：`cas/math/domains/polytools.py`（一元无平方） |
| 子结式 | 投影算子的核心 | pyCAS 已有：`cas/math/domains/polytools.py`（一元结式） |
| 因式分解 | 定向良好投影的不可约性判定、投影因子归一 | Reduce `packages/factor/factor.rlg`；pyCAS **未建** |
| Gröbner 基 | 符号不变性投影需要 | Reduce `packages/groebner/groebner.rlg`（约 30 KB）；pyCAS **未建** |
| 判别式 | 投影算子 | Reduce `packages/algint/algint.rlg`；pyCAS **未建** |
| 多元多项式运算 | 投影算子工作在多元 | pyCAS **未建** |
| 有理数运算 | 全部投影的底座 | pyCAS 已有：`cas/math/domains/q.py` |

## §9 实代数

| 工具 | 功能 | 参考路径 |
|---|---|---|
| 实代数数算术 | 精确表示实代数数并判零、比较 | Reduce `packages/redlog/ofsf/ofsfexfr.red`；pyCAS 部分已有：`cas/math/realroot.py` |
| 区间算术 | 隔离区间上的包含关系 | Reduce `packages/redlog/ofsf/ofsfdpep.red`；pyCAS **未建** |
| 符号不变量的区间判定 | 判定某多项式在胞腔上恒正/恒负/恒零 | 同上；pyCAS **未建** |

## §10 表达式工具

| 工具 | 功能 | 参考路径 |
|---|---|---|
| 符号表达式因式分解 | 把用户式子拆成标准因子 | Reduce `packages/factor/factor.rlg` |
| 代数扩张上的表达式运算 | 投影算子在系数为代数数时的运算 | Reduce `packages/redlog/ofsf/ofsfexfr.red` |
| 整系数替换 | 去掉自由参数与分母 | Reduce `packages/redlog/ofsf/ofsfqe.red` |

## §11 结果表示与输出

| 工具 | 功能 | 参考路径 |
|---|---|---|
| CAD 数据的存取 | 一个结构体承载公式、投影序、投影因子、树、真值、定理 | Reduce `packages/redlog/ofsf/ofsfcad.red`（数据记录族） |
| 解集表示 | 区间 / 点 / 代数点 / 解析式的统一表示 | 同上（sample point 表示） |
| 树的持久化与重放 | 把 CAD 结果存下来复现 | Reduce `packages/redlog/ofsf/ofsfcad.red`（树导出） |
| 哈希表 | 样本点去重、公式去重的容器 | Reduce `packages/redlog/rltools/bhashtable.red` |
| 列表工具 | 树与投影集的列表运算 | Reduce `packages/redlog/rltools/lto.red` |

## §12 覆盖范围（决定「完整」到什么程度）

| 工具 | 功能 | 参考路径 |
|---|---|---|
| 仅判定（QE） | 判定一个实闭域公式的真假 | Reduce `packages/redlog/ofsf/ofsfqe.red` |
| 解公式 | 给出解集的显式公式 | Reduce `packages/redlog/ofsf/ofsfcad.red` |
| 区间闭包 | 求解集在给定区间上的近似 | Reduce `packages/redlog/ofsf/ofsfqe.red` |
| 投影集本身 | 只输出投影多项式 | 同上 |
| 部分 CAD | 只构造到指定层 | 同上 |
| 量词消去次数估计 | 估计消去所需层数 | 同上 |
| 符号不变性 | 在不定次数/不定系数下给出真值定理 | Reduce `packages/redlog/ofsf/ofsfgs.red`、`ofsftfc.red` |
| 与外部求解器对接 | 把难点交给 QEPCAD 等 | Reduce `packages/redlog/ofsf/qepcad.red` |

## §13 参考实现的额外发现（对 pyCAS 的意义）

Reduce 的 CAD 建立在**两个自有的、多项式之上的抽象层**之上，而不是直接建立在裸多项式之上：

1. **有序域标准形（OFSF）层**——`ofsf.red` + `rltools/sfto.red`。CAD 算子全程在标准形上运算。好处是「投影因子」「系数」「表达式」都有统一的、可比较的表示，符号判定与签名因此可做。
2. **代数扩张层**——`ofsfexfr.red`（约 29 KB，109 个过程）。投影算子需要把表达式当代数系数来运算（子结式、判别式在代数系数下仍需精确）。

这两层是「CAD 做成」与「CAD 写成裸多项式」的主要差别所在，也是 pyCAS 移植时最容易漏掉的部分。

---

## §14 pyCAS 现状与缺口

**已有（可复用）**：

- 一元实根隔离：Sturm 链、符号变化、开区间根计数、Cauchy 界、隔离区间精化、有理根、无平方分解 —— `cas/math/realroot.py`
- 一元结式、无平方分解 —— `cas/math/domains/polytools.py`
- 一元 gcd —— `cas/math/domains/poly.py`
- 一维 CAD：抽取边界多项式、按根切分胞腔、符号在胞腔上求值、量化消去 —— `cas/math/cad.py`
- 域能力字段与投影阶梯 —— `cas/math/project.py`

**完全未建（按 §1–§12 对照）**：

- 多元多项式运算（投影算子工作在多元）—— §8
- 因式分解、Gröbner 基、判别式 —— §8
- 区间算术、符号不变量区间判定 —— §9
- 有序域标准形层 / 代数扩张层 —— §2
- 投影算子（Collins / Hong / McCallum 全部）—— §3
- 高维胞腔构造、扇区、胞腔树 —— §5
- 样本点上的符号判定与签名 —— §4、§6
- 解公式构造 —— §7
- 量词消去驱动（多变量）—— §7

**结论**：pyCAS 现有的是「一维 CAD + 一元实根隔离」，即 CAD 的**最底层一格**。完整 CAD 需要在此之上补齐 §1–§12 全部条目，其中 §2（标准形层）、§3（投影算子）、§5（胞腔构造）、§7（解公式）是四块从未有过的新结构。

---

## §15 参考源码位置

| 库 | 版本 / 位置 | 说明 |
|---|---|---|
| **REDUCE / REDLOG** | `D:\code\python\CAS\reduce-algebra` | CAD 核心在 `packages/redlog/ofsf/`（`ofsfcad.red` 69 KB、`ofsfqe.red` 125 KB、`ofsfdpep.red` 54 KB、`ofsfexfr.red` 29 KB、`ofsfgs.red` 23 KB、`ofsftfc.red` 21 KB）；底座在 `packages/redlog/rltools/`（`sfto.red` 45 KB、`lto.red` 40 KB、`sftoresultant.red` 19 KB）；作者 A. Dolzmann、A. Seidl、T. Sturm、M. Kosta |
| **FriCAS** | `D:\code\python\CAS\fricas\src\algebra` | CAD 相关：`cyldec.spad`（柱状代数分解）、`reclos.spad`（实闭域）、`realzero.spad`（实零点）、`sign.spad`（符号） |
| **Maxima** | `D:\code\python\CAS\maxima\src` | CAD 相关：`realroot`-类操作在 `poly*.lisp` 与 `lim*.lisp` |

---

## §16 参考实现自身的缺口（如实记录，不得当作已实现）

- **REDLOG 的 CAD 是「有序域标准形」上的 CAD**：其投影算子、代数扩张、代数数表示均依赖 OFSF 抽象层，移植到裸多项式层不是简单替换。
- **符号不变性路径**（`ofsfgs.red` 的 Gröbner 化简器 + `ofsftfc.red` 的 Type Formula Construction）依赖 Gröbner 基；REDUCE 的 Gröbner 包（`packages/groebner/groebner.rlg`）能力有限，不等于完整 Gröbner 机器。
- **REDLOG 另有两层实代数实现在别处**（`acfsf`/`talp`/`ibalp`/`tplp`），本文档只取证了 `ofsf` 层；移植前需确认目标层。
- **FriCAS 的 CAD 是胞腔分解包**（`cyldec.spad`），与 REDLOG 的 OFSF 路线不同；其投影算子细节需另行取证。
- **Maxima 无完整 CAD**（其 `realroot` 类能力分散在 `poly*.lisp`、`lim*.lisp`），不足以作 CAD 的语义权威。

---

## §17 与本文件边界相邻的问题（尚未裁定，本文件不代为决定）

- 是否移植 OFSF 标准形层，还是直接在 pyCAS 的域协议（能力字段）上做投影算子。
- 是否需要符号不变性路径（依赖 Gröbner 基），还是只做 Collins / Hong / McCallum 三种投影。
- 「完整 CAD」是否包含解公式（不含 CAD 的解集公式），还是只要量化消去判定。
- 「完整 CAD」是否包含实代数输入（参数带代数数），还是只支持有理系数。
- pyCAS 现有的一维 CAD 是否保留为独立地基，还是并入通用胞腔构造。

以上五项在裁定前，`progress.md` 不得把它们记为已实现，`cas_v4_arch.md` §十一 第六阶段不得把它们记为已规划。
