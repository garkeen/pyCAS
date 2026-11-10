# pyCAS

pyCAS 是一个纯符号、验证优先的通用计算机代数系统，使用 Python 实现，运行时零第三方依赖。

系统把一次计算拆成固定问题、候选结果和独立核验三个环节。每个结果都附带：

- 成立区域、参数范围或分支条件；
- 支撑它的关系、证书或独立 checker；
- 它在答案集合中的覆盖范围；
- 尚未处理的情形及其原因。

精确符号计算是默认路径。超出当前能力片段时，系统返回结构化的未决或拒答信息。

## 目标

### 三项地基目标

1. **完整 Risch**：参数积分与超越数积分，参照 FriCAS；
2. **完整 Gröbner 基**：多元多项式理想论，包括属员、方程组与消元；
3. **完整 CAD**：多变量实代数投影、胞腔分解与量化消去。

### 同时建设

- 参数与系数正交的有效结构；
- 分段函数、定积分与区域化微积分；
- 可判定的 ODE 子类；
- 完整的手动与自动工作簿；
- 持久化、重放与可恢复的交互历史。

ODE/PDE 与离散方向按 `cas_v5_arch.md` §25、§30.15 分解。一般非线性、PDE 与丢番图问题按能力边界处理。代数函数 Risch 的函数域、整基、局部信息与除子等几何/算术依赖保留在架构 §30.13。

## 总体架构

### 三个计算平面

| 平面 | 职责 |
|---|---|
| 数学计算 | 已绑定 parent 的元素、矩阵、理想、塔、胞腔；执行精确算法 |
| 数学核验 | 问题、候选、区域、证书；独立重建被证明的关系 |
| 交互编排 | 对象版本、任务、动作、假设、策略、历史 |

### 数据流

```text
文本/对象 + 语义 frame + 用户意图
  → 解析、绑定、定型、定义展开
  → 固定 ProblemSpec + AlgebraRequest
  → 有效代数表示中的候选计算
  → 独立 checker 验证确切规格
  → kernel 原子发行 Judgment/InferenceRecord
  → 工作流对象、条件、来源与 revision 历史
```

### 分层

| 路径 | 职责 |
|---|---|
| `cas/foundation/` | 互不混用的身份类型与 issuer |
| `cas/syntax/` | 不可变 Term、结构相等/hash/序、de Bruijn 绑定、出现位置与捕获规避替换 |
| `cas/language/` | Sort、结构签名、定型、Proposition、ProblemSpec、未决理由、声明 DSL |
| `cas/algebra/` | 有效结构、parent、精确代数算法；与 Term/frame/kernel 解耦 |
| `cas/semantics/` | World/Frame、符号表、定义展开、请求角色、参数与特化、条件与区域、Term↔代数元素桥 |
| `cas/kernel/` | Judgment/Obligation/InferenceRecord、checker 注册、一致性、原子账本与单批 commit |
| `cas/operations/` | 开放操作协议、ProblemSpec/Proposal/CheckerBinding 注册 |
| `cas/math/` | 数学声明、候选服务、独立 checker、操作实现 |
| `cas/workflow/` | 对象、候选、任务、验证关联、事件、revision、手动交互与历史 |
| `cas/runtime/` | 显式装配与 workspace 入口 |
| `cas/frontend/` | parser、printer、session、REPL |

依赖方向以 `cas_v5_arch.md` §3 为准。`semantics` 负责桥接，`math` 提供操作与 checker，`workflow` 消费公共协议，`runtime` 负责装配，`kernel` 按公共协议处理判断与提交。装配集中在 `runtime/bootstrap.py`，import 期不修改全局状态。

### 关键对象

| 对象 | 含义 |
|---|---|
| `Term` | 中性语法树 |
| `Parent` | 明确的有效代数结构；域成员、判等和算法能力由它提供 |
| `Proposition` | 已定型、绑定合法并带有意义 frame 的公式 |
| `ProblemSpec` | 固定的输入、目标、区域、结果语言、参数承诺与覆盖要求 |
| `Judgment` | kernel 已发行的可信命题，附带来源与义务 |
| `Candidate` | 尚未获得信任的提议答案 |
| `Revision` | 工作簿可见对象、关系、任务与历史的不可变快照 |

### 设计原则

- **纯符号**：计算在明确的代数结构中进行，结论由符号算法给出。
- **计算与验证分离**：搜索器产生候选，独立 checker 验证确切规格，kernel 原子发行 Judgment/InferenceRecord。
- **按能力分派**：parent 的能力决定可用算法和判等；分派依据是能力，不依赖 Python 类型、节点名字或形状。
- **对象与关系分离**：`Term` 只是语法树；`HasDerivative` 等是关系。对关系右侧再求导不会自动扩大既有关系。
- **区域分离**：固有定义域、表示有效区域、关系核验区域、正则性区域、原问题目标区域分别保存。
- **相等分离**：结构相等、域内相等、当前取值相等、区域上函数相等、偏函数相等、问题等价分别判定。
- **三值判定**：对外命题判定为 Yes/No/Unknown；`No` 必带证据，`Unknown` 只使用 FRAGMENT / GUARDED / UNDECIDABLE / BUDGET 四类理由。
- **数学语义数据化**：常数、函数、规则、导数模板、定义域条件只以数据 + 显式装配存在；内核按声明处理语义。
- **单一实现**：同一概念只有一个模块、一个声明 DSL、一个证书 schema、一条 discharge 路径。
- **失败边界显式**：能力必须声明输入表示、所需能力、终止依据和完整性范围；未决状态会明确返回。

## 文档职责

| 文档 | 职责 |
|---|---|
| `README.md` | 项目定位、目标与总体架构 |
| `AGENTS.md` | 项目定位、代码风格、语义要求、实现纪律，以及当前进度与缺陷的唯一权威 |
| `roadmap.md` | 从当前代码到终态的施工路线、阶段依赖与交付条件 |
| `cas_v5_arch.md` | 对象模型、数学语义、有效表示、核验边界、数据流与终态契约 |
| `reference.md` | 参考项目、算法来源与源码路径索引 |
| `progress.log` | 已完成的施工、验收与经验教训记录 |
| `risch.md` / `cad.md` / `maple.md` / `mathematica.md` | 研究笔记与工具清单 |

当前可用的数学能力、片段边界、未实现项与已知缺陷，以 `AGENTS.md` 第五节为准。

## 入口

```console
$ python repl.py
```

程序化装配从 `cas.runtime` 开始；工作区与前端入口分别位于 `cas.workflow` 与 `cas.frontend`。具体命令、当前片段和限制以 `AGENTS.md` 与 REPL 的 `help` 为准。

## 运行时与开发依赖

- 运行时：Python >= 3.11，零第三方依赖。
- 开发/验收工具：`pytest`、`mypy`、`ruff` 等，不属于运行时依赖。
- 验收命令与实现纪律见 `AGENTS.md` §4.1。
