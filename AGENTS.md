# AGENTS.md — pyCAS v5 项目定位、工程纪律与当前状态

## 一、这是什么项目

pyCAS 是一个**纯符号、验证优先的通用计算机代数系统**，Python 实现，运行时零第三方依赖。

它不是“算出一个表达式就返回”的计算器，也不是靠数值采样、形状猜测或化简器碰运气给出答案的系统。每次计算都走同一条管线：

```text
文本/对象 + 语义 frame + 用户意图
  → 解析、绑定、定型、定义展开
  → 固定 ProblemSpec + AlgebraRequest
  → 有效代数表示中的候选计算
  → 独立 checker 验证确切规格
  → kernel 原子发行 Judgment/InferenceRecord
  → 工作流对象、条件、来源与 revision 历史
```

项目有三个计算平面：

| 平面 | 职责 |
|---|---|
| 数学计算 | 已绑定 parent 的元素、矩阵、理想、塔、胞腔；执行精确算法 |
| 数学核验 | 问题、候选、区域、证书；独立重建被证明的关系 |
| 交互编排 | 对象版本、任务、动作、假设、策略、历史 |

目标是做一个**能清楚说明每个结果在什么范围、什么条件下、依据什么成立**的 CAS，而不是只追求“能算很多题”。

文档职责都很重要，不能互相替代：

- `cas_v5_arch.md`：**具体如何实现**。它规定对象模型、数学语义、有效表示、核验边界、数据流和终态契约；写代码前先读对应章节。
- `roadmap.md`：**按什么路线实现**。它规定从当前代码到终态的施工顺序、能力图、阶段依赖、每批交付条件和并行关系；不记录当前进度或缺陷。
- `reference.md`：**有什么可以参考**。它索引可对照的参考项目、算法来源和源码路径（Maxima、FriCAS、REDUCE/REDLOG 等）；参考行为不是本项目的证明。
- `progress.log`：**日后审查与经验教训**。它只追加已完成、已验收的施工记录，写明做了什么、依据是什么、验收结果和值得保留的教训；不记录计划、未完成项或当前缺陷。
- `AGENTS.md`（本文件）：**项目定位、目标、代码风格、语义要求、实现纪律，以及当前进度与缺陷**。它是当前状态的唯一权威。
- `README.md`：项目定位、目标与总体架构；不记录当前进度、缺陷或施工路线，也不替代上述任何一份权威文档。当前状态只在 `AGENTS.md` 第五节维护；每次提交必须同批更新 `AGENTS.md`，README 不得复制状态。
- `risch.md` / `cad.md` / `maple.md` / `mathematica.md`：研究笔记与工具清单，不作为当前状态或路线来源。

## 二、目标

### 2.1 终极目标

三项地基目标，每项都有已知终极形态：

1. **完整 Risch**（参数积分与超越数积分，参照 FriCAS）；
2. **完整 Gröbner 基**（多元多项式理想论：属员、方程组、消元、代数预处理）；
3. **完整 CAD**（多变量实代数投影 + 胞腔分解 + 量化消去）。

同时建设参数与系数正交、分段函数与定积分、可判定 ODE 子类、完整手动/自动工作簿、持久化与重放。ODE/PDE 与离散方向按架构 §25、§30.15 分解；一般非线性/PDE/丢番图问题不虚构总算法。代数函数 Risch 的几何/算术依赖保留在 §30.13，不从最终目标删除。

### 2.2 实施原则

- **彻底重构，不是迁移。** 不保留兼容层，不保留双 API，不为旧调用改写新语义。
- **完整设计不得缩目标。** 分期实施不等于把系统改为最低可用产品；“不建空代码”不等于“不设计未来能力”。
- 架构 §30 维护通向完整 CAS 的能力图，§32 维护贯通数据流；未完成的目标不能用删文档、缩范围或一句“以后研究”消失。
- 节奏：先让一条纵线完整贯通（表达式 → 问题 → 候选 → 规格 → 验证 → 发行 → 历史），再沿完整依赖图横向生长。

## 三、代码风格与语义要求

### 3.1 依赖方向

- `workflow` 不导入具体 math 实现；`runtime` 只装配；`kernel` 不认识数学操作名。
- 域、声明、checker、操作一律经显式 builder 装配并冻结；import 期不修改全局状态。
- 测试不写在源码目录。依赖方向以架构 §3 为准。

### 3.2 对象与关系

- **Term 与代数元素分离**：Term 只是语法树，不带类型、定义域或证明；计算在显式 `Parent` 元素上进行，两者通过 bridge 转换。
- **对象与关系分离**：`x^2` 是中性表达式；`HasDerivative(U, f, x, g)` 是关系。对 `g` 再求导不会自动扩大它与 `f` 的既有关系。
- **五种区域分开**：固有定义域、表示有效区域、关系核验区域、正则性区域、原问题目标区域。不能用一个混合 `region` 字段装下。
- **六种相等分开**：结构相等、域内相等、当前取值相等、区域上函数相等、偏函数相等、问题等价。

### 3.3 数学语义数据化

常数、函数、规则、导数模板、定义域条件只以数据 + 显式装配存在（DSL 声明 + builder），禁止 Python 直注册。两类 head 必须分清：

- **数学语义 head**（如 `Sin`/`Exp`/`Log`/`Sqrt`/`Abs`）：存在与语义只能来自声明，任何模块不得写死这些名字，不得为某个具体函数加专用分支；
- **语言签名 head**（`Plus`/`Times`/`Power`、比较、逻辑连接词、`Quote`/`Piecewise` 的结构位置）：这是项语言自身的结构，算法可据其分派。

判据：**换一个函数名，这段代码要不要改。** 要改就是硬编码。数学函数语义归 `math/*`，纯表示与代数算法归 `algebra/*`；内核不认识具体数学 head。规则必须声明全部条件；有条件导数模板允许存在，应用时必须证明或显式保留条件，分支破裂者如实留痕。

### 3.4 域、判等与三值

- 按 parent 的**能力**分派，不按 Python 类型、节点名字、形状或具体 parent 类型嗅探。
- `Real` 是取值范围，不是任意实数的有效表示；转换失败不得被压成“非零”“不相等”。
- 域内 `equal`/`is_zero` 对已接受成员**完全定义**，不返回 Unknown；非成员属于桥接层越界，不是域内三值。
- 新结构先建立成员表示与完全、终止的判等；未建立判等的表达式不能冒充有效域成员。
- 对外命题判定经 Yes/No/Unknown；`No` 必带证据；`Unknown` 只用 FRAGMENT / GUARDED / UNDECIDABLE / BUDGET 四类理由；未决不得被静默当成 Yes 或 No。
- 求解器与验证器分家：checker 不得与所验证的搜索算法同住一个模块，也不得从该模块导入；`verify_*` 只做验证。

### 3.5 命名与文档

- 命名与代码组织按架构 §29.7–§29.8；名字必须描述实际数学运算，不用 `process`、`handle`、`engine` 等泛名隐藏数学。
- `normalize` 必须说明规范化的结构与不变量；`simplify` 是启发式优化，不假装唯一正规形；`is_zero` 只对可完全判零的有效成员返回 bool。
- 冻结 dataclass（`frozen=True, slots=True`）或等价封装表示不可变值；内部 dict/list 不得借只读注解泄漏可变别名。
- 判定、提交、checker 结果用封闭变体；非法状态由构造方式排除。
- 文档用中文；源码（`.py` / `.dsl`）与测试源码用英文。

## 四、实现纪律

### 4.1 红线

以下约定用于建立清楚、可验证的数学软件。接口有冲突时先修正数据模型与消费者，再提交完整的实现；新增能力同时交付真实算法、测试和准确状态。

1. **依赖先行。** 写代码前先写清：属于哪一层、允许依赖谁、谁消费它、失败状态是什么、与现有模块是否重复。没有消费者或没有失败边界的抽象不建。
2. **数学语义数据化。** 常数、函数、规则、导数模板、定义域条件只以数据 + 显式装配存在；禁止 Python 直注册；内核不认识具体数学 head。
3. **操作经注册表。** 数学操作是数据注册的 `OperationSpec`，经 `OperationRegistry` 解析。kernel、workflow、frontend 不得按 operation id、具体操作名或具体函数名写数学分支。
4. **无特判，片段诚实。** 通用算法先行，快路径只能长在通用算法之上并可证明是其子集；不得凭语法外观、具体函数名、parent 名字或“看起来是零”猜数学事实，不得只覆盖手头案例。能力必须声明输入表示、所需能力、终止依据和完整性范围；片段外诚实拒答。
5. **域按能力分派。** 按 parent 的能力分派，不按 Python 类型、节点名字、形状或具体 parent 类型嗅探；域内判等完全定义，不返回 Unknown。
6. **判等优先，代数语义直白。** 新结构先建立完全、终止的判等；优先正规形，但允许明确的精确算法。禁止数值采样、形状猜测、化简器碰运气；计算写成明确的代数运算、导子和映射，不用分析性逼近替代。
7. **单一实现，拒绝空壳。** 同一概念只有一个模块、一个声明 DSL、一个证书 schema、一个结果信封、一条 discharge 路径、一个条件判定器、一个 bootstrap 装配入口；复制粘贴第二份规则视为缺陷。独立 checker 可以独立验证，但共享的规则与证书契约必须唯一。没有真实消费者的协议、目录、字段、状态不建；已建但未接线的能力要么本批接线，要么删除。禁止 TODO、空实现、占位模块、双 API、转发层、兼容层与“保留以后用”。
8. **信任字段必须被消费。** `BasisRef` 的 world/version/digest、`CheckerSpec` 的 schema/accepted kinds、证书的实例匹配必须进入 kernel 的实际检查；没有被消费的信任字段不得存在。
9. **三值、验证器与内核边界。** 对外判定 Yes/No/Unknown；`No` 必带证据；`Unknown` 只用四类理由；`ConditionPolicy` 对 Unknown 的处置永远开启。checker 不导入被验证的搜索器；内核不遍历代码找数学 head。
10. **对象与记账。** 热循环不进账本；只有需要进入工作簿的中性产物才建 Artifact；不逐次创建对象或 Judgment；已发行判断不可覆写；历史可截断，但活跃结果依赖的证明支持必须可解析。预算只影响是否得到答案，不改变已给答案的真假；耗尽只能产出 Unknown(BUDGET)、候选或明确部分结果。`0^0`、空乘积、零因子、负幂、除以零等边界必须有显式语义或诚实拒答，不得由 Python 默认行为决定数学含义。
11. **验收与文档。** 每个修复先有回归测试；每条能力至少一对案例：**正向可用 + 越界诚实拒绝**；能随机自证的性质加固定种子性质测试。只允许类型检查、行为测试、性质测试三类验收；禁止按标识符、字符串、import 面或 AST 名字判断设计正确性。提交前跑：

    ```console
    python -m mypy --strict cas
    python -m ruff check cas tests
    python -m pytest -q
    python -m compileall -q cas
    ```

    README、roadmap 与代码同批更新，progress.log 同批追加；过期文档算债务。

**立项自检：** 函数定律等声明语义是否已数据化？算法是否覆盖宣称片段而非只覆盖手头案例？域是否按能力分派？不确定时是否诚实未决？职责是否单一？名字是否就是它做的事？任一为否，不立项。完整终态是否仍保留在设计与依赖图中，也必须检查。

### 4.2 不允许简化、特判、漏做

- **不允许简化实现。** 不得用“先这样”“暂时够用”“只处理当前案例”的局部实现冒充完整片段；不得把一般算法替换成只覆盖测试样例的分支。
- **不允许特判。** 不得按具体函数名、操作名、parent 名字、语法外观、节点形状、测试夹具或“看起来是零/一”猜数学事实。已确定结构中的零/一、次数和封闭表示变体分支是合法代数算法，不在此禁令内。
- **不允许漏做。** 已声明的输入、分支、条件、失败状态和覆盖范围必须全部实现；未实现的分支不得留在代码中伪装完成，也不得用异常、超时或“未找到”冒充数学结论。
- **不允许空壳与未接线能力。** 没有真实消费者的协议、字段、状态、目录不建；已建能力必须在本批接线，否则删除。禁止 TODO、占位模块、双 API、转发层、兼容层和“保留以后用”。
- **不允许静默降级。** 不得把 Unknown 当 Yes/No，不得把条件未决当成立，不得把“没找到”当“不存在”，不得把预算耗尽当“无解/不可积/完整解集”，不得用数值采样或近似替代符号证明。
- **每个修复先有回归。** 每条能力至少覆盖正向可用与越界诚实拒绝；能随机自证的性质加固定种子测试。测试只做行为与性质验收，不做名字/AST 门禁。
- **未完成项只写入本文件第五节。** 不得在代码、测试或文档中把未完成项写成已完成；`progress.log` 只记录已验收的完成项。

### 4.3 实现必须带参考依据

每个非平凡算法、规则、checker、域构造和优化都必须能回答“依据是什么”：

1. **数学依据**：算法名、定理、论文或教材（例如 Risch 算法、Buchberger 判据、Sturm 计数、Hong 投影）。
2. **参考实现**：对应的参考项目与文件路径（Maxima、FriCAS、REDUCE/REDLOG、SymPy 等，索引见 `reference.md`）。
3. **本项目落点**：该依据在本项目哪个模块、哪个片段、哪个证书/测试中消费。

写法要求：

- 在模块或类 docstring 中写明算法名、前提和参考来源；不要只写“实现了求导/积分”。
- 可复用的参考取证记入 `reference.md`；已完成批次的参考依据写入 `progress.log` 对应条目。
- 没有现成参考时，必须写清数学推导、适用前提和为什么可信；不得用“业界惯例”或“参考实现也这样”代替依据。
- 参考实现的行为不是本项目的证明；与架构裁定冲突时以本项目裁定为准。
- 测试必须覆盖参考算法声明的边界和失败情形；参考输出相同不构成数学证明。

### 4.4 改动流程

1. 改动前完整读将改的文件，再读 `cas_v5_arch.md` 对应章节；先画清依赖、消费者与失败边界，裁定优先于直觉与参考实现。
2. **删旧实现，不得只加不删。** 新增数学语义落到对应 `math/*`，经显式 builder 装配，不写进内核，不在 import 期改全局。
3. 新增操作走 `OperationSpec`，不改 workflow/frontend 的数学分派；热循环只传代数值/局部数据，需进入工作簿的中性产物才建 Artifact，证明与 discharge 只有一条原子发行路径。
4. 不保留 v4 用例，也不为使测试变绿恢复 v4 语义；发现旧债务时同批删除或完整接线，不以“后续处理”留在树中。
5. 文档与代码同批更新：README、roadmap、AGENTS 的当前状态与 progress.log 的完成记录必须一致。

### 4.5 已否决设计：不得回潮

- 以驻留表、对象地址或 hash 值充当结构身份；
- 把任意表达式包装成有效域（`TermField` 式伪域），或把判零的 Unknown 压成 False；
- 裸表达式、Artifact、候选答案进入可信命题槽位或作为前提；
- 把“找到一个根/一个原函数/一个解”当成必然结论或完整解集；
- 由全部自由符号自动决定计算变量或域；
- 点值等式穿过绑定体、积分、导数、`Piecewise` 或 `Quote` 而不要求函数级/区域级条件；
- 分支合并相信调用方载荷里的答案文本；
- 用未知的判零结果继续消元，或用“没找到”冒充“不存在”；
- 默认零导子；商结构未经依据取得 field 能力；
- import 期修改全局状态，或由注册顺序决定域选择；
- 为旧入口保留兼容层、转发层或双 API；
- 用关键字/AST 名字扫描冒充正确性门禁。

### 4.6 提交授权

- **未经用户明确同意，不得提交。** 禁止擅自执行 `git commit`、`git cherry-pick --continue`、`git revert`、`git reset`、`git push` 或任何改写历史、发布提交的操作。
- 允许在 working tree 中修改文件、运行测试和查看 diff；提交前必须把变更摘要、验收结果和拟提交信息交给用户，得到明确同意后才能提交。
- 用户说“撤销/重做”只授权对应范围内的修改；不得自行扩大范围，不得顺手提交其他文件，也不得在未同意时用“修复”名义新增提交。

## 五、当前进度与缺陷

本节是当前实现状态的唯一权威；`roadmap.md` 只规定路线与顺序，`progress.log` 用于日后审查与经验教训，只追加已完成、已验收的记录。

### 5.1 当前实现位置

- **S0/K0**：求导/积分纵线已有可用切片；`VariableRoles` 与请求维度（coverage/parameter_mode/result_language）已贯通，`TypedExpr`、定型 `ProblemSpec`、`AlgebraView` 与 bridge 的 `to_view`/`render`/`typed_view` 已接入，`parameter_schema`/`capability_requirements` 已接入所有注册操作，`ExecutionRequest` 已把固定问题、匹配的 `AlgebraRequest`、frame、条件策略与预算绑定给提案和提交，operation/service/checker 已完成从旧 `to_value`/`to_term` 的迁移，旧 polynomial bridge API 已删除；`BasisRegistry` 已消费 `BasisRef` 的 name/kind/version/digest/world，`Unverified` 已携带结构化 missing/conditions；核心数据流与结果契约仍未全部闭合；`CheckOutcome`/`CommitResult`/问题与提议结果已改为显式联合，提交边界已拆为 `validate_commit` → `ValidatedCommitBatch` → `publish_commit`，请求目标按预装配 view 局部选择，显式 `FunctionValue`、函数值应用/多表示/保守相等、`EqualOn`/`SamePartialFunction` 独立 checker 与比较/延拓操作、Task/Candidate 状态、执行尝试/取消、revision DAG 分支/合并、多动作事务、有限集合结果与结构化 decomposition 结果已接入。终态语义/类型不变量仍未全部闭合。工作流状态已由 `derive_task_state` 从候选、验证链接、尝试与固定请求单一派生；`Candidate` 记录 verification/applicability/coverage/result-language 四维；`VerificationLink` 记录规格种类/frame/coverage/条件/义务；`ResultSchema` 声明并检查结果形状；`Blocker` 携带目标命题与预算；`CheckRequest`/`CommitProposal` 携带候选数学数据并由数学 checker 强制核对；`Event`/`Revision` 已记录输入 revision/frame/输入对象/参数/执行报告/输出 revision 与 world/producing event，并由 `Session.history()`/REPL `history` 消费；`Revision.focus` 记录对象/任务/候选/出现位置焦点，`Session.focus` 从 revision 单一派生。
- **信任边界与历史快照（2026-11-08）**：`validate_commit`/`KernelStore._publish`/`FrameStore.create` 已用 `readable` 同时校验 meaning world、frame 可见性与逃逸；`ValidatedCommitBatch`/`Proposition`/`TypedExpr`/`AlgebraView` 的 seal 已改为非 init 字段，`dataclasses.replace` 不能伪造；`RejectedKind` 区分无效证据/无效请求/条件否证/规格否证，workspace 保留 `refuted_conditions`；`InferenceRecord` 记录证书 schema 身份；`VerificationContext.readable` 与 `problem_mismatch` 的 region 覆盖已接入；`CaseMergeChecker` 要求两个分支 premises；`FunctionValue`/`SamePartialFunction` 使用双向多重集与完整 `Proposition` 意义相等，参数符号不同只报 `UNKNOWN`；条件线性化不再零吸收偏函数因子；`DerivativeChecker`/初等/Hermite checker 绑定 problem region，specialize 证书携带 generic source/mapping 并由 checker 重建；`Revision` 增加 task/candidate 快照，取消从 attempt 派生，`merge_cases` 使用分支最新后代并保留 split 身份/可见性/父子边，`merge_case_conclusion` 传入分支 premises；`Occurrence` 增加 expected subterm；verified link 必须有 judgment，verified candidate 必须有 specifications/checker/certificate；`Revision.object_names` 与 `Event.actor_kind`/`operation_version` 已接入；`AlgebraView` 增加 `ConversionWitness` 并消费 `source_domain`/`valid_on`；`SetSort` 区分空集；`StructuredResult` 组件经 `CommitProposal`/`CheckRequest`/`Candidate` 绑定到 Hermite checker。
- **K1/U1 最小闭合**：`VerificationContext` 增加 `DecisionService`、`SupportsService`、`BudgetService`、`AlgebraService`、`DefinednessService` 与 `axioms`；`problem_mismatch` 与 Hermite checker 消费 decision/algebra/definedness，`CaseMergeChecker` 消费 supports，`LocalReceipt`/`decide` 携带 budget。新增 `AxiomRef`、`BudgetTicket`、`ConstructionRelation`、封闭 `Verdict`（`VerdictYes`/`VerdictNo`/`VerdictUnknown`）与 `LocalReceipt`/`RefutationReceipt`；`decide` 只调用 `validate_commit`，不发布 judgment、不写工作流；`Workspace.decide_candidate` 与 `decide` 命令已接入。前端 `@LABEL` 已支持在公式中嵌入当前 revision 的对象快照；`World`/`Frame`/`Declaration`/`Definition`/`Hypothesis` 已有稳定内容 digest，`Revision.frame_digest`/`Event.frame_digest` 记录并由 history 显示。`extend_function` 在 `EqualOn` 验证成功后记录 `function_extension` 构造关系，`relations` 命令显示。`Artifact`/`ObjectVersion` 已作为 `Expression`/`FunctionObject` 的不可变类型视图接入，`object` 命令显示 artifact kind/source operation；存储仍以现有对象记录为唯一权威。
- **A0/A1**：Z/Q、泛型多项式、一元 `divmod`/`gcd`/`xgcd`、精确除法、伪除法、内容/本原部分、平方自由分解、结式、判别式、子结式 PRS 链、多项式原函数、既约 K(x) 与有理 Hermite 归约；`polynomial_gcd` 与 `resultant` 已作为注册操作接入独立 checker（Bezout 恒等式与整数 Bareiss Sylvester 行列式）；Z/Q 因式分解、多元 gcd/分解和一般代数扩张尚未建立。
- **A4**：域上矩阵的 RREF、秩、仿射解、零空间、不相容见证、行列式与逆已实现；Z 上 Bareiss 分式自由行列式、Hermite/Smith 标准形及实际幺模变换已实现，`IntegerMatrixSpace` 已被 `ResultantChecker` 消费；域上矩阵算法仍是无矩阵表达式桥的公开低层 API，模结构、整数线性求解和更多模算法未建。
- **R0（首片）**：`cas/algebra/real_roots.py` 提供特征零有序域上一元非零平方自由多项式的精确 Sturm 链、零点跳过的符号变差、精确 Horner 取值与开区间相异实根计数；`root_count` 已作为注册操作接入独立 `RootCountChecker`，证书携带 p/a/b/n 与 Sturm 链项，checker 逐环验证证书链（首项=p、第二项=p'、后续项=-rem(...)、末项为非零常数）并重算 `V(a)-V(b)-[p(b)=0]`，不重建第二条链；操作在 admission/build 阶段拒绝零/非平方自由/非常数端点/反向区间，`define_problem` 因而记录 BLOCKED；`bootstrap` 与 `bootstrap_elementary` 注册该操作，参数化入口不注册（`Q[a]` 不是有序域）。根界、根隔离区间/RootOf、重数输出、实代数数（R1）与 CAD 未建。
- **P0**：Q[a…][x] 求导/积分、目标切换、显式基域 `bootstrap_parameterized_over` 与有理点特化已贯通；参数关系、参数分支、真实异常集算法和精确有理值之外的特化点尚未实现。
- **I0**：多项式原函数操作与 `HasDerivative` 验证已贯通；有理 Hermite 已通过 `HasHermiteReduction` 规格、证书与独立 checker 发行余项，并作为 `DECOMPOSITION` 结构化结果发行；区域化恒等式已验证：checker 提取 `Ne(D,0)` 源域、证明 claim region 非空且位于源域内、检查 `v`/`r` 的分母整除 `D`，再验证 K(x) 形式恒等式；`1/x`、`1/x^2` 在分母非零区域上可验证，全局 `TRUE` 仍诚实拒绝。留数与对数部分未建。
- **U0**：对象、候选、核验、假设、历史、`declare`/`define` 声明与定义、`diff`/`integrate`/`hermite`/`solve`/`gcd`/`resultant`/`specialize` 命令已有；`candidates`/`check`/`edit` 手动候选交互、Task/Candidate 状态、执行尝试/取消、revision branch/merge/switch、多动作事务、手动问题定义/运行、出现位置、依据方向的改写/换元、构造图、两情形分裂与历史合并已接入；`merge_case_conclusion` 已把两个互补分支中的闭合判断组合成基 frame 的 case-analysis 判断；带局部声明/定义、带未决义务、超过两情形及自动研究 revision 的完整证明合并仍未完成。
- **G/R/C/D/F/O**：除 R0 的根计数首片外，各高级里程碑尚未按新架构实现；完整目标和直接依赖见架构 §30 与 roadmap。

### 5.2 W0 已完成与剩余

已完成并验收：

- 表达式幂与环幂边界：桥只在底数为全局非零常数时投影 `Power(f, 0)`；`0^0`、`x^0`、形式参数 `a^0` 拒绝；`PolynomialRing.pow(a, 0) == 1` 保持。
- 原问题与指定区域：显式区域必须是已证区域的子区域；候选保留原 `ProblemSpec`；结果区域记录在 `OperationResult.region`/`VerificationLink.condition`。
- 泛结果历史可见性：`GenericResult` 进入 `Revision` 快照；undo/redo 与后续特化使用同一可见性规则。
- 工作区句柄身份：输入必须是本 workspace 的精确 `Expression` 且当前 revision 可见；外来/伪造句柄拒绝。
- 批量多项式：`PolynomialRing.sum`、`is_constant`、`is_nonzero_constant`。
- 封闭结果：`CheckOutcome`、`CommitResult`、`ProblemOutcome`、`ProposalOutcome`、`DerivationOutcome`、`SpecializationOutcome` 均为显式联合。
- 提交两阶段：`validate_commit` 只做验证并发行 sealed `ValidatedCommitBatch`，不写 ledger；`publish_commit` 校验 store token/world/frame/seal 后调用唯一 `_publish`，并核对 batch 的 conclusions 与 judgments、used_premises 与 inference 一致，重复发布由 ledger 在写入前拒绝。`CommitResult` 是 `ValidatedCommitBatch | Deferred | Rejected`，发布成功后的 `Committed` 不进入该联合；`Committed.obligations` 保留继承/复用义务，batch 只携带本批新义务。workspace、applicability、consistency 全部走两阶段，测试 helper `commit_now` 只存在于 `tests/support.py`。
- 执行请求与能力声明：`ExecutionRequest` 固定 `OperationRequest`、`ProblemSpec`、匹配的 `AlgebraRequest`、frame、`ConditionPolicy` 与 `ExecutionBudget`；`ProblemBuilt.algebra` 是操作把选中 view 交给工作流的唯一通道，`propose` 消费 `ExecutionRequest`，提交边界使用 `execution.frame`/policy/budget。`OperationSpec.capability_requirements` 由 `Capability` 结构词汇声明，`OperationRegistry` 按入口提供的 `provided_capabilities` 拒绝缺能力的注册；三个 bootstrap 入口各自提供实际装配的能力。`BasisRegistry` 按 name/kind/version/digest/world 校验 checker 的 `trusted_dependencies`，`bootstrap_elementary` 注册真实声明 basis。
- checker 结构化未决：`Unverified` 携带 `missing`/`conditions`，`TypedExprFailure` 暴露统一 `missing`，五个 polynomial checker 与初等 checker 把 `ViewRefused`/typing failure 的结构化信息传到 `Deferred`/`Blocker`；`Deferred` 增加 `missing`，workspace 两条执行/复核路径都保留。
- 请求局部角色：`DifferentiationView`/`IntegrationView` 按 target 预装配；同一会话可切换 `x` 与形式参数，Q[a][x] 与 Q[x][a] 各自选择正确系数结构。
- 函数对象：`FunctionValue` 固定参数绑定、固有定义域、结果 sort 和带有效区域的表示；`FunctionObject` 进入 revision；工作区定义函数时要求表示区域位于固有域内。
- 函数值运算：`FunctionValue.applications` 做参数替换并返回每个表示的项与区域项；`with_representation` 支持多表示；`same_partial_function`/`equal_on` 用 `SAME`/`DIFFERENT`/`UNKNOWN` 保守判定；工作区 `apply_function` 记录中性表达式与应用条件，`extend_function` 通过 `EqualOn` 独立 checker 证明新旧表示在旧域上一致后才记录新的函数版本。
- 函数值核验：`EqualOn`/`SamePartialFunction` 词汇、证书与 `FunctionEqualityChecker` 已接入；`compare_functions` 注册操作可发行 `PROPOSITION` 结果；`FunctionExtensionOperation` 要求 `EqualOn(old_domain, old, new)`，`FunctionComparisonOperation` 同时使用 `EqualOn` 与 `SamePartialFunction`。
- 工作区事务：`apply`、`assume`、`define_function` 抛出异常时同时回滚 kernel、frame 与工作区记录；早期逻辑拒绝不写记录，已进入记录阶段的拒绝/否证按历史保留；revision 记录直接父指针。
- 任务与历史：`TaskRecord`/`TaskState`/`CandidateState`/`ExecutionAttempt` 记录固定问题、候选、派生状态与执行尝试；`branch`/`switch_to`/`merge` 建立 revision DAG；`merge` 允许跨 frame 的历史视图合并，其他 frame 的对象保留原 frame 且不会自动在当前 frame 可用；`transaction()` 把多个动作作为一个原子回滚单元；`candidates`/`check`/`edit` 提供手动候选交互；`cancel_task` 保留已完成证明，只取消未完成任务。
- 手动工作簿：`define_problem`/`run_task` 固定并执行用户问题，执行任务与手动任务通过 `parent`/`depends_on` 形成构造图；`occurrences`/`rewrite`/`substitute` 记录出现位置、改写方向与新对象版本；`case_split` 发行互补假设的两个子 frame，`merge_cases` 合并两个分支历史，`merge_case_conclusion` 把两个分支中同一结论的闭合判断组合成基 frame 的 case-analysis 判断。
- 结构化结果：`ResultLanguage.DECOMPOSITION` 与 `StructuredResult` 进入 proposal、`OperationResult` 和 revision；Hermite 发行 `polynomial_part`/`remainder` 组件，undo/redo 与合并保持可见性。
- 有限集合结果：`ResultLanguage.SET`、`Set` 结构项与 `SetSort` 已接入；`solve_linear` 对一次/常数多项式发行有限解集，`HasSolutionSet`/`HasSolutionSubset` 与 `LinearSolutionChecker` 分别核验完整性与可靠性；`Coverage.SOUND_SET`/`COMPLETE_SET` 进入问题与工作流。
- 多项式 gcd/结式：`polynomial_gcd` 由 Bezout 恒等式和整除性独立核验；`resultant` 由整数 Bareiss 计算 Sylvester 行列式独立核验，`IntegerMatrixSpace` 因此获得真实操作消费者。
- 实根计数（R0 首片）：`cas/algebra/real_roots.py` 实现精确 Horner 取值、Sturm 链 `p, p', -rem(...)`、零点跳过的符号变差与开区间相异实根计数；`root_count` 注册操作、`HasRootCount(p, a, b, n)` 规格、`RootCountCertificate`（含 Sturm 链项）与独立 `algebra.root_count` checker 已贯通，checker 逐环验证证书链（不重建第二条链）并核对候选计数，不导入搜索模块；admission/build 与 `propose` 共用同一片段规则，`define_problem` 对零/非平方自由/非常数端点/反向区间记录 BLOCKED。片段固定为“Q[x] 中非零平方自由 p、精确有理常数端点、a<b、开区间、相异根”；零点多项式、非平方自由、非常数端点、反向区间与非多项式项以结构化 `missing` 拒绝，不猜计数、不伪造 `Refuted`。`bootstrap`/`bootstrap_elementary` 注册，参数化入口不注册；REPL 已有 `root_count [@LABEL] A B`。根界、根隔离区间/RootOf、重数、实代数数与 CAD 仍未建。
- 子结式：`UnivariatePolynomialRing.subresultant_chain` 实现特征零域上的子结式 PRS；末端非零项与 `gcd` 相伴；两个输入允许同次，初始一对之后度数严格下降。
- 有理 Hermite：`HasHermiteReduction(U,f,x,v,r)` 规格、`HermiteCertificate`、独立 `HermiteChecker` 与 `hermite_reduce` 操作已接入；余项 `r` 作为表达式发行，`v` 和原 `f` 在证书中；checker 独立复核 `f=D(v)+r` 与 `den(r)` 平方自由。
- 结构化拒绝：`Blocker` 携带 `reason`/`detail`/`missing`/`conditions`/`attempted`，进入 `OperationResult`、`TaskRecord` 与 `ExecutionAttempt`；`ProblemUnsupported`/`ProposalUnsupported` 保留缺失能力与未决条件；`Deferred(GUARDED|UNDECIDABLE|BUDGET)` 映射为 `OperationStatus.UNKNOWN`，不再冒充 `UNSUPPORTED`；前端显示 `missing`/`conditions`。`differentiate` 的“请求区域未被导数区域覆盖”从 `FRAGMENT` 改为 `GUARDED`，并保留请求区域作为未决条件。
- 核验绑定原问题：`CheckRequest` 携带 `ProblemSpec`，`CommitProposal` 携带 `problem`；`CheckerSpec.requires_problem` 强制数学 checker 必须拿到原问题。数学 checker 校验 `problem.operation`/`target`/`inputs`，`solve_linear` 还校验 coverage；`validate_commit` 在调用 checker 前拒绝缺失或不匹配的问题；工作区 `apply` 与 `check` 传递原问题。新增 kernel 测试覆盖“数学 checker 缺原问题”和“问题 kind 不匹配”。
- 工作流状态派生：`derive_task_state` 成为 `TaskState` 的唯一派生入口，消费固定 `ProblemSpec`、`Candidate`、`VerificationLink`、`ExecutionAttempt` 与 blocker；workspace 的 define/run/check/edit/block/cancel 路径全部改为调用它。派生规则覆盖 READY/BLOCKED/PARTIALLY_SOLVED/COMPLETED/COMPLETED_CONDITIONAL/CANCELLED，并消费 coverage、parameter_mode、language fit、链接条件与 kernel obligations；泛参数答案对 `ALL_PARAMETER_VALUES` 请求保持 PARTIALLY_SOLVED。请求的显式 `externalizable` 集现已随固定问题进入执行；链接条件与 kernel obligations 全部属于该集时派生 `COMPLETED_CONDITIONAL`，否则 `PARTIALLY_SOLVED`。
- 候选与验证载荷：`Candidate` 记录 verification/applicability/coverage/result-language 四维；`VerificationLink` 记录 specification kind、frame、coverage、结果区域与未闭合 kernel obligations；`Candidate.checked` 是唯一维度转移入口。`edit_candidate` 增加未检查候选时不抹掉旧候选的已验证结果；后续 deferred check 不降级已完成任务，也不把失败尝试的 blocker/detail 写回已完成任务；`candidates` 命令显示四维。
- 结果 schema 形状：`ResultSchema` 新增 `ResultShape`（EXPRESSION/PROPOSITION/SET/DECOMPOSITION）并强制 shape 与 language 一致；`validate` 检查 SET 必须是结构 `Set` 项且具有 `SetSort`（`set_term` 必须显式提供，`None` 直接拒绝）、PROPOSITION 的命题 sort、DECOMPOSITION 的组件和 EXPRESSION 不得携带 decomposition。workspace 只负责按 schema 需要做 elaboration 与结构识别，不再维护独立的结果形状分支。
- 结构化拒绝载荷：`Blocker` 增加 `target`（目标命题）与 `budget`（执行预算）；workspace 在提案/核验/定义/手动任务/手动复核路径填充已知目标与预算，`Session._report` 渲染 target 与预算限制。
- 候选数学数据核验：`CheckRequest`/`CommitProposal` 携带 `candidate`（工作流实际要发布的中性 term）；`validate_commit` 原样传入，数学 checker 强制核对候选与规格/证书声明的项一致，缺失或不一致返回 `InvalidEvidence`，不伪造成 `Refuted`。
- 核验上下文：内核在 `validate_commit` 中从提交 frame 构造 `VerificationContext`（world/frame/frames + `DecisionService`/`SupportsService`/`BudgetService`）并传入 `CheckRequest`；`problem_mismatch` 要求数学 checker 必须拿到上下文，并校验每个问题输入的 meaning world/frame 可见性；`problem_mismatch`/Hermite checker 消费 decision，`CaseMergeChecker` 消费 supports，`LocalReceipt`/`decide` 消费 budget；`AxiomRef`、`BudgetTicket`、`AlgebraService` 已接入。`DefinednessService` 与完整支持收集仍按真实消费者补齐。
- 事件与 revision 载荷：`Event` 记录 input revision、frame、输入对象版本、请求参数快照、执行报告与 output revision；`Revision` 记录 world 与 producing event。`_append_revision` 在创建 revision 后回填 event 的 output revision，不改写原事件；`Session.history()` 与 REPL `history` 消费这些字段并显示输入标签、参数、执行状态与输出 revision。
- 焦点载荷：`Focus` 封闭联合（ObjectFocus/TaskFocus/CandidateFocus/OccurrenceFocus）进入 `Revision.focus`；workspace 动作记录对象/任务/候选/出现位置焦点，`Session.focus` 从 revision 单一派生，`Session.history()` 显示 focus 种类与目标；焦点不改变数学输入。
- 声明与定义命令：`Workspace.declare`/`define` 在 `_transaction()` 内通过 `FrameStore.create` 建立子 frame，记录 `Declare`/`Define` 事件与 revision；`define` 先定型 body，失败不建 frame；重复名/别名环/逃逸/非良构 body 结构化拒绝；不发行 kernel judgment。REPL 新增 `declare NAME : SORT` 与 `define NAME := EXPR`，sort 词汇映射到 `language.sorts`。
- 候选角色契约：`CandidateRole`（RESULT/SOURCE/REMAINDER/SET/CONCLUSION/RIGHT）由 `CheckerBinding.candidate_role` 显式声明，经 `CommitProposal`/`CheckRequest` 传入 checker，并记录在 `Candidate` 上供手动复核复用；数学 checker 按角色选择规格中的对应项，缺失或错误角色返回 `InvalidEvidence`。`published_candidate` 的 operation 名分支已删除。
- 有理桥与区域：`AlgebraView` 增加 `source_domain`/`valid_on`；多项式桥在其片段上全定义，保持 `None`；有理桥对分母项发行 `Ne(den, 0)` 区域并保留消去前的洞（如 `x/x`）；`HermiteOperation`/`HermiteChecker` 消费该区域，非全定义输入返回 `UNKNOWN(GUARDED)` 并保留条件，全定义输入保持原有形式恒等式验证。
- 世界身份与自由符号可见性：`semantics.frames.new_world` 为每次装配发行进程内唯一 `WorldId`，`bootstrap._start` 使用它；`bootstrap_elementary` 在装配后以 `frames.world.id` 建立 `BasisRef`。`FrameStore.escapes` 现在把从未引入且不是语言 head/operator 的自由符号也报告为逃逸，`readable` 因此拒绝跨 world 或含未声明符号的命题；同批声明/定义通过显式 `local` 集合避免误报。
- 输入/参数/结果 schema：`OperationSpec.input_schema`/`parameter_schema`/`result_schema` 已成为必需字段，`OperationRegistry` 校验三者存在；`ResultSchema.single_language()` 是各操作固定结果语言的唯一来源。中央 `OperationInput` 联合已删除：`OperationRequest.parameters` 是 `tuple[tuple[str, object], ...]`，各操作用 `ParameterSchema` 解析成自己的参数载荷；无参数操作共用 `EMPTY_PARAMETER_SCHEMA`。
- 请求契约：`VariableRoles` 由 `ProblemSpec` 与 `AlgebraRequest` 共享；`OperationRequest` 携带 `coverage`/`parameter_mode`/`result_language`；各操作从预装配 view 与 `result_schema.single_language()` 取得固定维度，显式请求不一致时结构化拒绝；`define_problem` 执行与 `apply` 相同的准入并在定义期记录 BLOCKED；blocked 任务保留请求的 coverage/result_language，`run_task` 拒绝定义期 blocked 任务，避免把被改写的 fallback problem 当成原问题执行。`result_languages`/`FragmentSpec`/`Completeness` 已删除，不应恢复。
- 原子性与义务环境：`case_split` 的两个分支 commit 处在同一 workspace/frame/store 事务内；任一分支持非 `Committed` 时抛模块私有异常并整体回滚，不留下半个 split、judgment 或 revision；`FrameStore.count()` 报告当前已发布 frame 数，回滚后的 `stats()` 一致。`KernelStore.find_obligation` 除可见性和 term 相等外，还要求 `FrameStore.environment_unchanged(obligation.frame, frame)`：祖先 obligation 只在不新增声明/定义/假设的子 frame 中复用。
- 函数与集合：`same_parameter_signature` 是参数签名的唯一判定，`FunctionEqualityChecker` 的 `EqualOn`/`SamePartialFunction` 与 `compare_functions` 操作共同消费；不同参数形状在创建 candidate 前结构化拒绝，checker 对形状不同独立 `Refuted`，仅参数符号不同返回 `UNKNOWN`（alpha 等价不由本层决定）。有限集合的规范形式是“去重 + 按 `Term` 稳定结构序排序”，`set_term` 与 `set_members` 使用同一规范序；`SetSort` 的 `empty` 区分空集与 unknown-scalar 非空集。
- 状态载荷：`TaskRecord` 在构造时拒绝 `COMPLETED`/`COMPLETED_CONDITIONAL`/`PARTIALLY_SOLVED` 无 candidate、`BLOCKED` 无 blocker、`READY` 带 candidate/attempt/blocker；`OperationResult` 拒绝 `VERIFIED`/`CONDITIONAL` 无 candidate 或无 verification、`REFUTED` 无 candidate。`Rejected` 且无 refutation 的路径现在记录结构化 `Blocker`，不再产生无 blocker 的 BLOCKED 任务。
- 定型表达式：`language.typing.TypedExpr` 由唯一 sealed 入口 `Ty.typed` 发行，携带 resolved/expanded Term、sort、`MeaningKey` 与自由符号 `BindingView`；`MeaningKey` 移到 `language.meaning`，`IllScoped` 归入 typing，`elaborate.typing` 已删除。`ProblemSpec.inputs` 改为 `tuple[TypedExpr, ...]`，裸 Term 拒绝、跨 world 拒绝；`workspace._same_problem` 允许“祖先 frame 定义、后代 frame 运行”，同时检查输入 frame 可见与逃逸符号。
- 解释桥：`semantics.bridge.AlgebraView[E]` 由私有 seal 发行，固定 source TypedExpr、parent、value、target/parameter `SymbolBinding`、interpretation、`ConversionWitness` 与 `source_domain`/`valid_on`；`to_view` 返回 `ViewBuilt | ViewRefused`，`render` 返回 `Rendered | RenderRefused`，失败携带 `missing`/`conditions` 而不是压成 `None`。`typed_view` 是 checker 的独立准入路径：先 `elaborate.typed`，再 `to_view`，失败保持 `Unverified`。operation/service/checker 已全部迁到 `to_view`/`render`，旧 `to_value`/`to_term`/`to_polynomial` 与公共 `to_rational_function`/`to_rational_term` 已删除；多项式桥在其片段上全定义，`source_domain`/`valid_on` 保持 `None`；有理桥对分母项发行 `Ne(den, 0)` 区域，孔洞不伪装成 `TRUE`。
- 解释桥关系与拒绝契约：`typed_view` 在 `ViewBuilt` 后消费 `AlgebraView.interpretation` 与 `ConversionWitness` 的 `injective`/`preserves_equality`；解释与请求不一致返回 `interpretation_mismatch`，非单射或不保等号的 witness 不能把目标相等传回源相等而返回 `conversion_witness`，表示同构/嵌入的 witness 允许。sealed `AlgebraView` 强制 `PARAMETER_FAMILY` 至少绑定一个参数、其他解释不得绑定参数。`_admit_bindings` 先消费 `FreeSymbol.sort`，非标量自由符号返回 `scalar_symbol`；`Role` 不再经 `semantics.request` 转发。`ViewRefused`/`RenderRefused`/`Blocker`/`DerivationUnsupported`/`ProblemUnsupported`/`ProposalUnsupported` 统一要求非空 detail。
- **区域与定义性证据（2026-11-09）**：新增 `cas.semantics.regions` 的 `RegionSpec`（有序坐标 + `Proposition` 条件）与封闭 `RegionCertificate`（`NonemptyCertificate`/`SubregionCertificate`/`CoversCertificate`）；`certify_nonempty`/`certify_subregion`/`certify_covers` 只在本项目受限条件片段能证明时发行证书，`verify_region_certificate` 独立重检非空/包含/覆盖且不信任 `method` 文本。`conditions.condition_satisfiable` 只对 ground-true 与单原子线性区间非矛盾合取返回 `True`，ground-false/区间矛盾返回 `False`，其余诚实返回 `None`。`Definedness` 改为 `DefinednessExactness`（`TOTAL`/`EXACT`/`SUFFICIENT`）+ `RegionSpec` + 可选 `RegionCertificate`；`AlgebraView` 新增 `signature` 字段，发行时校验每个区域与源同 world、两个区域共享同一 `MeaningKey`（区域可在源 world 的后代 frame），并只在两个区域都存在时要求 `valid_on` 是可证子区域；源全定义（`source_domain=None`）时 `valid_on` 可以单独存在。`AlgebraView.definedness` 从既有区域单一派生 `Definedness`：两区域都空为 `TOTAL`；`domain` 存在且 `valid_on` 为空或相等为 `EXACT`；`domain` 存在且 `valid_on` 是严格子区域时为 `SUFFICIENT` 并携带 `SubregionCertificate`；`domain` 为 None 而 `valid_on` 存在时也是 `SUFFICIENT`，不携带证书，桥的 `ConversionWitness` 是该充分区域的证据。`Definedness` 的区域坐标必须包含源的全部自由符号，允许额外坐标并保留区域自身顺序。`HermiteChecker` 消费 `Definedness`、独立复核证书，并保留上下文 `DefinednessService` 覆盖检查。声明函数定义域、`Guarded`/`Piecewise` 分支局部语义、binder-aware premises、一般偏函数定义域、`ProblemSpec`/`FunctionValue` 的区域迁移和结果语言覆盖仍未建；`Proposition` 的结构定义性前提已由后续批次闭合。
- **区域绑定排序与稠密证书边界（2026-11-09）**：`RegionSpec` 增加 `sorts: tuple[tuple[SymbolId, Sort], ...]`，按 `SymbolId` 规范化；非空时必须恰好覆盖全部坐标，`sort_of` 查询单坐标绑定，`is_dense` 仅在全部坐标为 `RATIONAL`/`REAL` 时为真（空坐标集 vacuously dense）。`certify_nonempty`/`certify_subregion`/`certify_covers` 在任一参与区域非稠密时直接返回 `None`，`verify_region_certificate` 对非稠密区域上的伪造证书返回 `False`；`conditions.condition_satisfiable`/`is_empty_condition` 的稠密序假设因此只在 `is_dense` 为真时被消费。`AlgebraView` 增加 sealed `region_bindings: tuple[FreeSymbol, ...]`（默认 source binding view），要求覆盖源自由符号与每个现存区域的自由变量；`definedness` 用该绑定视图构造 `RegionSpec` 的坐标与排序，修复“区域含后代 frame 额外坐标时 `definedness` 报自由变量越界”的缺陷。严格子区域需要 `SubregionCertificate` 而绑定排序非稠密时，`definedness` 精确抛 `ValueError`，不静默降级。`Definedness` 已 sealed，只由 `_issue_definedness`/`AlgebraView.definedness` 发行，`dataclasses.replace` 不能伪造。`function_region` 为参数坐标记录 `FunctionParameter.sort`，条件含非参数自由变量时整体省略 `sorts`，使覆盖证书被诚实拒绝。`VariableRoles.world`、`ProblemSpec.function_inputs` 与函数相等 checker 的 problem binding 已由后续批次闭合；`ProblemSpec` 的精确性/解释要求与 `VariableRoles` 目标/参数排序已由后续请求契约批次闭合；`externalizable` 正向路径与系数范围/值域字段已由后续批次闭合；完整绑定位置与 binder-aware 角色、跨 frame 前提弱化、结果语言与嵌入字段仍未建，本批不声称完整 S1。
- **函数表示覆盖（2026-11-09）**：`cas.math.functions.equality` 新增 `function_region`/`function_coverage_regions`/`function_coverage_certificate`/`coverage_matches_value`，用 `RegionSpec`/`certify_covers` 在受限条件片段上证明函数新固有域被全部表示有效区域覆盖；`FunctionEqualityCertificate` 增加可选 `coverage: CoversCertificate`。`extend_function` 在 `EqualOn` 之外要求该覆盖证书，缺少可证覆盖时返回 `ProposalUnsupported(GUARDED, missing={"representation_coverage"})`，不创建候选、函数版本、构造关系或判断；`FunctionEqualityChecker` 独立重检证书并核对它精确匹配 `certificate.right`，伪造/不匹配为 `InvalidEvidence`。`SamePartialFunction` 证书携带覆盖字段时明确拒绝。一般半代数区域、任意多表示覆盖完整性与重叠一致性仍未建。
- **泛结果区域载荷（2026-11-09）**：`GenericResult.valid_on`/`excluded_cases` 已从裸 `Proposition` 迁移为 `RegionSpec`，即 §8.4/§10.3 的同一 `Region` 描述，不建立第二套区域类型。`cas.semantics.regions.region_from_proposition` 是 Proposition 载荷进入区域的唯一桥，坐标取 `coordinate_symbols(proposition.term)` 的排序结果；`GenericResult.assemble`/`coverage_claim`/`is_unconditional`/`validate_coverage_claim`、`specialize`、`OutsideValidity`/`NeedsRecomputation` 已统一读取 `RegionSpec.condition`。workspace 由 `MathematicalProposal` 构造泛结果时经该桥包装，`specialize` 的可见性检查读取 `family.valid_on.condition` 与每个排除情形的条件；`MathematicalProposal` 的公开字段本批仍为 `Proposition`，其准入规则复用同一桥。裸 Proposition 进入 `GenericResult` 为 `TypeError`；`ALL_VALUES` 仍要求 canonical `TRUE` 区域且无排除情形。
- **结构定义性前提（2026-11-09）**：`Proposition` 增加 `definedness: tuple[Proposition, ...]`，由 `propositions.check` 在定型后从项结构收集并递归发行：指数为 `IntLit <= 0` 的整数幂记录 `Ne(base, 0)`，和/积/比较/`And`/`Or`/`Not`/`Implies`/`Guarded`/`Piecewise` 递归到操作数；`Quote`/`Set` 载荷与 `Binder` body/annotations 不在本批检查；声明函数应用只递归参数，不发明函数定义域。前提按结构去重并保持首次出现顺序，必须与命题同 `MeaningKey`、不得重复、不得等于命题自身；`dataclasses.replace` 仍不能伪造。`conditions.premises_proved` 是唯一前提蕴含规则；`regions.premises_proved_from`/`proved_subregion` 让 `certify_nonempty`/`certify_subregion`/`certify_covers` 与 `verify_region_certificate` 拒绝未证明前提，`AlgebraView` 发行/`definedness` 与 `DefinednessService.covers` 消费同一规则。`elaborate.proposition` 经 `check` 自动携带前提。消费侧修正：`specialize` 对 `valid_on`/`excluded_cases` 先递归求值定义性前提（假前提 → 点不在有效区域/排除情形不适用，未决前提 → `NeedsRecomputation`），再求主条件；`FunctionEqualityChecker._check_equal_on` 先独立发行 claim region，再用 `proved_subregion` 证明它是各固有域与表示区域的全定义子区域，`_check_same` 拒绝带开放前提的完整域参与者；`FunctionExtensionOperation.propose` 与 workspace 的 `define_function`/`extend_function` 全部改用 `proved_subregion`；`proved_subregion` 新增 `same_meaning=False` 供 checker 在已独立校验同 world/可见 frame 后比较祖先 frame 的区域。裸 Proposition 载荷（`ProblemSpec.region`、`OperationRequest.region`、`FunctionValue.intrinsic_domain`/`FunctionRepresentation.valid_on`、`MathematicalProposal.result_region`/`valid_on`/`excluded_cases`）的当前消费者仍按 term 读取，故构造时明确拒绝非空 `definedness`，而不是静默忽略前提。声明函数定义域、`Guarded`/`Piecewise` 分支局部语义、binder-aware premises、一般偏函数定义域与这些载荷的 `RegionSpec` 迁移仍未建。
- **请求局部导子（2026-11-09）**：`AlgebraRequest.differential` 是请求局部导子载荷：缺省 `None` 表示该请求不假设任何导子（绝不使用零导子兜底）；存在时必须是 `DifferentialStructure`，并且是该请求唯一导子权威——同一 target 在另一请求中可以换用另一导子。`DifferentiationView`/`SpecializationView` 构造时要求请求携带导子，且视图的 `differential` 必须与请求的 `DifferentialStructure` 是同一对象（按 `is`，不是结构相等），缺失/不一致抛 `ValueError`；视图字段只是已校验的便利引用，不构成第二套导子选择。`bootstrap`、`bootstrap_parameterized`（每个 `K[parameters][target]` 视图与特化 Q[x] 视图）与 `bootstrap_elementary` 已把既有 `differential`/`base_differential` 写入全部对应 `AlgebraRequest`。嵌入、参数关系、实嵌入与 `VariableRoles` 绑定位置与 binder-aware 角色仍未建；目标/参数排序已由后续请求契约批次闭合（world 已固定）。
- **定义性保留 witness（2026-11-09）**：`ConversionWitness` 增加 `preserves_definedness`；表示同构与嵌入要求 `injective`/`preserves_equality`/`preserves_nonzero`/`preserves_definedness` 全为真，`representation_isomorphism()` 固定为真；一般同态允许失败。`AlgebraView.__post_init__`/`_issue_view`/`_admit_view_relation` 在视图携带 `source_domain`/`valid_on` 时要求 witness 保留定义性，`typed_view` 以 `ViewRefused(missing={"conversion_witness"})` 拒绝不保留定义性的区域视图；全定义视图不发明定义性声明，非保定义同态仍按单射/保等号规则传递等式。多项式桥、参数多项式桥与有理桥继续发行 `preserves_definedness=True` 的表示同构。嵌入/同态的具体实现、混域消解与 `AlgebraRequest` 嵌入字段仍未建。
- **解释与 witness 一致性（2026-11-09）**：`semantics.bridge` 新增唯一规则 `_interpretation_witness_refusal`，由 `AlgebraView.__post_init__` 与 `_issue_view` 共同消费：`EMBEDDED` 视图只接受 `EMBEDDING`/`REPRESENTATION_ISOMORPHISM`，`HOMOMORPHISM` 与“嵌入值”矛盾；`PARAMETER_FAMILY` 视图只接受 `REPRESENTATION_ISOMORPHISM`，`EMBEDDING`/`HOMOMORPHISM` 不足以声称形式参数族表示；`FORMAL` 仍接受三种 kind，由既有 `injective`/`preserves_equality`/`preserves_nonzero`/`preserves_definedness` 事实决定可传递什么。直接构造边界以 `ValueError` 拒绝，`_issue_view` 以 `ViewRefused(Reason.FRAGMENT, missing={"interpretation_witness"})` 在建造前拒绝。该规则与区域/定义性保留规则独立叠加，未改变既有 `preserves_definedness` 检查；多项式桥、参数多项式桥、有理桥与特化 Q[x] 视图仍发行表示同构并通过。具体嵌入/同态桥、混域消解与 `AlgebraRequest` 嵌入字段仍未建。
- **函数问题绑定与世界作用域角色（2026-11-09）**：`ProblemSpec.function_inputs` 固定函数问题所涉及的 `FunctionValue` 对象身份（参数绑定、固有域、全部表示区域），`compare_functions`/`extend_function` 的 `build_problem` 已传入对应值；非空时要求 `roles.target is None`，且每个固有域/表示区域与类型化输入同 world。`VariableRoles.world` 记录目标/参数 `SymbolId` 所属 meaning world；`ProblemSpec` 与 `AlgebraRequest` 都拒绝未绑定 world 的角色集，并要求 `roles.world`、`region`、每个 `externalizable` 前提与输入同 world。三个桥在 `to_view` 中以 `ViewRefused(missing={"request_world"})` 拒绝角色 world 与源 TypedExpr 不同的请求。`FunctionEqualityChecker` 将证书 `left`/`right` 绑定到 `problem.function_inputs`（compare 两项、extension 旧函数一项），`EqualOn` 消费 `problem_mismatch` 的 problem-region ⊆ claim-region 规则，`SamePartialFunction` 在 problem region 不可证位于完整域内时拒绝，并检查每个表示区域是其固有域的可证子区域；非稠密参数排序与区域中的非参数自由变量分别诚实返回 `GUARDED`/`FRAGMENT`。本切片只闭合 `function_inputs` 身份、world 作用域角色、桥的 `request_world` 拒绝与函数 checker 的 problem binding；`ProblemSpec` 的精确性/解释要求、`VariableRoles` 目标/参数排序、系数范围/值域字段与 `externalizable` 正向路径由后续批次闭合；当前仍开放的是 `VariableRoles` 绑定位置与 binder-aware 角色、跨 frame 前提弱化、嵌入、结果语言与一般完备性；本切片不声称完整 S1 或一般函数定义域语义。
- **请求契约（2026-11-10）**：`ProblemSpec` 增加 `Exactness`（当前只接受 `EXACT`；`APPROXIMATE` 在构造期以精确 `ValueError` 拒绝，因为没有近似 checker）与语言层 `InterpretationRequirement`（`FORMAL`/`PARAMETER_FAMILY`/`EMBEDDED`，language 不导入 semantics）。`AlgebraRequest.interpretation_requirement` 是唯一映射入口；`ProblemBuilt`/`ExecutionRequest` 要求有 algebra 时 problem requirement 非空且等于该映射，无 algebra 的函数问题时必须为 `None`。`VariableRoles` 增加 `target_sort`/`parameter_sorts`，按 target/parameters 是否存在校验；`ProblemSpec` 要求目标/参数排序，并要求输入 `BindingView` 中与角色同名的符号排序一致。`ProblemSpec` 对 `region` 与每个 `externalizable` 前提做稠密排序检查：每个自由变量必须由输入绑定、角色或函数参数绑定，排序必须是 `RATIONAL`/`REAL`；未知、整数、复数或未绑定坐标在构造期拒绝。`problem_mismatch` 增加 `roles`/`interpretation_requirement`/`exactness` 全绑定检查，微分/积分/初等/Hermite/线性/gcd/结式 checker 传入固定 request 的 roles 与 interpretation，函数 checker 不传 roles/interpretation 但保留 `function_inputs` 绑定。系数范围/值域（coefficient-range/value-domain）字段与 `externalizable` 正向路径由同日后续批次闭合；嵌入、结果语言、完整绑定位置与 binder-aware 角色仍未建；本切片不声称完整 S1 或一般区域代数。
- **候选代数快照与上下文代数（2026-11-10）**：`Candidate.algebra` 记录候选被提出时的精确 `AlgebraRequest` 快照；workspace `_apply` 用 `execution.algebra` 构造，`edit_candidate` 在清除证书时保留，`_candidate_proposal` 原样提交，因此 `check_candidate`/`decide_candidate` 复核同一 target/parameter/interpretation/differential，而不是重新装配另一个视图。`Candidate` 要求非空时 `algebra.roles == problem.roles`、`algebra.target == problem.target`；函数问题（`problem.function_inputs` 非空）必须为 `None`。`cas.kernel.evidence.context_algebra_mismatch` 是固定请求 checker 的唯一上下文代数规则；Derivative/Elementary/Hermite/Linear/Gcd/Resultant checker 全部消费 `VerificationContext.algebra`（Hermite 的本地重复检查已删除），`FunctionEqualityChecker` 对携带 algebra 的函数请求返回 `InvalidEvidence`，`CaseMergeChecker` 等核心逻辑规则不要求 algebra。`validate_commit` 仍只从 `proposal.algebra` 构造上下文；缺失/不同由 checker 报 `InvalidEvidence`，不伪造 `Refuted`。`externalizable` 正向路径与系数范围/值域字段由同日后续批次闭合；当前仍开放的是注册 `Covers` 规格/checker（当前 `CoversCertificate` 只是函数延拓内部证书）、嵌入/实嵌入、结果语言覆盖、完整绑定位置与 binder-aware 角色；本切片不声称完整 S1。

- **外部可置前提正向路径（2026-11-10）**：`define_problem` 不再因 `problem.allows_unresolved()` 整体拒绝问题，保留外部前提的 world、稠密排序与 frame 可读性检查，并把请求的显式 `externalizable` 集固定进唯一的 `ProblemSpec`。`apply`/`_apply` 新增显式 `externalizable` 参数；`operation.build_problem` 返回 `ProblemBuilt` 后，workspace 用 `dataclasses.replace` 把固定问题的集合替换为请求的显式集合，再执行维度检查、构造 `ExecutionRequest`、提案与提交；operation 自己构造的集合不构成第二权威。`run_task` 传入 `task.problem.externalizable`，`_same_problem` 继续精确比较该集合。proposal 的 `result_region` 作为 `VerificationLink.condition` 进入任务派生；`derive_task_state` 只在链接条件与 kernel obligations 全部属于固定显式集合时给出 `COMPLETED_CONDITIONAL`，无开放条件仍为 `COMPLETED`，否则 `PARTIALLY_SOLVED`。`result_region` 是工作流条件，不是 kernel obligation。测试覆盖：`sqrt(x)` 在 `x > 0` 外部化时 `COMPLETED_CONDITIONAL`，不同集合或无集合时 `PARTIALLY_SOLVED`，`x^2` 无条件结果保持 `COMPLETED`，直接 `apply` 传递集合，手动复核条件候选仍为 `COMPLETED_CONDITIONAL`，`_same_problem` 拒绝不同集合，frame 外前提被拒。跨 frame 前提弱化、注册 `Covers` 规格/checker（当前 `CoversCertificate` 只是函数延拓内部证书）、嵌入/实嵌入、参数关系、结果语言、完整绑定位置与 binder-aware 角色、一般完备性仍未建；系数范围/值域字段已由同日后续批次闭合。

- **系数范围与值域（2026-11-10）**：`cas.language.problems` 新增 `ValueDomain`（`INTEGER`/`RATIONAL`/`REAL`/`COMPLEX`，无 `ANY` 逃逸值）、`DomainRequirement` 与唯一映射 `value_domain_of_sort`；`ProblemSpec.domain_requirement` 固定语言层系数范围 `coefficient` 与允许值域 `values`，有 target 的问题要求 `coefficient` 非空且 `values` 与 `target_sort` 映射一致，函数问题固定 `coefficient=None`/`values=REAL`，既无 target 又无函数输入的核心/实用问题保持 `None`。`AlgebraRequest.coefficient_domain` 是必需装配声明（当前 Q 基座全部为 `RATIONAL`，Z 测试声明 `INTEGER`），不从 parent 类型嗅探；`value_domain` 由 `roles.target_sort` 经同一映射派生。`ProblemBuilt`/`ExecutionRequest` 强制 problem 与 algebra 的 coefficient/value domain 双向一致；`problem_mismatch` 增加可选 coefficient/value domain 检查，固定请求 checker 传入自身请求值，函数 checker 传 `None`/`REAL`。`CoversCertificate` 仍是函数延拓的内部证书：由 `FunctionEqualityChecker` 独立重检，不发行独立 `Covers(region, pieces)` judgment；本片段没有 `Covers` Proposition/checker/operation，注册 `Covers` 是未来 K1/S1 工作且必须与真实发布消费者同批加入。该裁定不声称 §12.2 已完整实现。

- **固定问题比较与区域绑定排序（2026-11-10）**：`workspace._same_problem` 在既有 operation/输入/roles/function_inputs/region/result_language/coverage/externalizable 比较之外，精确比较 `ProblemSpec.exactness`、`interpretation_requirement` 与 `domain_requirement`；`run_task` 仍只通过该唯一比较器接受执行重建的问题，重建出不同答案标准、解释要求或系数/值域的执行被记录为 blocked。`semantics.bridge._region_binding_refusal` 对 `region_bindings` 中与源自由符号同 `SymbolId` 的条目要求排序等于源 `BindingView` 的排序；显式绑定不能再把非稠密源坐标伪装成 `REAL` 以骗取稠密 `SubregionCertificate`。后代 frame 的额外坐标仍由桥声明排序，本规则不为它们推断排序。

- **默认初等入口的积分路径（2026-11-10）**：`bootstrap_elementary` 继续用 `calculus.derivative.elementary` 验证 `differentiate`（该 checker 只接受 `differentiate`），并在同一 Q[x] 桥/请求上注册既有 `DerivativeChecker`（id `calculus.derivative.polynomial`，`CheckerSpec` 只接受 `integrate`、无 trusted dependencies）。`_integration_views` 获得显式 checker-id 参数，初等入口的积分 service 与 view 绑定该多项式检查器，因此默认 REPL 的 `integrate` 对 `2*x + 3` 等多项式返回 `VERIFIED`；`1/x` 仍在多项式片段外以 `UNSUPPORTED`/`polynomial_antiderivative` 拒绝。`bootstrap`/`bootstrap_parameterized` 的积分绑定与行为不变，且没有第二份多项式 checker 实现。

- **泛结果家族方向与特化选择（2026-11-10）**：`Revision.generic_results` 保留同一 source 的多个 `GenericResult`；`Workspace._apply` 追加新家族而不是覆盖，`Workspace.generic_results` 返回全部可见家族，`generic_result` 返回最新家族，`derivative_family` 只选择 correctness specification 为 `HasDerivative` 且 `claim.source == source.term`、`claim.candidate == family.result`、`claim.variable.symbol_id == runtime.variable` 的最新家族。`Workspace.specialize` 只对导子方向家族特化；只有积分、其他关系或另一目标变量的家族时返回结构化 `UNSUPPORTED`（`missing=derivative_family`）且不写 kernel，不把真公式误报为 `REFUTED`。`SpecializationOperation.propose` 对非导子方向家族同样结构化拒绝；`merge`/`merge_cases` 按家族记录合并并去重相同记录。一般积分家族特化仍未实现。

- **前端 decide 边界（2026-11-10）**：`Session._decide` 把 `Workspace.decide_candidate` 的 `ValueError`（不可见候选、编辑后无证书等）翻译为 `SessionError`，REPL 因而只报告错误并继续；`check_candidate` 行为不变。编辑产生的候选仍是无证书的 unchecked 记录，手动证据录入未实现。

仍未完成：

| 边界 | 当前问题 | 验收出口 |
|---|---|---|
| 情形合并的数学结论 | `merge_case_conclusion` 已对两个纯互补假设分支、同一结论、闭合判断发行基 frame 判断；带局部声明/定义、带未决义务、超过两情形、分支结论不同的合并未建 | 覆盖更一般的 case 证明合并，并保留互斥/覆盖与前提可见性 |
| 结果语言覆盖 | `DECOMPOSITION`、`SET`、`SOUND_SET`/`COMPLETE_SET` 与有限解集已有；无限集、区间、覆盖分解和一般集合运算未建 | 集合/覆盖结果语言覆盖非有限情形，且与请求覆盖一致 |
| A2/A3 代数完备性 | Z/Q 因式分解、多元 gcd/分解、一般代数扩张和模结构未建；这些是 W2 的 A2/A3 节点，不是 W1 的公共核心 | 按 roadmap W2 交付算法、证书与真实消费者 |
| A4 低层边界 | 域上矩阵的秩/零空间/行列式/逆仍是公开低层 API，没有矩阵表达式桥；`IntegerMatrixSpace` 已被结式 checker 消费 | 建立矩阵表达式桥后注册为操作，或维持明确记录的公开低层 API 契约 |
| 支持/核验契约 | `Blocker` 已保留 reason/missing/conditions 并新增 target/budget；`CheckRequest`/`CommitProposal` 已绑定原问题、候选数学数据与 `RejectedKind`；`OperationSpec.input_schema`/`parameter_schema`/`result_schema` 已声明并被 `build_problem`/workspace 消费；`VariableRoles.world`、`ProblemSpec.function_inputs`、`TypedExpr`、定型 `ProblemSpec.inputs`、`AlgebraView`/`to_view`/`render`/`typed_view`、`ExecutionRequest`、`ValidatedCommitBatch`/`validate_commit`/`publish_commit`、`BasisRegistry`、`capability_requirements` 已建并接入，operation/service/checker 已迁移；函数问题 checker 已绑定 `problem.function_inputs` 并执行 problem-region 覆盖、表示区域包含、非稠密参数与非参数自由变量检查；`AlgebraView.source_domain`/`valid_on`、`ConversionWitness` 与有理桥已接入并由 Hermite 消费；`CheckRequest` 已携带 `VerificationContext`（decision/supports/budget）并由 `problem_mismatch` 校验 region 覆盖；固定请求 checker 的 `VerificationContext.algebra` 已由唯一 `context_algebra_mismatch` 消费，`Candidate.algebra` 保存执行代数快照并由手动复核原样重提，函数问题拒绝 algebra 快照；`LocalReceipt`/`Verdict` 已建，`AxiomRef`、`DefinednessService`/`AlgebraService` 与完整 §13.4 支持收集仍属 K1 | 按 §32.4/§16.1/§32.6 继续补齐 K1 载荷；搜索结果使用 §11.3 变体 |
| 工作流历史载荷 | `Event`/`Revision` 已记录输入 revision/frame/输入对象/参数/执行报告/输出 revision 与 world/producing event，并由 `Session.history()`/REPL `history` 消费；`Revision.focus`、task/candidate 快照、`Occurrence.expected`、`Revision.object_names`、`Event.actor_kind`/`operation_version` 已接入；`ConstructionRelation`、`verification_refs`/`explanation_ref` 与完整持久化/重放载荷未建 | 按 §17.8/§17.9/§32.4 补齐构造关系、完整 Event 分类与持久化/重放 |

### 5.3 已知缺陷与未实现项

- **条件与义务**：区域空性/包含、受限蕴含/等价、`ConditionChecker` 与 `resolve_applicability` 已接入；`Blocker` 已保留 `GUARDED`/`FRAGMENT` 区分并携带 target/budget，进入任务/尝试记录与前端显示；`CheckRequest` 已绑定原问题、候选数学数据与 `VerificationContext`（world/frame/frames + `DecisionService`/`SupportsService`/`BudgetService`）；固定请求 checker 的 `VerificationContext.algebra` 现由唯一 `context_algebra_mismatch` 规则消费，候选通过 `Candidate.algebra` 保存提出时的精确请求快照并由手动复核原样重提，函数问题拒绝 algebra 快照；`problem_mismatch` 与 Hermite checker 消费 context decision，`CaseMergeChecker` 消费 context supports；条件线性化已修复零吸收。`NeedsInformation`/`BudgetExhausted`/`Cancelled` 搜索变体与完整支持收集仍未建；`LocalReceipt`/`AxiomRef`/`BudgetTicket`/`AlgebraService`/`DefinednessService` 已建。一般一阶一致性、等价变形后的否证、多原子线性不等式组与更完整的 Or/Not 仍未建。区域判定只覆盖单原子线性边界与受限连接词，不宣称一般半代数区域代数。
- **命题与区域载荷**：`Proposition` 已增加 `definedness: tuple[Proposition, ...]`：架构 §12.1 要求的结构定义性前提已由 `propositions.check` 收集，非正指数整数幂记录 `Ne(base,0)`，和/积/比较/布尔连接词递归到操作数；前提参与相等/hash 与 seal，`dataclasses.replace` 不能伪造，`Quote`/`Set` 载荷与 `Binder` body/annotations 明确不检查。`RegionSpec`/`RegionCertificate` 已建立：`RegionSpec` 固定有序坐标与条件命题，`NonemptyCertificate`/`SubregionCertificate`/`CoversCertificate` 由受限条件片段发行并由 `verify_region_certificate` 独立重检；`conditions.premises_proved`/`regions.premises_proved_from`/`proved_subregion` 已被区域证书、`AlgebraView` 发行/`definedness` 与 `DefinednessService.covers` 消费，未证明前提不会被当作成立。`Definedness` 已改为 `DefinednessExactness`（`TOTAL`/`EXACT`/`SUFFICIENT`）+ `RegionSpec` + 可选证书，由 `AlgebraView.definedness` 单一派生并由 Hermite checker 消费；`SUFFICIENT` 既覆盖非平凡固有域上的严格子区域（携带 `SubregionCertificate`），也覆盖源全定义而表示仅在充分子区域有效（证书为空，桥的 `ConversionWitness` 是证据）。区域坐标只要求包含源的全部自由符号，允许额外坐标并保留自身顺序；视图发行要求每个区域与源同 world、成对区域共享同一 `MeaningKey`。`GenericResult.valid_on`/`excluded_cases` 已迁移为 `RegionSpec`，经 `region_from_proposition` 从现有 Proposition 载荷取得确定坐标，并由 workspace 泛结果记录与 `specialize` 消费；`specialize` 现在递归求值条件的定义性前提，假前提视为点不在有效区域/排除情形不适用，未决前提返回 `NeedsRecomputation`。仍为裸 Proposition 的区域载荷（`ProblemSpec.region`、`OperationRequest.region`、`FunctionValue.intrinsic_domain`/`FunctionRepresentation.valid_on`、`MathematicalProposal.result_region`/`valid_on`/`excluded_cases`）本批在其构造器拒绝非空 `definedness`，因为当前消费者按 term 读取；这不是 `RegionSpec` 迁移完成。声明函数定义域、`Guarded`/`Piecewise` 分支局部语义、binder-aware premises、一般偏函数定义域、`ProblemSpec`/`FunctionValue` 的区域迁移和结果语言覆盖仍未建。`OperationSpec.explanation_schema` 尚未接入，因为当前没有记录/渲染解释配方的消费者。本批进一步闭合区域描述侧：`RegionSpec` 记录 binding sorts 并提供 `is_dense`，非稠密/未知排序区域不发行也不接受稠密序证书；`AlgebraView.region_bindings` 使含后代 frame 额外坐标的区域进入 `definedness`，`Definedness` 已 sealed 且只由视图发行；`_region_binding_refusal` 拒绝与源自由符号排序不一致的显式绑定，显式绑定不能再把非稠密源坐标伪装成稠密坐标，后代 frame 额外坐标仍由桥声明排序；`function_region` 只为参数坐标写排序，含非参数自由变量时省略排序。`ProblemSpec` 的精确性/解释要求与 `VariableRoles` 目标/参数排序已由后续请求契约批次闭合；系数范围/值域已由同日后续批次闭合；完整绑定位置与 binder-aware 角色、注册 `Covers` 规格/checker、结果语言、嵌入字段与一般完备性仍开放；`externalizable` 正向路径已由 2026-11-10 批次在工作流片段闭合（请求显式集经 `ProblemSpec`/`ExecutionRequest` 保留，`derive_task_state` 只在全部开放条件都属于该集时给出 `COMPLETED_CONDITIONAL`），跨 frame 前提弱化仍未建；`VariableRoles.world`、`ProblemSpec.function_inputs` 与函数相等 checker 的 problem binding 已由本批闭合，不是本批完成项的说法不再适用于这三项。
- **函数值层**：`FunctionValue` 是工作簿对象而不是中性 Term，因此没有通用 `ResultLanguage.FUNCTION` 结果通道；函数关系通过 `EqualOn`/`SamePartialFunction` 命题发行，函数版本由显式 `extend_function` 动作记录。`FunctionValue.intrinsic_domain` 与每个表示 `valid_on` 是带 `MeaningKey` 的命题，`FunctionEqualityChecker` 校验其 world/frame 可见性；表示集合按双向多重集与完整命题意义比较，重复表示被拒绝；参数符号不同只返回 `UNKNOWN`，不伪造成 `Refuted`。`FunctionValue`/`FunctionRepresentation` 本批只接受总条件（`definedness` 为空）；`FunctionEqualityChecker` 用 `proved_subregion` 证明 claim region 是各固有域/表示区域的全定义子区域，`FunctionExtensionOperation.propose` 与 workspace 的 `define_function`/`extend_function` 使用同一前提感知规则，部分条件的新域/新表示区域在 `propose` 中返回结构化 `ProposalUnsupported`。多表示覆盖同一固有域的完整性现在由 `extend_function` 要求 `CoversCertificate` 并在 `FunctionEqualityChecker` 中独立重检（仅限受限区域片段：ground truth、单原子线性区间、受限蕴含）；一般半代数区域、任意多表示覆盖完整性、重叠一致性以及 `FunctionValue` 的 `RegionSpec` 迁移仍未核验/未建。函数问题现在由 `ProblemSpec.function_inputs` 固定 `FunctionValue` 身份，checker 在 `problem_mismatch` 之后要求 compare 的两侧、extension 的旧函数与问题值精确相等；`EqualOn` 额外要求 problem region 被 claim region 覆盖，`SamePartialFunction` 要求 problem region 位于两侧完整域内，并逐个检查表示区域是固有域的可证子区域。非稠密参数排序返回 `Unverified(GUARDED)`，claim region 含非参数自由变量返回 `Unverified(FRAGMENT)`；函数问题没有代数视图，`FunctionEqualityChecker` 拒绝 `context.algebra` 非空的请求，workspace 函数候选的 `Candidate.algebra` 必须为 `None`；普通无 problem 的 checker 调用保持原行为。
- **信任元数据**：`CheckerSpec`、`BasisRef`、证书类型与节点数/深度预算已有记录；`BasisRegistry` 已在 `validate_commit` 中逐项校验 name/kind/version/digest/world，`ValidatedCommitBatch`/`validate_commit`/`publish_commit` 两阶段已建并消费 store token/seal/world/frame；`ValidatedCommitBatch`/`Proposition`/`TypedExpr`/`AlgebraView` 的 seal 已改为非 init 字段，`dataclasses.replace` 不能伪造；`validate_commit`/`KernelStore._publish`/`FrameStore.create` 已用 `readable` 同时校验 meaning world、frame 可见性与逃逸；`CheckRequest` 已携带原 `ProblemSpec`、候选数学数据与内核构造的最小 `VerificationContext`（world/frame/frames），`problem_mismatch` 校验问题输入、problem region 覆盖与 meaning world/frame 可见性；`InferenceRecord` 记录证书 schema 身份；`CheckerSpec.requires_problem` 强制数学 checker 绑定原问题，数学 checker 强制核对候选与规格/证书声明的项一致；`WorldId` 已从硬编码 0 改为每次装配唯一，`escapes` 已报告未声明自由符号。`VerificationContext` 的 decision/supports/budget/algebra/definedness 服务与 `axioms` 已接入；`context_algebra_mismatch` 是固定请求 checker 的唯一 algebra 规则，`Candidate.algebra` 保存提出时的精确请求并由手动复核原样重提，函数问题拒绝 algebra 快照；片段级一致性 checker、多推理批次与分支合并支持、持久化的内容寻址 world 身份与跨 store/session 句柄仍未建；`LocalReceipt`/`RefutationReceipt`/`Verdict`/`AxiomRef`/`BudgetTicket` 已建。候选发布侧由 `CheckerBinding.candidate_role` 显式声明（RESULT/SOURCE/REMAINDER/SET/CONCLUSION/RIGHT），经 `CommitProposal`/`CheckRequest` 传到 checker；`published_candidate` 的 operation 名分支已删除。
- **结果 schema 的形状**：`ResultSchema` 已声明 `ResultShape`（EXPRESSION/PROPOSITION/SET/DECOMPOSITION）并强制 shape 与 language 一致；`validate` 检查 SET 必须是结构 `Set` 项且具有 `SetSort`（`set_term` 必须显式提供，`None` 直接拒绝）、PROPOSITION 的命题 sort、DECOMPOSITION 的组件和 EXPRESSION 不得携带 decomposition；workspace 只负责按 schema 需要做 elaboration 与结构识别。`StructuredResult` 的组件经 `CommitProposal`/`CheckRequest`/`Candidate` 传到 checker；Hermite checker 校验 `polynomial_part`/`remainder` 与已验证分解一致。多语言/多形状 schema 目前显式拒绝，待出现真实多结果语言操作时再扩展。
- **操作参数边界**：`OperationRequest.parameters` 是 `tuple[tuple[str, object], ...]`；每个注册操作声明自己的 `ParameterSchema` 并解析成私有参数载荷，`OperationRegistry` 校验 schema 存在，中央 `OperationInput` 联合已删除；`OperationRequest.parameter` 已删除，类型判定归各操作的 schema。
- **初等层**：只覆盖一元函数、非负整数幂；负幂/分式、更多函数、初等表达式相等判定、完整 `BasisRef`、别名/角色尚未实现。条件定律体调用的函数定义域已并入结果区域；体内部的非零要求仍属于受信 basis 的承诺。默认初等入口的 `differentiate` 仍由 `calculus.derivative.elementary` 验证；多项式子片段的 `integrate` 由同批注册的 `calculus.derivative.polynomial` 验证，负幂/分式仍以多项式片段外拒绝。
- **代数层**：`xgcd`、伪除法、精确除法、内容/本原部分、平方自由分解、结式、判别式、子结式 PRS 链与有理 Hermite 已建；Z 上 Bareiss 分式自由行列式、Hermite/Smith 标准形与实际幺模变换已建；`polynomial_gcd` 与 `resultant` 已接入注册操作和独立 checker；Z/Q 因式分解、多元 gcd/分解、一般代数扩张和模结构未建（A2/A3 属 W2）。正特征平方自由、非域系数普通除法诚实拒绝。`pseudo_divmod`、`content`、`primitive_part`、`squarefree_part`、`discriminant`、`subresultant_chain` 以及域上矩阵的 `rank`/`nullspace`/`determinant`/`inverse` 仍是公开低层 API，没有 workflow/operation 消费者；`IntegerMatrixSpace` 已由 `ResultantChecker` 消费。按红线 7，未接线的低层 API 不能算端到端能力，其契约由类型、性质测试和模块文档明确。
- **实根计数层（R0 首片，2026-11-10）**：`cas/algebra/real_roots.py` 的 `sturm_chain`/`sign_variations`/`count_real_roots_open` 只覆盖特征零有序域上的非零一元平方自由多项式；`sturm_chain` 以严格降次的欧几里得余式链终止于非零常数，零多项式与非平方自由多项式分别以 `nonzero_polynomial`/`squarefree_polynomial` 拒绝，正特征与非有序系数域以 `characteristic_zero_field`/`ordered_coefficient_field` 拒绝。`count_real_roots_open` 要求 `a<b`，采用开区间公式 `V(a)-V(b)-[p(b)=0]`，端点根由这一加入约定处理，不用第二套约定。`root_count` 操作证书携带完整 Sturm 链；`RootCountChecker` 逐环验证该链（首项=p、第二项=p'、后续项=-rem(...)、末项非零常数）并从已验证链重算计数，不重建第二条链；候选数错误报 `Refuted`，证书/链/问题不匹配（含缺失/多余/错误首项/非恒常尾项/零余式提前终止）报 `InvalidEvidence`，零/非常数端点/反向区间报 `Unverified(FRAGMENT)`。`ORDERED_FIELD` 是 `Capability` 的真实词汇，由 `bootstrap`/`bootstrap_elementary` 提供并被 `root_count` 声明；参数化运行时（`Q[a]` 非有序）不注册该操作。admission/build 与 `propose` 共用同一片段规则，手动 `define_problem` 在定义期即记录 BLOCKED。根界、根隔离区间、`RootOf`/实代数数、重数输出、R1、CAD、实根与理想/解集语义的其余部分均未建；本切片不声称完整 R0。
- **积分层**：多项式原函数操作已由 `HasDerivative` checker 验证；默认初等入口也通过同一多项式检查器（`calculus.derivative.polynomial`）验证其多项式子片段；有理 Hermite 已通过 `HasHermiteReduction` 规格、证书和独立 checker 发行余项；留数与对数部分、Risch 塔和初等/非初等判定未建。`1/x` 仍被多项式积分片段拒绝，但可由 `hermite` 命令归约。有理桥现在为分母项发行 `Ne(den, 0)` 的 `source_domain`/`valid_on`；Hermite operation 把该区域写入规格/证书与 `result_region`，checker 对非全定义区域返回 `Unverified(GUARDED)` 并保留条件。区域化恒等式验证已建：checker 证明 claim region 非空且位于源域内、`v`/`r` 的分母整除源分母 `D`，再验证 K(x) 形式恒等式；全定义输入仍走原有形式恒等式路径。
- **问题与覆盖层**：`solve_linear` 与求导/积分/gcd/结式/Hermite 等操作的请求维度已贯通；显式 coverage/parameter_mode/result_language 与操作固定维度不一致时结构化拒绝，blocked 任务保留请求维度，`run_task` 不再执行定义期 blocked 任务。workflow 接受 `ONE_VERIFIED` 的 `EXPRESSION`/`PROPOSITION`/`DECOMPOSITION` 结果，以及 `SOUND_SET`/`COMPLETE_SET` 的有限 `SET` 结果；`solve_linear` 已贯通完整/可靠有限解集。无限集、区间、覆盖分解与通用集合运算仍明确拒答；`externalizable` 前提现由工作流正向接收，并在全部开放条件都属于显式集时派生 `COMPLETED_CONDITIONAL`，不把它当作 kernel obligation 或无条件结果。
- **本轮审查新增未闭合项**：`AlgebraView` 的 `source_domain`/`valid_on` 已建立：多项式桥在其片段上全定义，保持 `None`；有理桥对分母项发行 `Ne(den, 0)` 区域，`HermiteOperation`/`HermiteChecker` 已消费；区域化 Hermite 恒等式验证已建。sealed view 已校验自由符号覆盖、parent 成员关系、interpretation/parameter binding 一致性、每个区域与源同 world 以及成对区域共享同一 `MeaningKey`；target/parameter 与 parent ring 的桥特定一致性由 bridge 准入负责。`ProblemSpec` 的 resolved/raw term 对齐已在 workspace 的请求定型路径完成。证书按 request frame 解释，`FunctionValue` 的域/表示命题携带 `MeaningKey` 并由 checker 校验可见性；`Event`/`Revision` 已记录输入输出/参数/作用域/输出 revision，`ConstructionRelation` 与持久化/重放未建；`TaskState` 单一派生与 `Candidate`/`VerificationLink` 四维/规格/frame/coverage/条件/义务已闭合。
- **声明与绑定**：声明 DSL 已统一常数/函数/定律与 binder/operator 的 loader；前端 `define` 已提供局部别名，声明 DSL 的别名/角色声明仍未接入。binder 已完成声明参数 sort、函数值/值 binder、嵌套索引与注解外层定型；注解驱动的参数 sort、量化/全称引入、前端 binder 语法与 source 形式仍未完成。
- **桥接**：多项式与 `K(x)` 的有理函数桥已建（含负整数幂）；任意基域表达式的反向解析仍需专门桥接。零次幂只在底数为全局非零常数时投影，`0^0`/`x^0`/形式参数 `a^0` 拒绝；负幂的零基（如 `0^-1`）也按片段外拒绝。其他全局非零性判定（如 `x^2+1 > 0`）尚未接入，保持片段外拒答。`ConversionWitness.preserves_definedness` 已在 `AlgebraView.__post_init__`/`_issue_view` 发行与 `_admit_view_relation`/`typed_view` 准入边界消费：携带 `source_domain`/`valid_on` 的视图必须由保留定义性的 witness 支撑。解释与 witness kind 的一致性已由唯一规则 `_interpretation_witness_refusal` 在 `AlgebraView.__post_init__`/`_issue_view` 强制：`EMBEDDED` 拒绝 `HOMOMORPHISM`，`PARAMETER_FAMILY` 拒绝非 `REPRESENTATION_ISOMORPHISM`，`FORMAL` 保留三种 kind 并由 witness 标志决定可传递的事实；`_issue_view` 以 `ViewRefused(Reason.FRAGMENT, missing={"interpretation_witness"})` 拒绝。具体嵌入/同态实现、混域消解与 `AlgebraRequest` 嵌入字段仍未建。
- **参数层**：角色分离、`AllParameterValues`/`GenericParameters` 覆盖声明、精确有理点特化、异常集协议、revision 级家族可见性和显式基域装配已完成；同一 source 的多个 `GenericResult` 家族现按记录保留，`Workspace.derivative_family` 只选择导子方向家族，`specialize` 对积分/其他方向家族返回结构化 `UNSUPPORTED`。一般积分家族特化、参数关系（多项式等式/不等式/整数约束）、参数分支、会生成非空异常集的真实局部化算法，以及精确有理值之外的特化点尚未实现。
- **请求局部导子**：`AlgebraRequest.differential` 已作为请求局部导子载荷接入，缺省 `None` 表示无导子假设，存在时必须为 `DifferentialStructure`；`DifferentiationView`/`SpecializationView` 按对象同一性校验请求导子，四个 bootstrap 视图（Q[x]、`K[parameters][target]`、特化 Q[x]、初等）已携带既有 `DifferentialStructure`。本切片只闭合“请求固定一个已有导子并交给现有求导消费者”，嵌入/转换映射、参数关系、实嵌入、`VariableRoles` 绑定位置与 binder-aware 角色（目标/参数排序已闭合）、导子塔、常数域以及 `DifferentialStructure` 的持久化/重放载荷仍未建。
- **请求契约（2026-11-10）**：`ProblemSpec.exactness` 与 `interpretation_requirement`、`VariableRoles.target_sort`/`parameter_sorts`、问题区域/`externalizable` 前提的稠密排序校验、以及 `problem_mismatch` 的 roles/interpretation/exactness 全绑定检查已建并接入。本批已闭合工作流片段内的 `externalizable` 正向路径（显式集经 `ProblemSpec`/`ExecutionRequest` 保留，`COMPLETED_CONDITIONAL` 只在全部开放条件都属于该集时派生）；同日后续批次已闭合系数范围/值域字段（`ValueDomain`/`DomainRequirement`/`AlgebraRequest.coefficient_domain`/`value_domain` 与 problem/algebra 双向绑定）；仍未建：跨 frame 前提弱化、注册 `Covers` 规格/checker、嵌入/实嵌入、参数关系、结果语言覆盖、完整绑定位置与 binder-aware 角色、近似 checker 与一般完备性；一般半代数/离散区域代数、`Guarded`/`Piecewise` 分支局部语义、binder-aware premises 与声明函数定义域亦未建。本切片不声称完整 S1。`CoversCertificate` 是函数延拓内部证书，没有独立 `Covers` judgment；注册 `Covers` 规格/checker 属未来 K1/S1。
- **否证**：目前只识别可见闭合判断中的结构否定；等价的否定形式、多原子条件否证与一般一阶推理未接入。`Blocked` 只表达当前不能应用，不表达结论为假。
- **工作流历史载荷**：已删除无消费者的 `Blocker.next_action`、`TaskRecord.created_by_event`、`ExecutionAttempt.event`、`Event.note`、`VerificationLink.detail`、`FunctionParameter.name`；`Event.judgments` 由 `Workspace._append_revision` 的发布前一致性检查消费，`Revision.label` 由 `Session.undo`/`redo` 显示，`VerificationLink.condition` 由 `Session._report` 与条件结果输出消费。`Event` 已记录 input revision/frame/输入对象/参数快照/执行报告/output revision；`Revision` 已记录 world/producing event/focus、task/candidate 快照、`Occurrence.expected` 与 `object_names`；`Event` 已记录 `actor_kind`/`operation_version`；`Session.history()` 与 REPL `history` 消费这些字段。`function_extension` 构造关系已接入；仍缺多结果槽的一般 `ConstructionRelation`、`verification_refs`/`explanation_ref` 与完整持久化/重放载荷。
- **前端**：已覆盖纵线：`expr`/`declare`/`define`/`diff`/`integrate`/`hermite`/`solve`/`gcd`/`resultant`/`specialize`/`assume`/`candidates`/`check`/`edit`/`decide`/`history`/`undo`/`redo`；`declare`/`define` 通过 `FrameStore.create` 建立子 frame 并记录 `Declare`/`Define` 事件，无 kernel judgment；`candidates` 显示 verification/applicability/coverage/language 四维；未注册 label 的 workspace 对象显示为 `v{version}`，`Session.focus` 不再回退到最后可见表达式，conditional 结果统一显示条件/义务。`@LABEL` 已支持嵌入公式并解析为当前 revision 的不可变对象快照；`object @LABEL` 显示 `Artifact`/`ObjectVersion` 视图；`Session._decide` 把工作区的 `ValueError` 统一翻译为 `SessionError`，REPL 不会因为不可见或未检查候选而终止。仍无隐式标量默认、持久化；REPL 默认装配初等片段，参数化入口仍在 Python API；`specialize` 只接受精确有理字面量；`gcd`/`resultant` 需要两个显式对象标签；重定义/遮蔽仍按当前 frame 的重复名拒绝；编辑候选保持无证书 unchecked，手动证据录入未实现。
- **工作流与工程终态**：函数对象、失败事务回滚、Task/Candidate 状态与 revision 快照、执行尝试/取消、revision branch/merge/switch（含跨 frame 历史视图合并）、多动作事务、结构化 decomposition、有限集合结果、手动问题定义/运行、出现位置、改写/换元、构造图、两情形分裂/历史合并/`merge_case_conclusion`、分支最新后代合并与分支 premises、`function_extension` 构造关系、同一 source 的多泛结果家族及其 revision/branch/merge 快照已接入；带局部声明/定义或未决义务的分支、超过两情形的证明合并、一般积分家族特化、手动证据录入、多结果槽的一般构造关系、完整 Event 分类（`verification_refs`/`explanation_ref`）、覆盖派生、方程变换、持久化/重放/并发仍未建。
- **固定问题比较与区域绑定排序（2026-11-10）**：`workspace._same_problem` 已精确比较 `ProblemSpec.exactness`/`interpretation_requirement`/`domain_requirement`，`run_task` 不会接受重建出不同答案标准、解释要求或系数/值域的执行；`AlgebraView.region_bindings` 对与源自由符号同 `SymbolId` 的条目要求排序等于源 `BindingView`，拒绝用显式绑定覆盖已知源符号的排序，后代 frame 额外坐标仍由桥声明排序。这两项不改变本节其余开放项：跨 frame 前提弱化、注册 `Covers` 规格/checker、嵌入/实嵌入、参数关系、结果语言覆盖、完整绑定位置与 binder-aware 角色、近似 checker、一般半代数/离散区域代数与一般完备性仍未建。

### 5.4 下一批

按依赖与风险：

1. 当前 polynomial/rational/function 请求切片已具备下列闭合件，但请求契约整体尚未闭合：`VariableRoles` 已建（world 与 target/parameter 排序已绑定）并与 `AlgebraRequest` 共享，coverage/parameter_mode/result_language 已贯通，`define_problem` 已执行准入；`TypedExpr` 与定型 `ProblemSpec.inputs`、`AlgebraView` 与 `to_view`/`render`/`typed_view` 已接入；`parameter_schema`/`capability_requirements` 已接入所有注册操作，中央 `OperationInput` 联合已删除；`ExecutionRequest` 已绑定固定问题、匹配的 `AlgebraRequest`、frame、policy/budget；`ValidatedCommitBatch`/`validate_commit`/`publish_commit` 已把提交拆成验证与发布两阶段并修复 seal 伪造；`BasisRegistry` 已消费 `BasisRef` 的 name/kind/version/digest/world；`Unverified` 已携带结构化 missing/conditions；`ResultSchema` 已声明并检查结果形状；`Blocker` 已携带 target/budget；`CheckRequest` 已携带候选数学数据、`VerificationContext`（decision/supports/budget）与 structured 组件；`CheckerBinding.candidate_role` 已替代 operation 名候选选择；`Verdict`/`decide` 已接入；`AlgebraView.source_domain`/`valid_on`、`ConversionWitness` 与有理桥已接入并由 Hermite 消费；operation/service/checker 已迁移，旧 polynomial bridge API 已删除。区域化 Hermite 验证已闭合；`AxiomRef`/`BudgetTicket`/`Verdict`/`@LABEL` 与 world/frame 内容 digest 已闭合；`AlgebraService` 已建并接入局部消费者，`DefinednessService` 已闭合；`function_extension` 构造关系已闭合；`RegionSpec`/`RegionCertificate`/`DefinednessExactness` 与 `AlgebraView.definedness` 已闭合；`Proposition` 的结构定义性前提已由 `specialize`、函数 checker/extension、workspace 函数区域检查与区域证书消费，裸 Proposition 区域载荷本批以构造器拒绝部分条件保守处理；一般多结果槽 `ConstructionRelation`、`Artifact`/`ObjectVersion`、Event/Revision 完整载荷、声明函数定义域、`Guarded`/`Piecewise` 分支局部语义、binder-aware premises、一般偏函数定义域与持久化/重放仍属 K1/U1/E0；`ProblemSpec` 的系数范围/值域字段已闭合；`VariableRoles` 绑定位置与 binder-aware 角色、跨 frame 的 `externalizable` 前提弱化、注册 `Covers` 规格/checker、嵌入/实嵌入、参数关系、结果语言、一般半代数/离散区域代数、近似 checker 与一般完备性仍未闭合；`externalizable` 正向路径已在工作流片段闭合（请求显式集随固定问题进入 `ExecutionRequest`/候选/提交，`COMPLETED_CONDITIONAL` 仅由全部开放条件均属该集派生）。不能把本项写成整个请求契约已闭合。下一步按 W1/W2 推进。
2. W1 收尾：决定 A4 矩阵算法是建立矩阵表达式桥后注册操作，还是保持公开低层 API；把分支结论合并回基 frame 的数学 case 证明（U1-c）接入 kernel；继续为 A1 的低层算法寻找真实消费者。
3. W2 三条基线按依赖并行：I0 有理积分链（留数与对数部分）、G0 Buchberger、R0/R1 实代数链（R0 已完成开区间平方自由实根计数首片，下一段是根界、隔离与重数）；A2/A3 因式分解、多元 gcd/分解、一般代数扩张按需推进。
4. W3 随基线推进：G1/G2、C0/C1、D0/D1、F0/F1；同步 K1/U1。
5. W4/W5 按 roadmap §8–§9 的里程碑闭合与扩展路线推进。

### 5.5 审查未闭合项与测试状态

`red` 表示验收测试已写、当前实现应当失败；`blocked` 表示类型/API 尚不存在，不能写行为测试，也不建空壳测试。

| 未闭合项 | 级别 | 测试状态 |
|---|---|---|
| `VerificationContext` 的完整支持收集、片段级一致性 checker | P1 | `blocked`：`DecisionService`/`SupportsService`/`BudgetService`/`AlgebraService`/`DefinednessService`、`AxiomRef`、`LocalReceipt`/`RefutationReceipt`/`Verdict` 已建并接入；完整支持收集与片段级一致性 checker 未建 |
| `ConstructionRelation`、`verification_refs`/`explanation_ref` 与持久化/重放 | P1 | `blocked`：Event/Revision 输入输出/参数/作用域/输出 revision/focus、task/candidate 快照、`Occurrence.expected`、`Revision.object_names`、`Event.actor_kind`/`operation_version` 已建并由 `Session.history()` 消费；其余 Event/Revision 载荷、ConstructionRelation 与持久化/重放未建 |
| `World`/`Frame`/`Declaration`/`Definition`/`Hypothesis`/`DifferentialStructure` | P1 | `blocked`：`World`/`Frame`/`Declaration`/`Definition`/`Hypothesis` 已有稳定内容 digest 并由 `Revision.frame_digest`/`Event.frame_digest` 消费；`DifferentialStructure` 已作为 `AlgebraRequest.differential` 的请求局部载荷接入并由 differentiation/specialization 视图按对象同一性校验；其持久化/重放载荷以及嵌入/实嵌入仍未建 |
| `Artifact`/`ObjectVersion` 主存储、一般多结果槽 `ConstructionRelation` | P1 | `blocked`：`Artifact`/`ObjectVersion` 已作为现有对象记录的类型视图并由 `object` 命令消费；主存储迁移与多结果槽一般关系未建 |
| `Proposition` 定义性前提的剩余片段、`Guarded`、`ProblemSpec`/`FunctionValue` 区域迁移、结果语言覆盖 | P1/P2 | `blocked`：结构定义性前提已建（非正指数整数幂的 `Ne(base,0)`、和/积/比较/布尔连接词递归）并由 `RegionSpec` 证书、`AlgebraView`、`DefinednessService.covers`、`specialize`、函数 checker/extension 与 workspace 函数区域检查消费；裸 Proposition 区域载荷（`ProblemSpec.region`、`OperationRequest.region`、`FunctionValue`/`FunctionRepresentation` 区域、`MathematicalProposal` 区域）本批在构造器拒绝部分条件。声明函数定义域、`Guarded`/`Piecewise` 分支局部语义、binder-aware premises、一般偏函数定义域、`ProblemSpec`/`FunctionValue` 的 `RegionSpec` 迁移与结果语言覆盖未建 |
| `ResultSchema` 多语言/多形状、`FunctionValue` 多表示覆盖完整性 | P2 | `blocked`：当前显式拒绝多语言/多形状；`extend_function` 已要求并在 `FunctionEqualityChecker` 中独立重检 `CoversCertificate`（受限区域片段），但一般半代数区域与任意多表示覆盖完整性仍未建；本片段没有独立 `Covers(region, pieces)` Proposition/checker/operation，注册 `Covers` 规格/checker 属未来 K1/S1，且必须与真实发布消费者同批加入 |
| `OperationSpec.explanation_schema` | P2 | `blocked`：当前没有记录/渲染解释配方的消费者，未建空字段 |
| `Blocker` 子问题信息 | P1 | `blocked`：target/budget 已建并接线；独立 subproblem 字段未建（target 覆盖当前片段） |
| `ProblemSpec` 请求契约的剩余字段 | P1 | `blocked`：`exactness`/`interpretation_requirement`、`VariableRoles.target_sort`/`parameter_sorts`、问题区域/`externalizable` 稠密排序校验与 `problem_mismatch` 的 roles/interpretation/exactness 全绑定检查已闭合；`externalizable` 正向路径已在工作流片段闭合（`apply`/`_apply` 显式集经 `ProblemSpec`/`ExecutionRequest` 保留，`COMPLETED_CONDITIONAL` 只在全部开放条件都属于该集时派生）；系数范围/值域字段已闭合（`ValueDomain`/`DomainRequirement`/`AlgebraRequest.coefficient_domain`/`value_domain` 与 `ProblemBuilt`/`ExecutionRequest` 双向绑定）；`_same_problem` 现精确比较 `exactness`/`interpretation_requirement`/`domain_requirement`，`run_task` 拒绝重建出不同请求契约的执行；跨 frame 前提弱化、注册 `Covers` 规格/checker、嵌入/实嵌入、参数关系、结果语言、完整绑定位置与 binder-aware 角色、近似 checker 与一般完备性未建 |
| 一般积分家族特化与手动证据录入 | P1/P2 | `blocked`：`specialize` 当前只选择 correctness specification 为导子方向的家族；积分/其他方向家族返回结构化 `UNSUPPORTED`（`missing=derivative_family`），不实现通用家族特化。`Session._decide` 已把不可见/无证书候选翻译为 `SessionError` 并保持 REPL 继续；编辑候选仍为 unchecked，手动证据录入未建 |
| 嵌入/同态实现、混域消解、`AlgebraRequest` 嵌入字段 | P1 | `blocked`：`ConversionWitness.preserves_definedness` 已在 `AlgebraView.__post_init__`/`_issue_view` 发行与 `_admit_view_relation`/`typed_view` 准入边界消费，区域视图必须由保留定义性的 witness 支撑；解释与 witness kind 一致性已由 `_interpretation_witness_refusal` 在 `AlgebraView.__post_init__`/`_issue_view` 强制（`EMBEDDED` 拒绝 `HOMOMORPHISM`，`PARAMETER_FAMILY` 拒绝非 `REPRESENTATION_ISOMORPHISM`，`FORMAL` 保留三种 kind）；具体嵌入/同态桥、混域共同目标消解与请求嵌入字段未建 |

当前测试状态：`python -m pytest -q` → 1491 passed，0 failed。没有 `red` 验收测试；未闭合项均为上表 `blocked`。本批新增 R0 根计数首片：`tests/unit/test_real_roots.py`、`tests/unit/test_root_count.py`、`tests/property/test_real_root_properties.py` 覆盖 Sturm 余式递推、零点符号变差、平方自由/零多项式/正特征/非有序域拒绝、端点根、缩放不变性、区间可加性、独立链重建、checker 对证书链的逐环验证（缺失/多余/错误首项/非恒常尾项/异多项式链/零余式提前终止均 `InvalidEvidence`）、错误计数 `Refuted`、篡改证书/问题 `InvalidEvidence`、非常数端点 `Unverified(FRAGMENT)`、define_problem 四类 BLOCKED、run_task 拒绝与正向手动任务、无判断拒绝与 REPL 路径；该切片不声称完整 R0。本批同时闭合两个残余契约缺口：`workspace._same_problem` 精确比较 `ProblemSpec.exactness`/`interpretation_requirement`/`domain_requirement`，`run_task` 不会接受重建出不同请求契约的执行；`semantics.bridge._region_binding_refusal` 要求 `region_bindings` 中与源自由符号同 `SymbolId` 的条目排序等于源 `BindingView` 排序，拒绝把非稠密源坐标伪装成稠密坐标；这两项不声称完整 S1。本批 `externalizable` 正向路径已在工作流片段闭合：`apply`/`_apply` 的显式集替换 operation 内置集并随固定问题进入 `ExecutionRequest`、候选与提交，`run_task` 传递任务的集合，`_same_problem` 精确比较；`derive_task_state` 只在全部开放条件（链接条件与 kernel obligations）都属于该显式集时派生 `COMPLETED_CONDITIONAL`，无条件结果仍为 `COMPLETED`，否则为 `PARTIALLY_SOLVED`；`result_region` 是工作流条件，不是 kernel obligation。本批同时闭合系数范围/值域：`ProblemSpec.domain_requirement` 与 `AlgebraRequest.coefficient_domain`/`value_domain` 由 `ProblemBuilt`/`ExecutionRequest` 双向绑定，`problem_mismatch` 消费固定请求值。`CoversCertificate` 是函数延拓内部证书，由 `FunctionEqualityChecker` 独立重检；本片段没有独立 `Covers` judgment，注册 `Covers` 规格/checker 属未来 K1/S1。`Covers`/一般多表示覆盖、嵌入/实嵌入、参数关系、结果语言覆盖、完整绑定位置与 binder-aware 角色、跨 frame 前提弱化、近似 checker 与一般完备性仍未闭合；注册 `Covers` 规格/checker 仍属未来 K1/S1（当前 `CoversCertificate` 只是函数延拓内部证书）；一般半代数/离散区域代数、`Guarded`/`Piecewise` 分支局部语义、binder-aware premises 与声明函数定义域仍未闭合；本批不声称完整 S1。本轮修复三处回归：默认初等入口的积分改用同批注册的 `calculus.derivative.polynomial`（`differentiate` 仍用初等 checker）；同一 source 的多个 `GenericResult` 按记录保留，`specialize` 只选择导子方向家族并对积分家族结构化拒绝；`Session._decide` 将工作区 `ValueError` 翻译为 `SessionError` 且 REPL 继续。一般积分家族特化与手动证据录入仍未建；R0 的根隔离/根界/重数/实代数数与 R1/CAD 仍未建。
