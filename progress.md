# Progress

当前实现状态与下一步。设计裁定以 `cas_v5_arch.md` 为准，工程纪律以 `AGENTS.md` 为准。
本文只记状态，不重复设计。

**文档语言约定：本文档与 `AGENTS.md`、`cas_v5_arch.md` 一律用中文；源码（`.py` / `.dsl`）与测试源码用英文。**

## 当前阶段：v5 彻底重构（进行中）

v5 的新层（foundation / syntax / language / algebra / semantics / kernel / 求导 /
workflow / runtime / frontend）已完整，具备正式验收；v4 遗留代码树已全部删除。
全库 `mypy --strict cas`、`ruff`、`compileall` 与测试均转绿。当前数学能力是 Q[x]、
形式参数系数 Q[a…][x] 上的单变量多项式求导，以及由 data-only 声明装配的初等函数
片段（无条件定律可用，条件定律诚实拒答）；其余数学层将按 v5 架构重新落地。
内核现已具备显式的 `CheckerSpec`/`BasisRef` 信任元数据、frame 一致性状态，以及
`Blocked` 适用性分支。

### 已完成

| 层 | 内容 |
|---|---|
| 文档 | v4 架构文档删除；不可判定协议、根与序可判定性地图、Unknown 三出口并入 v5 §11.8–§11.10 |
| 纪律 | `AGENTS.md` 重写：只允许类型/行为/性质三类验收，禁止关键字与 AST 名字门禁 |
| foundation | `ids.py`：13 个互不混用的身份类型 + 单调 issuer |
| syntax | `term.py`：不可变项模型（字面量/符号引用/绑定变量/应用/binder/Quote），结构相等、hash、序，无介入、无 AC 排序、无化简 |
| syntax | `binding.py`：`shift` / `instantiate` / `abstract` / `substitute_free` / `free_symbols` / `well_scoped`，捕获规避，Quote 完全惰性 |
| language | `sorts.py`：Sort 封闭层次、数值嵌入塔、`join`、`is_ordered`（sort ≠ 表示） |
| language | `signatures.py`：结构 head 封闭集合、Arity、BindingSignature（参数 sort 与结果）、按 SymbolId 绑定的 LanguageSignature |
| language | `typing.py`：`Typed / NeedsDeclaration / Unsupported / IllTyped`；binder 局部索引环境与函数值/值 binder 定型 |
| language | `declarations.py`：唯一的 data-only 声明 DSL（常数/operator/函数/binder/导数定律与声明表达式）、文本/文件加载、带行号的拒答、`build_language` 装配 |
| language | `propositions.py`：`Proposition` 只能经 `check` 发行，必须良作用域、命题 sort，并携带 `MeaningKey` |
| language | `problems.py`：ProblemSpec 固定操作、输入、目标、区域、结果语言、参数模式、覆盖要求 |
| language | `decisions.py`：四类未决理由的封闭词表（FRAGMENT / GUARDED / UNDECIDABLE / BUDGET），供 checker outcome 与候选拒答消费 |
| algebra | `protocols.py`：Ring / Field / Euclidean / Ordered / IntegerEmbedding / RationalEmbedding / Derivation 分离，无默认零导子 |
| algebra | `parents.py`：ParentSpec 结构身份 + ParentRegistry（kind、base 有无、生成元与表示选项必须和结构一致；同描述一个 id，不同结构拒绝） |
| algebra | `rationals.py` / `integers.py`：Q 为有序域；Z 为欧几里得整环，gcd 非负归一 |
| algebra | `polynomial.py`：K[x₁…xₙ]，元素私有封印、跨环拒绝、系数环判等权威、形式偏导；一元域上才有 divmod/gcd |
| algebra | `rational.py`：K(x) 既约分式域，分母非零且首一，分子分母互素；形式导数与求逆 |
| semantics | `symbols.py` / `frames.py`：符号表；不可变 World/Frame，祖先可见、新鲜性、逃逸检查、别名环拒绝 |
| semantics | `definitions.py`：唯一自动代换通道，展开到不动点，预算出口 `DefinitionError` |
| semantics | `bridge.py`：Term ↔ 多项式显式片段；片段外返回 None，不猜表示 |
| semantics | `request.py`：`AlgebraRequest` 固定系数 parent、参数环、参数、目标与参数模式；角色属于请求，不属于符号 |
| semantics | `bridge.py`：项 ↔ 多项式元素；参数桥把参数映射到系数环生成元、目标映射到外层生成元 |
| semantics | `specialization.py`：`GenericResult`（有效区域/异常集/正确性规格/覆盖声明）、精确点 `Specialization`、条件求值与特化结果 |
| semantics | `services.py`：注入的 `DerivativeService` 协议与 `Derived / Unsupported / Invalid` 结果，工作流不知道候选来自哪个片段 |
| semantics | `conditions.py`：精确 ground 求值、三值逻辑、`and_all` 的线性边界规范化/矛盾检测/结构去重，以及受限 `implies`/`equivalent`；参数特化与初等条件共用 |
| semantics | `differential.py`：`DifferentialStructure` 把 parent 与选定导子显式配对 |
| semantics | `elaborate.py`：先展开别名再定型/发行命题，存下的命题 alias-free |
| kernel | `model.py` / `evidence.py`：Judgment / Obligation / InferenceRecord / Discharge / Applicability；`CheckerSpec`；frame 一致性状态；Checker 协议与四种 outcome |
| kernel | `trust.py`：`BasisRef` / `BasisKind` / `CertificateSchema`；schema 记录证书类型与节点数/深度预算，`commit` 在 checker 前检查 |
| kernel | `store.py`：唯一原子写入 `_publish`（只由 commit 调用）；support 传递闭包；适用性查询；按结构否定查找否证；一致性查询 |
| kernel | `commit.py`：实际验证规格必须等于请求；checker 准入的 problem/specification 种类；basis 写入推理记录；继承义务 + 新义务受同一 ConditionPolicy；已否定条件拒绝；证明与 discharge 同一批原子发行；已清偿义务不重复放电 |
| operations | `protocols.py` / `registry.py`：开放 `OperationSpec`、`OperationRequest`、`MathematicalProposal`、`CheckerBinding` 与冻结注册表；workflow 只通过注册表应用操作 |
| operations | 现有操作：`differentiation/operation.py`、`specialization_operation.py`；数学服务移到 `differentiation/services.py`，runtime 只装配 |
| kernel | `context_rules.py`：`HypothesisChecker` 只把 frame 中可见的精确假设命题验证为 `H ⊢ H` |
| kernel | `consistency.py`：核心矛盾规则（可见假设的 `H` 与 `not H`，或假设 `false`）与 `assess_consistency`；没有矛盾只保持 `Unassessed` |
| kernel | `condition_checker.py` / `applicability.py`：checker 与 resolver 分家；`ConditionChecker` 从前提判断证明条件并只上报实际使用的前提，检查所有命题在请求 frame 可读；`resolve_applicability` 在同一 commit 批次中发行证明与 discharge，未决保持 `Conditional`，被否定返回 `Blocked` |
| math | `differentiation/specification.py`：`HasDerivative(region, f, x, g)` 词表与解析 |
| math | `differentiation/verify.py`：系数级独立验证，不调用环的 `derivative` |
| math | `differentiation/checker.py`：证书逐项匹配；只有全域可证；片段外 Unverified；错误候选 Refuted 带见证 |
| math | `differentiation/elementary_checker.py`：要求 `Derivation` 规则实例树，逐节点重建并比对；接受结构相同或被证明等价的区域，否则 Unverified（不伪造否证） |
| math | `elementary/declarations.py` + `declarations.dsl`：data-only 常数/一元函数/定义域/导数定律、BASIS 与 USER_AXIOM 来源、精确有理 DSL 表达式；源文件名称与 SHA-256 摘要参与 `BasisRef` 装配 |
| math | `differentiation/elementary.py` / `derivation.py`：候选搜索 + 唯一的局部规则实例实现；同时计算可微区域与定义域，空区域、未声明依赖、负幂诚实拒答 |
| workflow | `records.py` / `workspace.py`：表达式对象、候选、验证关联、事件、revision；intake 不发行判断；undo/redo 只移视图；参数族记录与精确点特化；求导候选经注入服务；条件结果记录受限区域；假设创建子 frame，操作使用当前 revision frame |
| runtime | `bootstrap.py`：显式装配 Q[x]、Q[a…][x]、Q[x] 特化视图与初等函数片段；`bootstrap_parameterized` 固定参数角色，`bootstrap_elementary` 从声明文件装配函数与定律 |
| frontend | `parser.py`：文本 → Term，名称解析到稳定 SymbolId，结构 head 驱动，无化简、无数学语义 |
| frontend | `pprint.py`：可读形式 + 全应用 source 形式；source 对可解析项逐项往返，binder/自由索引/非符号算子显式拒答 |
| frontend | `session.py`：对象标签、焦点、intake/assume/diff/specialize/show/list/undo/redo；只经 Workspace 与 kernel；旧 `cas/api.py` 已删除，Session 是唯一前端门面 |
| frontend | `repl.py`：逐行 REPL，仅分派与打印；默认装配初等函数片段；条件结果显示受限区域；前端错误报告，诚实拒答仍是结果 |

### 参数域与系数域

参数符号与目标变量的角色现在由 `AlgebraRequest` 显式固定，而不是由符号名或全局域猜测：

- `AlgebraRequest`（`semantics/request.py`）携带系数 parent、参数环、参数元组、目标、
  `ParameterMode` 与 `Interpretation`；目标与参数必须不相交，参数环必须扩展系数
  parent，且其生成元必须恰好是声明的参数。角色是请求局部的：同一个符号可以在另一个
  请求中成为目标。
- `bootstrap_parameterized(("a",))` 装配 Q[a][x]：`a` 是系数参数，`x` 是目标；
  `ParameterPolynomialBridge` 把参数映射到系数环生成元、目标映射到外层生成元。
  `DerivativeChecker` 与 `Workspace` 使用同一个桥，因此验证与候选计算看到同一
  角色划分。
- 已支持 `a*x^2 → 2*a*x`、参数常量 `a → 0` 的验证；`a` 不作为求导目标
  （Workspace 拒绝），`1/a` 在多项式片段外诚实拒答。问题规格记录请求的参数模式。
- 尚未实现：参数关系（多项式等式/不等式/整数约束）、参数分支，以及会真正产生
  非空异常集的局部化算法；当前多项式求导不引入分母或分支。

### 参数特化、局部化与覆盖

- `semantics/specialization.py` 定义 `GenericResult`：结果、`valid_on`、异常集、
  正确性规格与 `CoverageClaim`（`SPECIFIED` / `GENERIC` / `PARTIAL` /
  `ALL_VALUES`）。`assemble` 从 `ParameterMode` 与有效性推导覆盖；声称
  `ALL_VALUES` 时构造期拒绝非空异常集或非 `true` 的有效区域。
- `Specialization` 要求请求的**全部**参数且只接受精确有理值。语义特化不是
  Q(a)→Q 的域同态：它先在点上求值有效区域，再逐个检查异常集；条件不可判定或命中
  异常即返回 `NeedsRecomputation`，绝不把未决条件当成成立；落在有效区域外返回
  `OutsideValidity`。
- 参数模式的默认值改为 `AllParameterValues`（符合 §8.2）；多项式求导无分母与分支，
  其 `GenericResult` 为无条件，覆盖 `ALL_VALUES`。显式传
  `parameter_mode=GENERIC_PARAMETERS` 可只声明形式族；`SPECIFIED_VALUES` 在形式
  参数运行时被拒绝。
- `bootstrap_parameterized` 额外装配 Q[x] 特化视图：独立的 parent、导子、桥与
  checker（id 为 `calculus.derivative.specialized`），与参数族 checker 同时注册在
  同一冻结 registry 中。
- `Workspace.differentiate` 为已验证的参数族记录 `GenericResult`；
  `Workspace.specialize` 先做语义特化，能代入时走泛参数公式，否则回到原问题在
  Q[x] 中重算；两条路径都把源与候选经 Q[x] 桥规范化并用独立 checker 复核后才提交。
  特化失败（无效点、缺失/多余参数、片段外）不写账本。
- 前端命令 `specialize [@LABEL] a=VALUE ...`：只接受精确有理字面量，缺失、重复、
  未知参数或非字面量值都是前端拒答；非参数化运行时返回 `unsupported`。
- 测试覆盖：语义层的有效区域/异常集/未决条件/覆盖声明；workflow 的泛公式路径、
  重算路径、伪造候选被否证、可见性与无写入拒答；端到端的多次特化与独立 checker
  记录；固定种子的“特化与求导可交换”性质（100 组随机多项式与有理点）。
- 尚未实现：参数关系与分支、会生成异常集的真实局部化算法；当前特化点只支持精确
  有理值，实代数点尚未接入。

### 绑定与声明 DSL（首个切片）

- `BindingSignature` 现在可以声明每个被绑定变量的 sort 与结果：`result=None` 表示函数值
  binder，定型为 `FunctionSort(parameter_sorts, body_sort)`；具体结果表示值 binder，
  要求 body sort 嵌入结果。
- 定型器新增局部绑定环境：`BoundVar` 经 `SortEnvironment.bound_sort` 取得 sort；嵌套
  binder 会按内层 arity 平移外层索引；注解在**外层**环境定型；缺失声明、arity 不匹配、
  越界索引、未声明参数 sort、body sort 不嵌入都分别诚实返回。
- `declarations.py` 提供 data-only DSL：
  `operator Sin (Real) -> Real`、`binder Lambda (Real) -> function`、
  `binder Integral (Real, Rational) -> Real`。支持注释、空行、文件加载、行号错误、
  重名与结构 head 名拒绝；`build_language` 把声明装成 `LanguageSignature`。
- 测试覆盖 lambda/Pair/Integral binder、嵌套索引、注解外层语义、FrameSorts 集成，
  以及 DSL 的装载、建语言、声明算子定型、错误行号与拒答。
- 尚未实现：注解驱动的参数 sort（当前参数 sort 来自声明）、量化/全称引入、binder 的
  前端语法与 source 形式、导数定律/定义域/别名等其余 DSL 声明。

### 初等函数片段与条件区域

- `math/elementary/declarations.dsl` 是 data-only 的 v4 旧文件替换：声明常数、一元函数、
  函数定义域与导数定律。示例：`sin`/`cos`/`exp` 为无条件定律，`sqrt`/`log` 的定律
  和定义域带条件。DSL 有自己的精确表达式解析器，不依赖会话符号表。
- `LawOrigin.BASIS` / `USER_AXIOM` 记录定律来源；装配器只把标准库文件作为 basis
  准入，用户公理来源的定律保留但不会被自动使用。尚无完整的 `BasisRef` 版本/摘要记录。
- `build_elementary` 把名称固定为稳定 `SymbolId`，生成 `OperatorSignature`，并拒绝
  重名、保留名、未知名称/函数、错误 arity、非数值指数、重复定律与非法 law 参数。
  无条件定律还必须满足：函数本身无定义域条件、定律无 guard、定律体只调用全定义函数
  且不含负幂；否则在装配期拒绝。
- `semantics/conditions.py` 提供精确 ground 求值（有理数、比较、And/Or/Not/Implies）、
  条件规范化与受限蕴含/等价判定：一原子线性比较化成边界，重叠边界取最强，矛盾
  边界化为 `false`，冗余不等号被删除；未知原子、多原子与非线性关系保持未决。
  参数特化与初等条件共用该模块，原先的私有求值器已删除。
- `differentiation/elementary.py` 与 `derivation.py` 在求导的同时计算
  `condition`（可微区域）与 `defined`（定义域）：函数定义域和定律条件都实例化到实际
  参数；内层导数为 0 时保留其条件（因此内层不可微的点不会被误当成可微；
  `sqrt(0)` 的导数 0 仍是无条件结果）；指数 0
  要求底数有定义且非零（`x^0` 的区域是 `x != 0`，`0^0` 未定义）。区域为空时拒答。
- `elementary_checker.py` 不再要求全域：它逐节点重建 `Derivation` 规则实例，
  并接受结构相同或 `equivalent` 证明等价的区域；区域更弱/不同或候选不同都返回
  `Unverified`，不伪装成 `Refuted`。`sqrt(x)` 的 `x >= 0 and x > 0` 现在规范化为
  `x > 0`。
- 工作流新增 `OperationStatus.CONDITIONAL`、`OperationResult.region` 与
  `VerificationLink.condition`；候选 `ProblemSpec.region` 记录受限区域。会话显示
  `verified on <region> @LABEL: …`。kernel judgment 本身是在该区域上无条件成立的
  规格，不是把全域结论挂一条说明；kernel 义务清偿留给未来的算法前提。
- `semantics/services.py` 引入注入的 `DerivativeService`；Q[x] 与参数化运行时使用
  多项式适配器，初等运行时使用符号适配器。参数特化路径保持不变。
- `bootstrap_elementary()` 从声明文件装配函数、常数、签名、frame、elementary checker
  与 Q[x] 子片段的代数视图；默认 REPL 已切换到该运行时。
- 测试覆盖：DSL 装载/装配/拒答、定义域与条件、basis 与用户公理、候选生成、
  链式/乘积/幂规则、区域计算、ground 折叠、线性边界规范化、矛盾检测、
  受限蕴含/等价、checker 的区域/候选校验、条件结果的 workflow 字段与会话显示、
  随机多项式与随机条件表达式的性质验收。
- 尚未实现：kernel 义务/`resolve_applicability` 的自动清偿；一般的一阶蕴含/等价
  （当前只覆盖单原子线性边界与受限 Or/Not）；多原子与非线性关系不做猜测；
  完整 `BasisRef`、别名/角色、非一元函数、负幂/分式与更多初等函数；初等表达式
  相等判定。

### 假设、条件检查与适用性（基础）

- `kernel/context_rules.py` 的 `HypothesisChecker` 实现核心规则 `Γ,H ⊢ H`：结论必须
  是提交 frame 中可见的**精确**假设命题（MeaningKey 参与比较），不接受同文本但不同
  意义的命题。假设本身通过 frame 扩展引入，不先把 H 提交到父 frame。
- `Workspace.assume` 在当前 frame 发行命题，创建包含该假设的子 frame，经
  `HypothesisChecker` 提交假设 Judgment，并创建携带子 frame 的新 revision；
  `undo`/`redo` 连同 frame 一起移动，账本不回滚。
- 求导与特化现在在**当前 revision frame** 中发行规格与 Judgment，而不是源对象的
  创建 frame；源对象的 frame 必须是当前 frame 的祖先。这样假设可以在后续操作中
  生效，旧对象仍然可见。
- `kernel/applicability.py`：
  - `ConditionChecker`（`logic.condition`）只用提交方提供的前提判断，通过受限
    `implies` 证明条件，并贪心删除未使用前提后上报 `used_premises`；未决条件返回
    `Unverified(GUARDED)`，不伪造否证。
  - `resolve_applicability` 读取 `inspect_applicability` 的未决义务，从当前 frame
    可见且自身 applicable 的 Judgment 中收集前提，并在**同一个 commit 批次**中
    发行条件证明 Judgment 与 discharge；发布前完成循环、作用域与前提闭合检查。
    证明失败、前提不足或超过预算时保持 `Conditional`。
  - 解析只排除目标 Judgment 自身；使用条件判断的前提会继承其（已闭合的）条件。
  - 保守限制：一个带未闭合义务的证明不能在同一批次中放电；前提必须已经 applicable。
- `KernelStore.judgments_visible` 提供当前 frame 可见判断的只读查询。
- 前端新增 `assume FORMULA`，只接受可整理的命题；成功后显示 `assumed: …`。
- 测试覆盖：假设的精确性与意义环境、frame 子链、undo/redo、当前 frame 操作、
  条件检查与 used_premises 最小化、更强前提放电、前提不足保持 Conditional、
  越界与无候选情形，以及证明+discharge 的单批原子发布与失败零写入。
- 尚未实现：一般一阶逻辑的一致性判定；解析器没有预算对象，只用前提数量上限保守
  停止；否证目前只识别结构否定，不做等价变形后的否定。

### 一致性与信任元数据（基础）

- `kernel/trust.py` 集中信任记录：`BasisRef`（名称、种类、版本、世界作用域、
  内容摘要）与 `CertificateSchema`（证书类型、节点数/深度预算）。frame 一致性
  只有 `Unassessed` 与 `Inconsistent(witness, detail)`；片段级一致性需要可验证的
  checker，当前不提供记录入口，避免把任意判断当成一致性证明。
- `kernel/evidence.py` 的注册项改为 `CheckerSpec`：绑定 checker、证书 schema、
  accepted problem kinds、accepted specification kinds 与 trusted dependencies。
  `CheckerRegistry` 只接受 spec，并校验 key/id 一致、种类非空、依赖不重复。
  `CommitProposal` 必须声明 problem/specification 种类；未准入的组合在 checker
  运行前被拒绝。`InferenceRecord.basis` 记录本次推理实际使用的可信依赖。
- `build_elementary` 可接收 `BasisRef`；装配器把声明文件名称与 SHA-256 摘要写入
  basis，并拒绝摘要不匹配或没有摘要的来源。初等 checker 的 spec 携带该 basis，
  因此每条初等求导推理都能追溯它使用的标准库依据。
- `kernel/consistency.py` 提供核心矛盾规则：只证明 `false`，依据是 frame 链上
  可见假设中的 `H` 与 `not H`，或直接假设 `false`。`assess_consistency` 尝试
  发行 `false` 并记录 `Inconsistent`；找不到矛盾、checker 缺失或结果未决都保持
  原状态。祖先的不一致会被后代继承。
- `KernelStore` 拒绝为不一致 frame（含后代）发行任何判断；`Workspace.assume`
  在提交假设后自动评估，并在矛盾时返回 `INVALID`、记录矛盾判断到事件中；
  `diff`/`specialize` 在不一致 frame 中停止且不写账本。撤销回到一致 frame 后
  操作恢复；账本不回滚。
- 适用性新增 `Blocked(refuted, unresolved, witnesses)`：由 `refutation_of` 在
  可见闭合判断中查找义务命题的结构否定；条件证明未闭合时不算否证。`commit` 对
  已否定条件返回 `Rejected`，用 `refuted_conditions` 与结论否证 `refutation`
  区分；`resolve_applicability` 遇到 `Blocked` 直接返回，不尝试放电。
- 测试覆盖：spec 的字段/种类/重复依赖校验；basis 摘要匹配与跨世界拒绝；推理记录
  basis；`CheckerSpec` 未准入种类拒绝；矛盾规则的互补/无关/false 假设；workflow
  的矛盾假设、继承、停止、撤销恢复与会话输出；`Blocked` 的单/多义务、条件否证
  不算否证、祖先可见与兄弟不可见；`resolve_applicability` 不为被否定义务写 discharge。
- 证书 schema 现在同时执行类型匹配与节点数/深度预算；预算在 checker 运行前拒绝
  超限或不可测量的证书，结构细节仍由 checker 的 `InvalidEvidence` 负责。
- 尚未实现：`AxiomRef` / `LocalReceipt` 的完整分类；一般一阶一致性判定、片段级
  一致性 checker 与等价变形后的否证。

### 操作协议、依赖倒置与域边界（本轮）

- 新增 `cas/operations/`：`OperationSpec`、`OperationRequest`、`MathematicalProposal`、
  `CheckerBinding`、`ProposalOutcome` 与冻结 `OperationRegistry`。操作是数据，
  workflow 不再按操作名分派数学。
- `differentiate` 与 `specialize` 的实现移出 workflow：求导构造器在
  `math/calculus/differentiation/operation.py`，参数特化构造器在
  `specialization_operation.py`；候选/证书服务移到 `services.py`，runtime 只负责装配。
- workflow 新增通用 `Workspace.apply(operation_id, inputs, ...)` 与
  `OperationResult`；求导/特化只是薄适配器。workflow 现在不再导入具体 math。
- 导数证书统一为 `differentiation/certificate.py` 的 `DerivativeCertificate`；
  初等证书额外携带 `Derivation` 规则实例树。候选器搜索并生成树，checker 用
  `derivation.py` 的唯一局部规则逐节点重建比对；删除 `elementary_verify.py`
  的第二套递归搜索。多项式 checker 仍有独立的系数级验证。
- 删除 `KernelStore.discharge` 第二条写路径；证明与 discharge 只能通过同一个
  `commit` 批次发行，已清偿义务重复放电会被拒绝。
- 初等定义域/定律条件组合模块改名为 `math/elementary/law_conditions.py`，与
  `semantics/conditions.py` 的条件判定职责分开。
- `Ring` 增加总成员检查；ℚ/ℤ/K[x]/K(x) 实现 `contains`；新增
  `AlgebraValue(parent, representation)` 与 `Parent.value`，求导服务在边界使用它。
- 信任记录移到 `kernel/trust.py`；`CertificateSchema` 记录实际证书类型与节点数/
  深度预算，`commit` 在 checker 前强制类型与预算；`CheckerSpec` 校验 trusted
  dependency 的 world 与当前 world 一致。
- 义务按 `(frame, proposition)` 复用：相同条件不再重复创建 obligation，已清偿的
  条件可被后续判断直接复用。
- `0^0` 不再由 Python 决定：ground 求值返回未决，零次幂的导数条件要求底数非零。
- 矛盾规则用 ground 真值识别 `not true` 等闭合假假设，而不仅是结构 `false`。
- 参数环改用 `GeneratorRing` 能力检查，不再只对 `PolynomialRing` 特判；单项式序
  成为 `PolynomialRing` 的显式参数，`ParentSpec.options` 必须完整声明 ring 的
  表示选项，缺项、多项或值不符都拒绝。
- `AGENTS.md` 重写为一份去重的红线清单；自动化代理的操作底线并入“改动流程”。
- 声明 DSL 统一：`language/declarations.py` 现在解析常数/operator/函数/binder/
  导数定律与声明表达式；`math/elementary/declarations.py` 只负责准入与建库，
  删除第二套 tokenizer/parser/AST。
- 三个 bootstrap 共用 `_start`、`_world`、`_derivative_spec`、`_q_coefficient`、
  `_q_polynomial` 装配助手；elementary 也从共享声明集构建。
- `FrameStore.readable` / `agree_in` 把跨 frame 弱化规则变成显式前置条件；
  `refutation_of`、矛盾规则与条件 checker 在比较裸 Term 前消费该规则。
- `_normalize_not` 只对全定义表达式把 `not` 推入比较；含未声明函数的比较保持未决。
- `terms.times` 不再静默丢弃零系数旁的符号因子；乘积法则跳过零导数和项时，
  其定义性仍由结果条件携带。
- `ProblemSpec` 的 target/parameter_mode 现在由操作持有的 `AlgebraRequest` 派生，
  不再由操作独立选择；边界写入 `problems.py` 与 `request.py` 的模块契约。
- `ALL_VALUES` 覆盖检查收敛到 `semantics/specialization.py` 的唯一校验函数；
  数据记录没有证明器，因此只接受规范 `true` 区域，保守但明确。
- `ConditionChecker` 与 `resolve_applicability` 分家；`Math` 只依赖
  `kernel/trust.py` 与 checker 接口，不再从 `kernel/model.py` 取信任记录。
- 新增规则实例证书、证书预算、跨 frame 可读性、零因子、Not 偏函数、完整
  `ParentSpec` 选项与 `ProblemSpec`/`AlgebraRequest` 边界测试；P0 零内层条件与
  BASIS 准入回归测试保留。
- 复审又发现并修掉：`terms.power` 曾把 `x^0` 折叠为 1（现在保留显式零次幂，
  一阶幂规则直接返回内层导数）；`_is_total` 曾把零次幂当作全定义（现在只承认
  正整数幂）；`ProblemSpec.coverage` 原先无人消费（`MathematicalProposal` 现在
  声明 `answer_coverage`，workflow 在 commit 前要求它与请求一致，并拒绝尚未实现
  的集合覆盖）；未实现的 `externalizable` 与非 `EXPRESSION` 结果语言现在被
  workflow 明确拒答，而不是静默忽略。
- 跨 frame 复审又收紧：`SymbolId` 在整个 FrameStore 内唯一，兄弟 frame 不能
  重复引入同一符号；不存在的 frame 不再让可见性查询抛异常；hypothesis 的项
  若引用无关 frame 的局部符号会在构造期拒绝。
- 操作/问题协议补上不变量：`ProblemSpec` 的字段种类、`OperationRequest` 的输入
  与参数种类、`CommitProposal` 的 policy/种类、`CheckRequest`/checker outcome
  的载荷、可信记录的 kind 与 types 都在构造边界检查；workflow 还要求固定问题
  的 inputs/target 与请求一致，并拒绝当前 frame 不可读的 region。
- 删除无生产消费者的 `ElementaryLibrary.admissible_law`、
  `DerivativeLaw.is_unconditional` 与 `RationalInput`；多项式环构造期检查系数
  结构与单项式序类型。条件定律体调用的声明函数定义域现在并入结果区域；
  体内部的非零要求仍作为受信 basis 的承诺写入 `law_conditions.py` 文档。
- 重复实现收口：两个 polynomial bridge 共用同一项转换器；求导/特化共用问题
  构造与 `HasDerivative` 发行；两个 checker 共用证书匹配；三处结构 head 构造
  统一为 `LanguageSignature.head_term`；比较 head 集合、解析/打印拼写与精确
  幂/精确有理映射各只有一份；区间矛盾判定不再在 `_interval_terms` 重抄。
- 上一轮复审遗留的未接线/构造绕过项已收口：
  - 删除没有 `decide` 消费者的 `Verdict`/`Yes`/`No`/`Unknown`；四类未决理由仍是
    checker outcome 的共享词表，`decide` 建立时再引入三值结果。
  - `build_language` 接入 `bootstrap_elementary` 的真实装配；常数是带 sort 的名字，
    不再伪装成零元 operator；`ElementaryLibrary.operators` 这一派生字段删除。
  - `DeclarationSet` 在构造期执行完整准入规则，loader 不再复制同一套语义校验；
    `ElementaryLibrary` 在构造期校验名称/id 映射、basis 类型与 BASIS 定律前提，
    直接构造不能再绕过 builder。
  - `ParentRegistry` 要求结构声明自己的 kind、是否需要 base、生成元与表示选项，
    并逐一核对；`ParentSpec` 明确只描述已准入片段，relations/结构证明/根嵌入尚不可
    表达，也没有结构能冒充它们。
  - `AlgebraRequest` 不再只比较 `ParentSpec.base`，而是要求参数环暴露的实际系数
    结构对象就是请求的系数 parent。
  - 删除无消费者的 `ProblemSpec.target_sort`（此前还错误地存了源表达式的 sort）与
    `Interpretation.FUNCTION`。
  - 比较拼写表移到 `language/signatures.py`，删除 `frontend/surface.py`；
    `standard_language` 委托给 `build_language`；声明表达式的节点判定与
    `DeclarationSet` 校验各只有一份。
  - 本轮概念 owner 收口：结构否定统一到 `language/propositions.negates`；
    `LawExpr` 遍历统一到 `language/declarations.law_children`；`IntegerRing` 与
    一元多项式环复用 `Euclidean.gcd`；`KernelStore` 的 pending obligation 查询
    只有一份；`AGENTS.md` 增加概念 owner 纪律。
- 仍属显式能力边界而非当前纵线缺陷：`Reason.UNDECIDABLE`/`BUDGET` 尚无片段产生者；
  `ObligationReason` 的细分原因等到有 checker 报告义务时再消费；`IntegerRing`、
  `RationalFunctionField` 与 `rational_structure` 目前是低层代数 API，尚未接入运行时
  的数学片段；`ParentSpec` 的 relations/结构证明/根嵌入要等商结构与代数扩张落地。

仍待完成（按依赖顺序）：

1. `Definedness`/`Region` 证书、`EqualOn`/`SamePartialFunction`、结果/解集表示，
   以及请求 `Coverage` 与答案 `CoverageClaim` 在集合结果上的映射。
2. kernel 多推理批次/`LocalReceipt`/`AxiomRef`、分支合并支持。
3. Artifact/ObjectVersion、Task/Candidate 状态、完整 Event、Revision DAG、
   分支合并与覆盖派生。
4. 手动代换/改写/方程变换/出现位置/声明定义入口与前端显示。
5. 自动算法最后接入。

### 第一条纵线：已贯通

文本 → 解析为 Term → 求导 → `HasDerivative` 规格 → 独立验证 → kernel 发行 → 工作流记录 →
会话显示 → 撤销/重做。

`x³−3x` 求导得到 `3x²−3` 并通过独立验证后发行；`1/x` 求导诚实返回 UNSUPPORTED，
账本零写入。纵线现在由 `tests/integration/test_vertical_slice.py` 与
`tests/integration/test_frontend_slice.py` 正式覆盖，`python repl.py` 可直接使用。

### 测试套件（本轮重写）

本轮删除全部 v4 测试（45 个文件、273 个用例）。它们引用已删除的 v4 API，且所测能力中
CAD、积分、求解、REPL 等尚未在 v5 重建；保留测试名而没有可测对象没有意义。新套件以
v5 对象重写数学性质，不通过兼容层迁就旧语义。

新套件共 672 个用例：

- `tests/unit`（含参数化展开，613 个）：ids、term、binding、sorts、signatures、typing、
  propositions、decisions、problems；rationals、integers、parents、polynomial、rational；
  symbols、frames、definitions、bridge、differential、elaborate、algebra request；
  evidence、store、commit；specification、verify、differentiation checker；
  bootstrap、workspace；parser、pprint、session、repl；参数桥与参数 checker；
  binder 定型、声明 DSL、参数特化语义与特化 workflow；初等声明、条件求值、
  符号求导与 checker；hypothesis checker、条件检查、used_premises 最小化、
  适用性解析与 frame 作用域假设；`CheckerSpec`/`BasisRef`、矛盾规则、一致性状态
  的继承与撤销恢复、`Blocked` 适用性与否定义务；开放操作协议、通用
  `Workspace.apply`、成员检查与 `AlgebraValue`、统一导数证书、规则实例树与
  证书预算、跨 frame 可读性、单批 discharge。
- `tests/integration`（31）：纵线端到端、前端纵线、参数化纵线与初等函数纵线。intake 不产生
  Judgment；一次发行一条判断；inference/certificate 与请求逐项一致；undo 不回滚
  账本；片段外零写入；二阶导是新判断；文本经 parser/session 走到同一
  `HasDerivative` 验证边界；参数化 Q[a][x] 的角色分离与验证；泛参数覆盖声明、
  精确有理点特化与 Q[x] 独立复核；初等函数的链式法则、条件区域、受限 problem
  与历史；假设创建子 frame、当前 frame 操作与撤销/重做；矛盾假设发行 `false`
  后会话停止且账本保留。
- `tests/property`（28，固定种子）：结构相等/hash/全序、重建项折叠为一个字典槽位；
  绑定往返、shift 可逆、同时代换、Quote 惰性；
  Q/Z/K[x]/K(x) 的域与环定律、导子加性与 Leibniz；
  随机求导的独立验证、checker 接受正确候选并以见证否证扰动候选、workspace 随机求导；
  随机参数化多项式的独立验证与 checker 接受/否证；特化与求导可交换；初等符号求导
  在多项式子片段上与 Q[x] 求导一致；随机初等表达式与随机条件表达式通过独立 checker。

前端行为另有明确覆盖：运算优先级/结合性、`1+1` 不化简、有理字面量折叠、名称稳定 id、
链式比较与空输入等解析拒答（带列号）、可读打印、source 形式往返、标签唯一性、
焦点随 revision、隐藏对象不可引用、undo 后新操作截断 redo、unsupported 不是前端错误。

测试只做行为与性质验收；没有任何按标识符、AST 名字或 import 面判断设计的门禁。

测试暴露并修掉的两处实现缺陷：

1. `semantics/definitions.expand` 在最后一轮恰好完成展开时仍报 `DefinitionError`：
   预算边界把「已到达不动点」误报为「预算耗尽」。现在循环结束后再检查一次可见别名。
   （由 `test_expansion_reports_when_it_cannot_reach_a_fixed_point` 钉住。）
2. `RationalFunctionField` 原先接受非一元多项式环，直到首次 `gcd` 才抛 `AttributeError`。
   现在构造期拒绝 `TypeError`。（由 `test_k_x_requires_a_univariate_polynomial_ring` 钉住。）

### v4 遗留树清理

删除的内容：

- `cas/errors.py` 与 `cas/syntax/{abstract,match,parse,pattern}.py`；
- `cas/math/` 下除 `calculus/differentiation/` 以外的全部旧模块：`base/`、`domains/`、
  `elementary/`、`solving/`、`calculus/integration/`，以及 `cad`、`realroot`、`tactics`、
  `rules`、`loader`、`decide`、`definitions`、`diff`、`integrate`、`piecewise`、
  `constraints`、`project` 等。

这些实现全部依赖已删除的 v4 内核/语法 API，与 v5 不兼容。git 历史保留它们作为重新
实现时的参考，当前树中不保留兼容层。`elementary/` 已按 v5 重新建立为 data-only
声明与独立 checker，不是旧实现的迁移。`README.md` 与 CI 已同步为 v5 验收
（`mypy --strict`、`ruff`、`compileall`、`pytest`）；旧的门禁式测试分类
（`contract` / `regression` / `random` 标记与 `tests/random` 路径）一并移除。

### v5 边界收口

对照 v5 审计发现并修复的实现偏差：

1. **Power 的 sort 规则**：非负整数字面指数保持底数 sort；负整数或符号整数指数把
   Integer 底数放宽为 Rational，Real/Complex 保持；分数指数返回 Complex（底数
   Unknown 时保持 Unknown）。不再把 `2^-1` 或 `2^(1/2)` 定型为 Integer。
2. **账本写入闭合**：唯一写入点改为私有 `_publish`，只由 `commit` 调用。写入前
   验证重复 id、引用闭合（judgment↔inference、premise/conclusion/obligation
   必须存在且互相一致）、帧存在、proposition 在其存储帧可读，以及 commit 的
   discharge 证明/目标帧可见。公开 API 不再提供直接写账本的入口；存储层测试
   全部经 `commit` 建账。
3. **前提来源**：`Verified.used_premises` 是 checker 报告的实际使用前提索引；
   `commit` 只把这些前提写进 `InferenceRecord`，并且只从它们继承条件。调用方给了
   但 checker 未使用的前提，不进入支持集，也不携带条件。
4. **义务帧可见性**：`commit` 检查新报告与继承的 obligation proposition 在提交帧
   可读；`_publish` 再校验一次。
5. **清偿证明闭合**：`commit` 的 discharge 只接受 applicable 的证明；证明自身
   还有未决条件时拒绝，而不是把原条件标记为已闭合（v5 §14.3）。
6. **Quote 定型惰性**：`Quote(...)` 的实参不再参与定型；parser 区分
   `quote(...)`（held-data term）与 `Quote(...)`（结构应用），source 形式可区分
   并能逐项往返。

### 验收（本轮）

- `python -m pytest -q`：672 passed（unit 613 / integration 31 / property 28）。
- `python -m mypy --strict cas`：76 source files，无问题（全库）。
- `python -m ruff check cas tests`：All checks passed。
- `python -m compileall -q cas`：通过。

### 已知语义缺口

- 条件与义务：条件区域、受限蕴含/等价、`ConditionChecker` 与
  `resolve_applicability` 已接入，证明与 discharge 已合并为单批原子发布；
  frame 一致性状态、核心矛盾规则与 `Blocked` 分支已建立；矛盾规则现在也识别
  ground 闭合假假设，但一般一阶一致性与等价变形后的否证仍未建。
- 信任元数据：`CheckerSpec`（证书 schema、accepted kinds、trusted
  dependencies）与 `BasisRef` 版本/摘要已接入；证书类型、节点数/深度预算与 basis
  world 由 kernel 检查。更细的结构校验仍由 checker 的 `InvalidEvidence` 承担，
  `AxiomRef` / `LocalReceipt` 的完整分类仍未建。
- 初等层仍只覆盖一元函数、非负整数幂；负幂/分式、更多函数、初等表达式相等判定、
  完整 `BasisRef`、别名/角色尚未实现。条件定律体调用的函数定义域现在会并入
  结果区域；体内部的非零要求（如负幂）仍属于受信 basis 的承诺。
- 问题/覆盖层：workflow 当前只接受 `ONE_VERIFIED` + `EXPRESSION` 结果；集合结果、
  `SOUND_SET`/`COMPLETE_SET` 与 externalizable premises 都明确拒答，尚未实现。
- 声明 DSL 已统一：常数/函数/定律与 binder/operator 使用同一个 loader；数学层只
  做准入与建库。别名/角色声明仍未接入。
- binder 类型规则首个切片已完成（声明参数 sort、函数值/值 binder、嵌套索引、注解外层
  定型）；尚未完成注解驱动的参数 sort、量化/全称引入、前端 binder 语法与 source 形式。
- 桥接只覆盖多项式；K(x) 的 Term 双向桥接未建。
- 参数层已完成角色分离、`AllParameterValues`/`GenericParameters` 覆盖声明、
  精确有理点特化与异常集协议；尚未实现参数关系（多项式等式/不等式/整数约束）、
  参数分支、会生成非空异常集的真实局部化算法，以及精确有理值之外的特化点。
- 否证目前只识别可见闭合判断中的结构否定；等价的否定形式、多原子条件否证与
  一般一阶推理仍未接入。`Blocked` 只表达当前不能应用，不表达结论为假。
- 前端当前只覆盖纵线：无声明/定义命令、无隐式标量默认、`@LABEL` 只作为命令目标，
  不能嵌入公式、只对 `x` 求导、无持久化；REPL 默认装配初等片段，参数化入口仍在
  Python API；`specialize` 只接受精确有理字面量。

### 下一步

按依赖顺序继续，不扩张计算功能：

1. 域层：转换/同态、`AlgebraValue` 的完整使用、`Definedness`/`Region` 证书、
   `EqualOn`/`SamePartialFunction`、结果/解集表示，以及请求 `Coverage` 与答案
   `CoverageClaim` 在集合结果上的映射。
2. 条件逻辑：多原子线性不等式组与更完整的 Or/Not；`refutation_of` 扩展到
   被证明等价的否定形式；未知关系仍返回 Unknown。
3. 信任收口：`AxiomRef`/`LocalReceipt`、片段级一致性 checker、多推理批次与
   分支合并支持。
4. workflow：Artifact/ObjectVersion、Task/Candidate 状态、完整 Event、
   Revision DAG/分支合并、覆盖派生；之后才是手动代换/改写/方程变换/出现位置
   与前端显示。
5. 计算层最后接入：初等函数扩展、参数关系/分支、积分、方程、实代数与 CAD；
   每个新数学层同时补行为测试与种子固定的性质测试。
6. 不恢复按名字扫描的门禁；结构不变量继续由构造方式保证。
