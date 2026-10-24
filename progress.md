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
| language | `declarations.py`：data-only 声明 DSL（binder/operator 签名）、文本/文件加载、带行号的拒答、`build_language` 装配 |
| language | `propositions.py`：`Proposition` 只能经 `check` 发行，必须良作用域、命题 sort，并携带 `MeaningKey` |
| language | `problems.py`：ProblemSpec 固定操作、输入、目标、区域、结果语言、参数模式、覆盖要求 |
| language | `decisions.py`：三值 Verdict；No 必带见证；Unknown 必带四类理由；不可转 bool |
| algebra | `protocols.py`：Ring / Field / Euclidean / Ordered / IntegerEmbedding / RationalEmbedding / Derivation 分离，无默认零导子 |
| algebra | `parents.py`：ParentSpec 结构身份 + ParentRegistry（同描述一个 id，不同结构拒绝） |
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
| semantics | `differential.py`：`DifferentialStructure` 把 parent 与选定导子显式配对 |
| semantics | `elaborate.py`：先展开别名再定型/发行命题，存下的命题 alias-free |
| kernel | `model.py` / `evidence.py`：Judgment / Obligation / InferenceRecord / Discharge / Applicability；Checker 协议与四种 outcome |
| kernel | `store.py`：唯一原子写入 `_publish`（仅 commit/discharge 调用）；support 传递闭包；显式 `discharge` 带环检测；适用性查询 |
| kernel | `commit.py`：实际验证规格必须等于请求；继承义务 + 新义务受同一 ConditionPolicy；一次整批发行 |
| math | `differentiation/specification.py`：`HasDerivative(region, f, x, g)` 词表与解析 |
| math | `differentiation/verify.py`：系数级独立验证，不调用环的 `derivative` |
| math | `differentiation/checker.py`：证书逐项匹配；只有全域可证；片段外 Unverified；错误候选 Refuted 带见证 |
| math | `elementary/declarations.py` + `declarations.dsl`：data-only 常数/一元函数/定义域/导数定律、BASIS 与 USER_AXIOM 来源、精确有理 DSL 表达式 |
| math | `differentiation/elementary.py` / `elementary_verify.py` / `elementary_checker.py`：符号候选生成、独立重建与 checker；条件定律/未声明依赖/负幂诚实拒答 |
| workflow | `records.py` / `workspace.py`：表达式对象、候选、验证关联、事件、revision；intake 不发行判断；undo/redo 只移视图；参数族记录与精确点特化；求导候选经注入服务 |
| runtime | `bootstrap.py`：显式装配 Q[x]、Q[a…][x]、Q[x] 特化视图与初等函数片段；`bootstrap_parameterized` 固定参数角色，`bootstrap_elementary` 从声明文件装配函数与定律 |
| frontend | `parser.py`：文本 → Term，名称解析到稳定 SymbolId，结构 head 驱动，无化简、无数学语义 |
| frontend | `pprint.py`：可读形式 + 全应用 source 形式；source 对可解析项逐项往返，binder/自由索引/非符号算子显式拒答 |
| frontend | `session.py`：对象标签、焦点、intake/diff/specialize/show/list/undo/redo；只经 Workspace 与 kernel；旧 `cas/api.py` 已删除，Session 是唯一前端门面 |
| frontend | `repl.py`：逐行 REPL，仅分派与打印；默认装配初等函数片段；前端错误报告，诚实拒答仍是结果 |

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

### 初等函数片段（首个切片）

- `math/elementary/declarations.dsl` 是 data-only 的 v4 旧文件替换：声明常数、一元函数、
  函数定义域与导数定律。示例：`sin`/`cos`/`exp` 为无条件定律，`sqrt`/`log` 的定律
  和定义域带条件。DSL 有自己的精确表达式解析器，不依赖会话符号表。
- `LawOrigin.BASIS` / `USER_AXIOM` 记录定律来源；装配器只把标准库文件作为 basis
  准入，用户公理来源的定律保留但不会被自动使用。尚无完整的 `BasisRef` 版本/摘要记录。
- `build_elementary` 把名称固定为稳定 `SymbolId`，生成 `OperatorSignature`，并拒绝
  重名、保留名、未知名称/函数、错误 arity、非数值指数、重复定律与非法 law 参数。
  无条件定律还必须满足：函数本身无定义域条件、定律无 guard、定律体只调用全定义函数
  且不含负幂；否则在装配期拒绝。
- `differentiation/elementary.py` 是候选生成器：字面量与常数导数为 0，目标为 1；
  支持 Plus、Times、非负整数 Power 与声明函数的链式法则。负幂、未声明依赖、条件
  定律/定义域、用户公理、无定律函数都返回带理由的拒答。
- `elementary_verify.py` 是第二个独立的求导实现，`elementary_checker.py` 只调用它。
  checker 校验证书与规格一致；结构不同的候选返回 `Unverified`，不伪装成 `Refuted`，
  因为没有初等表达式相等判定。
- `semantics/services.py` 引入注入的 `DerivativeService`；`Workspace.differentiate`
  只依赖候选/证书服务，不再知道多项式桥。Q[x] 与参数化运行时使用多项式适配器，
  初等运行时使用符号适配器。参数特化路径保持不变。
- `bootstrap_elementary()` 从声明文件装配函数、常数、签名、frame、elementary checker
  与 Q[x] 子片段的代数视图；默认 REPL 已切换到该运行时。
- 测试覆盖：DSL 装载/装配/拒答、定义域与条件、basis 与用户公理、候选生成、
  链式/乘积/幂规则、checker 的接受与拒绝、端到端会话、随机多项式与独立 checker 的
  性质验收。
- 尚未实现：条件定律与函数定义域的条件服务/义务清偿（`sqrt`/`log` 因此拒答）、
  完整 `BasisRef`、别名/角色、非一元函数、负幂/分式与更多初等函数、初等表达式
  相等判定。

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

新套件共 545 个用例：

- `tests/unit`（含参数化展开，491 个）：ids、term、binding、sorts、signatures、typing、
  propositions、decisions、problems；rationals、integers、parents、polynomial、rational；
  symbols、frames、definitions、bridge、differential、elaborate、algebra request；
  evidence、store、commit；specification、verify、differentiation checker；
  bootstrap、workspace；parser、pprint、session、repl；参数桥与参数 checker；
  binder 定型、声明 DSL、参数特化语义与特化 workflow；初等声明、符号求导与 checker。
- `tests/integration`（27）：纵线端到端、前端纵线、参数化纵线与初等函数纵线。intake 不产生
  Judgment；一次发行一条判断；inference/certificate 与请求逐项一致；undo 不回滚
  账本；片段外零写入；二阶导是新判断；文本经 parser/session 走到同一
  `HasDerivative` 验证边界；参数化 Q[a][x] 的角色分离与验证；泛参数覆盖声明、
  精确有理点特化与 Q[x] 独立复核；初等函数的链式法则、条件定律拒答与历史。
- `tests/property`（27，固定种子）：结构相等/hash/全序、重建项折叠为一个字典槽位；
  绑定往返、shift 可逆、同时代换、Quote 惰性；
  Q/Z/K[x]/K(x) 的域与环定律、导子加性与 Leibniz；
  随机求导的独立验证、checker 接受正确候选并以见证否证扰动候选、workspace 随机求导；
  随机参数化多项式的独立验证与 checker 接受/否证；特化与求导可交换；初等符号求导
  在多项式子片段上与 Q[x] 求导一致，随机初等表达式通过独立 checker。

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
2. **账本写入闭合**：唯一写入点改为私有 `_publish`，只由 `commit` 与 `discharge`
   调用。写入前验证重复 id、引用闭合（judgment↔inference、premise/conclusion/
   obligation 必须存在且互相一致）、帧存在、proposition 在其存储帧可读，以及
   discharge 的证明/目标帧可见。公开 API 不再提供直接写账本的入口；存储层测试
   全部经 `commit` 建账。
3. **前提来源**：`Verified.used_premises` 是 checker 报告的实际使用前提索引；
   `commit` 只把这些前提写进 `InferenceRecord`，并且只从它们继承条件。调用方给了
   但 checker 未使用的前提，不进入支持集，也不携带条件。
4. **义务帧可见性**：`commit` 检查新报告与继承的 obligation proposition 在提交帧
   可读；`_publish` 再校验一次。
5. **清偿证明闭合**：`discharge` 只接受 applicable 的证明；证明自身还有未决条件
   时拒绝，而不是把原条件标记为已闭合（v5 §14.3）。
6. **Quote 定型惰性**：`Quote(...)` 的实参不再参与定型；parser 区分
   `quote(...)`（held-data term）与 `Quote(...)`（结构应用），source 形式可区分
   并能逐项往返。

### 验收（本轮）

- `python -m pytest -q`：545 passed。
- `python -m mypy --strict cas`：59 source files，无问题（全库）。
- `python -m ruff check cas tests`：All checks passed。
- `python -m compileall -q cas`：通过。

### 已知语义缺口

- 初等函数片段只覆盖一元函数、非负整数幂与无条件且全定义的定律；条件定律与函数
  定义域尚未接入条件服务/义务清偿，因此 `sqrt`/`log` 诚实拒答。还没有完整的
  `BasisRef` 版本/摘要、别名/角色声明、初等表达式相等判定与更多函数。
- 语言层声明 DSL 首个切片只覆盖 binder/operator 签名；导数定律、定义域/值域、
  别名/角色与常数的 *语言级* 声明仍归各自的数学声明文件。
- binder 类型规则首个切片已完成（声明参数 sort、函数值/值 binder、嵌套索引、注解外层
  定型）；尚未完成注解驱动的参数 sort、量化/全称引入、前端 binder 语法与 source 形式。
- 桥接只覆盖多项式；K(x) 的 Term 双向桥接未建。
- 参数层已完成角色分离、`AllParameterValues`/`GenericParameters` 覆盖声明、
  精确有理点特化与异常集协议；尚未实现参数关系（多项式等式/不等式/整数约束）、
  参数分支、会生成非空异常集的真实局部化算法，以及精确有理值之外的特化点。
- 义务清偿目前是显式操作；自动解析/决策服务（inspect/resolve）尚未接入。
- 否定导致的 Blocked 变体尚未接入（需要 refutation 记录）。
- 条件被否证时的 Rejected 分支依赖未来的判定服务；当前只区分未决条件的三种策略。
- 前端当前只覆盖纵线：无声明/定义命令、无隐式标量默认、`@LABEL` 只作为命令目标，
  不能嵌入公式、只对 `x` 求导、无持久化；REPL 默认装配初等片段，参数化入口仍在
  Python API；`specialize` 只接受精确有理字面量。

### 下一步

1. 条件与义务：接入条件判定/清偿服务，让带条件定律和函数定义域产生显式义务或
   guarded 结果，而不是一律拒答；先服务 `sqrt`/`log` 的可微区域。
2. 初等层扩展：更多函数、负幂/分式与初等表达式相等判定；为每个新规则补正例、
   拒答与固定种子性质测试。
3. 语义层补齐：binder 表面语法与注解驱动 sort、量化/全称引入、K(x) 桥接；
   完整 `BasisRef` 与别名/角色。
4. 新的数学层：按目标顺序推进积分、方程、实代数与 CAD；先建立在已声明的初等函数
   与条件义务之上。
5. 参数层继续：参数关系、参数分支，以及让局部化算法真正产生异常集；前端下一层：
   声明/定义命令、对象引用嵌入公式、参数化会话入口与持久化。
6. 测试随能力增长：每个新数学层同时补行为测试与种子固定的性质测试；不恢复按名字
   扫描的门禁。
