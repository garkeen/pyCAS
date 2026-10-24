# Progress

当前实现状态与下一步。设计裁定以 `cas_v5_arch.md` 为准，工程纪律以 `AGENTS.md` 为准。
本文只记状态，不重复设计。

**文档语言约定：本文档与 `AGENTS.md`、`cas_v5_arch.md` 一律用中文；源码（`.py` / `.dsl`）与测试源码用英文。**

## 当前阶段：v5 彻底重构（进行中）

v5 的新层（foundation / syntax / language / algebra / semantics / kernel / 求导 /
workflow / runtime / frontend）已完整，具备正式验收；v4 遗留代码树已全部删除。
全库 `mypy --strict cas`、`ruff`、`compileall` 与测试均转绿。当前唯一的数学能力是
Q[x] 与形式参数系数 Q[a…][x] 上的单变量多项式求导，其余数学层将按 v5 架构重新落地。

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
| semantics | `bridge.py`：项 ↔ 多项式元素；新增参数桥，参数映射到系数环生成元、目标映射到外层生成元 |
| semantics | `differential.py`：`DifferentialStructure` 把 parent 与选定导子显式配对 |
| semantics | `elaborate.py`：先展开别名再定型/发行命题，存下的命题 alias-free |
| kernel | `model.py` / `evidence.py`：Judgment / Obligation / InferenceRecord / Discharge / Applicability；Checker 协议与四种 outcome |
| kernel | `store.py`：唯一原子写入 `_publish`（仅 commit/discharge 调用）；support 传递闭包；显式 `discharge` 带环检测；适用性查询 |
| kernel | `commit.py`：实际验证规格必须等于请求；继承义务 + 新义务受同一 ConditionPolicy；一次整批发行 |
| math | `differentiation/specification.py`：`HasDerivative(region, f, x, g)` 词表与解析 |
| math | `differentiation/verify.py`：系数级独立验证，不调用环的 `derivative` |
| math | `differentiation/checker.py`：证书逐项匹配；只有全域可证；片段外 Unverified；错误候选 Refuted 带见证 |
| workflow | `records.py` / `workspace.py`：表达式对象、候选、验证关联、事件、revision；intake 不发行判断；undo/redo 只移视图 |
| runtime | `bootstrap.py`：显式装配 Q[x]（无参数）与 Q[a…][x]（形式参数作为系数）；`bootstrap_parameterized` 把参数角色固定为目标之外的系数生成元 |
| frontend | `parser.py`：文本 → Term，名称解析到稳定 SymbolId，结构 head 驱动，无化简、无数学语义 |
| frontend | `pprint.py`：可读形式 + 全应用 source 形式；source 对可解析项逐项往返，binder/自由索引/非符号算子显式拒答 |
| frontend | `session.py`：对象标签、焦点、intake/diff/show/list/undo/redo；只经 Workspace 与 kernel；旧 `cas/api.py` 已删除，Session 是唯一前端门面 |
| frontend | `repl.py`：逐行 REPL，仅分派与打印；前端错误报告，诚实拒答仍是结果 |

### 参数域与系数域（首个切片）

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
  （Workspace 拒绝），`1/a` 在多项式片段外诚实拒答。问题规格记录
  `GenericParameters` 模式。
- 尚未实现：参数特化、局部化/异常集、`AllParameterValues` 覆盖、参数关系与
  参数分支；当前只承诺形式参数作为多项式系数的泛参数结果，不声称对所有参数值
  成立。

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

新套件共 454 个用例：

- `tests/unit`（含参数化展开，417 个）：ids、term、binding、sorts、signatures、typing、
  propositions、decisions、problems；rationals、integers、parents、polynomial、rational；
  symbols、frames、definitions、bridge、differential、elaborate、algebra request；
  evidence、store、commit；specification、verify、differentiation checker；
  bootstrap、workspace；parser、pprint、session、repl；参数桥与参数 checker；
  binder 定型与声明 DSL。
- `tests/integration`（13）：纵线端到端、前端纵线与参数化纵线。intake 不产生
  Judgment；一次发行一条判断；inference/certificate 与请求逐项一致；undo 不回滚
  账本；片段外零写入；二阶导是新判断；文本经 parser/session 走到同一
  `HasDerivative` 验证边界；参数化 Q[a][x] 的角色分离与验证。
- `tests/property`（24，固定种子）：结构相等/hash/全序、重建项折叠为一个字典槽位；
  绑定往返、shift 可逆、同时代换、Quote 惰性；
  Q/Z/K[x]/K(x) 的域与环定律、导子加性与 Leibniz；
  随机求导的独立验证、checker 接受正确候选并以见证否证扰动候选、workspace 随机求导；
  随机参数化多项式的独立验证与 checker 接受/否证。

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
实现时的参考，当前树中不保留兼容层。`README.md` 与 CI 已同步为 v5 验收
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

- `python -m pytest -q`：454 passed。
- `python -m mypy --strict cas`：51 source files，无问题（全库）。
- `python -m ruff check cas tests`：All checks passed。
- `python -m compileall -q cas`：通过。

### 已知语义缺口

- 声明 DSL 首个切片只覆盖 binder/operator 签名；导数定律、定义域/值域、别名/角色、
  常数以及 `math/elementary` 的数学声明尚未建。
- binder 类型规则首个切片已完成（声明参数 sort、函数值/值 binder、嵌套索引、注解外层
  定型）；尚未完成注解驱动的参数 sort、量化/全称引入、前端 binder 语法与 source 形式。
- 桥接只覆盖多项式；K(x) 的 Term 双向桥接未建。
- 参数层只完成首个切片：形式参数作为系数生成元与 `GenericParameters` 记录；特化、
  局部化/异常集、`AllParameterValues`、参数关系与参数分支尚未实现。
- 义务清偿目前是显式操作；自动解析/决策服务（inspect/resolve）尚未接入。
- 否定导致的 Blocked 变体尚未接入（需要 refutation 记录）。
- 条件被否证时的 Rejected 分支依赖未来的判定服务；当前只区分未决条件的三种策略。
- 前端当前只覆盖纵线：无声明/定义命令、无隐式标量默认（未声明名字可以进入对象，但
  求导会诚实拒答）、`@LABEL` 只作为命令目标，不能嵌入公式、只对 `x` 求导、无持久化。

### 下一步

1. 参数层继续：参数特化、局部化/异常集、`AllParameterValues` 覆盖与参数关系；
   每个新语义都配正例、拒答和性质测试。
2. 语义层补齐：binder 表面语法与注解驱动 sort、量化/全称引入、K(x) 桥接、
   义务自动清偿与否证；扩展声明 DSL 到导数定律、定义域与别名/角色。
3. 新的数学层：按 v5 架构重新落地被删除的能力。先做 `elementary` 声明（函数/常数/
   导数定律），再按目标顺序推进积分、方程、实代数与 CAD。
4. 前端下一层：声明/定义命令、对象引用嵌入公式、参数化会话入口、source/serialization
   形式、新的数学操作命令；每项都配「正例 + 诚实拒绝」行为测试。
5. 测试随能力增长：每个新数学层同时补行为测试与种子固定的性质测试；不恢复按名字
   扫描的门禁。
