# Progress

当前实现状态与下一步。设计裁定以 `cas_v5_arch.md` 为准，工程纪律以 `AGENTS.md` 为准。
本文只记状态，不重复设计。

**文档语言约定：本文档与 `AGENTS.md`、`cas_v5_arch.md` 一律用中文；源码（`.py` / `.dsl`）用英文。**

## 当前阶段：v5 彻底重构（进行中）

工作树处于重构中间态：新地基已落地，旧层尚未替换，因此 `pytest` 目前无法收集。
这是预期状态，不用兼容层掩盖。

### 已完成

| 层 | 内容 |
|---|---|
| 文档 | v4 架构文档删除；不可判定协议、根与序的可判定性地图、Unknown 三出口并入 v5 §11.8–§11.10 |
| 纪律 | `AGENTS.md` 重写：只允许类型/行为/性质三类验收，禁止关键字与 AST 名字门禁 |
| 测试 | 删除 4 个门禁文件；其余 45 个测试文件恢复为"行为规格参考与待改对象" |
| foundation | `cas/foundation/ids.py`：13 个互不混用的身份类型 + 单调 issuer |
| syntax | `term.py`：新项模型（字面量/符号引用/绑定变量/应用/binder/Quote），结构相等、hash、序，构造后不可变，纯语法不排序不化简 |
| syntax | `binding.py`：`shift` / `instantiate` / `abstract` / `substitute_free` / `free_symbols` / `well_scoped`，Quote 完全惰性 |
| language | `sorts.py`：Sort 封闭层次、NumberSystem 嵌入序、`join`、`is_ordered`（sort ≠ 表示） |
| language | `signatures.py`：结构 head 的封闭集合、Arity、BindingSignature、按 SymbolId 绑定的 LanguageSignature |
| language | `typing.py`：`infer` 返回 `Typed / NeedsDeclaration / Unsupported / IllTyped`，不复用裸 `None` |
| language | `propositions.py`：`Proposition` 只能经 `check` 发行，必须良作用域、命题 sort，并携带 `MeaningKey(world, frame)` |
| language | `problems.py`：ProblemSpec 固定操作、输入、目标、区域、结果语言、参数模式、覆盖要求；完整解请求不得外置前提 |
| algebra | `protocols.py`：Ring / Field / Euclidean / Ordered / IntegerEmbedding / Derivation 分离；无"默认零导子" |
| algebra | `parents.py`：ParentSpec（结构相等即身份，options 强制排序）+ ParentRegistry（同一描述一个 ParentId；同描述不同结构拒绝） |
| algebra | `rationals.py` / `integers.py`：Q 为域（有序、整数嵌入、显式零导子）；Z 为欧几里得整环（gcd 非负归一） |
| algebra | `polynomial.py`：多元多项式 K[x₁…xₙ]；元素由环签发（私有封印），跨环运算拒绝；系数环是判等权威；形式偏导用 `mul_int`，不假设整数嵌入；`UnivariatePolynomialRing` 才提供 divmod/gcd（gcd 首一归一） |
| algebra | `rational.py`：K(x) 既约分式域（分母非零且首一、分子分母互素、零为 0/1）；域运算、求逆、形式导数 `(n'd−nd')/d²`；元素同样私有封印 |
| kernel | `frames.py`：World/Frame 不可变版本；祖先可见性；声明/定义/假设的构造期校验；局部符号逃逸检查 |
| kernel | `model.py`：Judgment / Obligation / InferenceRecord / Discharge / Applicability（Applicable / Conditional / OutOfScope） |
| kernel | `evidence.py`：CheckRequest 与 Verified / Refuted / Unverified / InvalidEvidence；装配期校验 checker id 与 version 的冻结注册表 |
| kernel | `store.py`：唯一写入点 `publish`（整批校验后插入）；`support` 传递闭包；显式 `discharge` 带环检测；`applicability` 查询 |
| kernel | `commit.py`：checker 实际验证的规格必须等于请求；继承义务与新义务受同一 `ConditionPolicy`；一次整批发行 |
| semantics | `frames.py`（由 kernel 移入）：World/Frame、祖先可见性、构造期校验、逃逸检查、别名环拒绝 |
| semantics | `symbols.py`：会话符号表（一个名字一个稳定 id，`fresh` 用于遮蔽）+ `standard_language` |
| semantics | `definitions.py`：唯一的自动代换通道，展开到不动点；环在 frame 构造期已被拒绝 |
| semantics | `bridge.py`：Term ↔ K[x₁…xₙ] 的显式片段（字面量、生成元、和、积、非负整数幂）；片段外返回 `None` |
| semantics | `differential.py`：`DifferentialStructure`（parent + 选定导子），构造器封印；K[x] 偏导与 K(x) 形式导数 |
| semantics | `elaborate.py`：先展开别名再定型/发行命题；存下的命题是 alias-free 的 |
| language | `signatures.py` 扩展：`OperatorSignature` + `operators` 表，声明算子（谓词/函数）可被定型；数学意义仍在 math |
| language | `typing.py`：声明算子检查元数与参数 sort 的嵌入关系 |
| math | `differentiation/specification.py`：`HasDerivative(U,f,x,g)` 词表、构造与解析（谓词身份是 SymbolId） |
| math | `differentiation/verify.py`：系数级独立验证，不调用环的 `derivative`，因此不会自我认证 |
| math | `differentiation/checker.py`：证书必须与规格逐项一致；片段外 `Unverified`；错误候选 `Refuted` 并带见证 |
| workflow | `records.py`：Expression / Candidate / VerificationLink / Event / Revision / OperationStatus |
| workflow | `workspace.py`：intake（只落表达式对象，不发行判断）、differentiate（候选 → 精确规格 → commit → 验证关联）、undo/redo（只移指针，账本不回滚） |
| runtime | `bootstrap.py`：显式装配 Q、K[x]、选定导子、`HasDerivative` 谓词与 checker、声明 `x : Real` 的 frame、账本；`new_workspace` |

### 第一条纵线：已贯通

表达式 → 求导 → `HasDerivative` 规格 → 独立验证 → kernel 发行 → 工作流记录 → 撤销/重做，
通过运行时脚本验证：

- intake 不产生任何 Judgment；
- `x³−3x` 求导得到 `3x²−3`，checker 独立复核后发行判断，Applicability 为 Applicable；
- 规格可反解析回 `(region, source, variable, candidate)`，候选与链接一致；
- undo 后视图中只剩源表达式、账本判断仍在；redo 恢复；撤销后做新操作会截断 redo 分支；
- `1/x` 求导返回 UNSUPPORTED，账本零写入、无结果对象。

仍是脚本验收，尚未变成 `tests/` 下的正式验收。

### 已知的语义层缺口

- 声明 DSL（函数签名、导数定律、常数）尚未建：目前没有初等函数消费者，等 `math/elementary` 落地时再加。
- binder 的类型规则仍未建，`infer` 对 `Binder` 诚实返回 `Unsupported`。
- 桥接只覆盖多项式；K(x) 的 Term 双向桥接未建。

### 已知的内核缺口

- 义务清偿目前是显式操作；自动解析/决策服务（inspect/resolve）尚未接入。
- 否定导致的 Blocked 变体尚未接入（需要 refutation 记录）。
- 定义展开与定义性分析属于 semantics，尚未接入 commit。

### 已知的语言层缺口

- binder 的类型规则属于 elaboration：`infer` 对 `Binder` 返回 `Unsupported`，不猜变量类型。
- 声明的数学函数签名表尚未接入；`infer` 对未登记的结构外 head 返回 `NeedsDeclaration`。

### 静态检查

新文件通过 `ruff` 与 `mypy`。全库 mypy 暂不可用：旧层仍引用已删除的 `cas.syntax.termpath`。

### 已自检的语义（运行时脚本，不是测试套件）

- 独立构造的同构项相等、同 hash、不同对象；
- 构造后不可变；
- binder 开/闭往返；跨嵌套 binder 的捕获规避正确；
- 注解按外层深度处理；
- Quote 对所有绑定操作与自由符号完全惰性；
- 同时代换不重访插入项；
- arity 不匹配被拒绝。

### 下一步

1. 第 11 步：把纵线脚本变成正式 v5 验收——行为测试（正例 + 诚实拒绝例）+ 性质测试（随机多项式求导与独立验证）。
2. 前端重写：parser/printer/session，把输入接到新 API；不再兼容 v4 命令面。
3. 清理旧 v4 树：未迁移的算法（CAD、实根隔离、结式等）逐项迁移后删除，不留兼容层。

### 旧测试的处置

- 保留并逐层指向新 API：`tests/random/*`、`test_judge`、`test_decide_*`、
  `test_projected_consumption`、`test_piecewise_lift`、`test_printing`、
  `test_definitions`、`test_rule_*`、`test_solve_parametric`、`test_surface_names`、
  `test_abstract`、`contract/test_declarations_dsl`、`contract/test_domain_registry`。
- 按新内核/工作流 API 改写：`test_kernel_model`、`test_scope_*`、`test_step_refs`、
  `test_undo_redo`、`test_requirement_refutations`、`test_refutation_closure`、
  `tests/integration/*`、`tests/regression/*`。
- 其中断言已否决行为的用例改写而不迁就：对裸表达式 `Claim`、分支合并相信载荷答案、
  点等式穿过绑定体。
