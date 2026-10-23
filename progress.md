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

1. `cas/kernel`：World/Frame、Judgment/Obligation/InferenceRecord、commit、原子批次 store。
2. `cas/semantics`：Frame 与 elaboration（binder 变量类型在此确定）、声明 DSL 装配、定义展开、Term↔parent 桥。
3. `cas/math`：`HasDerivative` 规格 + 独立验证 checker。
4. `cas/workflow`/`runtime`：表达式对象、候选、验证关联、revision/undo；然后跑通第一条纵线。

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
