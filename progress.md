# 进度

本文记录当前实现状态与下一步。与 `cas_v4_arch.md`（设计权威）分开维护；`cas_v3_arch.md` 已废止，仅历史追溯。

## 文件架构（v4 §三 目标树落位，2026-09-10）

纯移动 + import 重写，行为零变；tests(57)/stress(41) 全绿验收；`git mv` 保留历史。环解药原样保留（均有注释）：term↔termpath PEP 562 惰性回接、rules↔loader 函数内回边、piecewise 底部 E402 导入、project 的 import 期域注册、library 的 `load_all()`。新子包 `__init__.py` 全空——eager re-export 会把惰性环变回硬导入环。

| 位置 | 内容 |
|---|---|
| `cas/syntax/` | term（驻留项层）、termpath（树遍历/重写）、match（模式匹配） |
| `cas/kernel/` | verdict（判定 ADT）、context（v3 可变 Context，阶段5 换持久化 Scope；decide 依赖已方法内惰性化——kernel 不拉 math） |
| `cas/workflow/` | workflow（Step DAG，v3 遗留，阶段3 拆） |
| `cas/math/` | domains/（base/q/z/qi/poly/ratfunc/polytools/linalg）、decide、qarith、project、diff、integrate、cad、tactics、piecewise、domcond、rules、simplify、judge、realroot、loader |
| `cas/frontend/` | parser、pprint、repl（根目录 `repl.py` 留入口壳，`python repl.py` 不变） |
| 留根 | `cas/errors.py`（共享异常）；`library/`（阶段6 迁为 math/*，搬两次是浪费） |

已知容忍的结构债：workflow→math 顶层依赖（v3 遗留，阶段3 拆 checker 注册表时解决）；syntax/termpath、match → `cas/errors`（基础设施，留根）。

## v4 迁移路线图（v4 §十一 六阶段）

| 阶段 | 内容 | 状态 |
|---|---|---|
| 1 拆语法（模块落位） | 语法入 syntax/，前端入 frontend/ | ✅ 2026-09-10 |
| 1 拆语法（模式元语言） | PatVar/PatSeq 移出 Term（Pattern 独立层次） | ✅ 2026-09-10（本次，不变量 2 转绿） |
| 2 新内核模型 | Scope / Judgment / Evidence / StepProposal / commit / CheckerRegistry | ⬜ 未开始 |
| 3 拆除 Derivation ADT | Step 无子类，`_verify` isinstance 分派 → checker 注册表 | ⬜ 未开始（不变量 14 红） |
| 4 Artifact/Task/Judgment 分离 | workflow 三图分离 | ⬜ 未开始（不变量 16 红） |
| 5 持久化 Scope 树 | 可变 Context → 父指针树；undo/redo 移 revision 指针 | ⬜ 未开始 |
| 6 数学模块迁移 | library → math/*，install(builder) 装配 | ⬜ 未开始 |

不变量 CI 门禁（`tests/test_v4_invariants.py`）：1/2/18 绿，14/16 挂 xfail 红灯
（reason 写明迁移阶段），随阶段落地翻绿。

### 阶段 1b：模式元语言（2026-09-10）

`PatVar`/`PatSeq` 移出 `Term`，新建 `cas/syntax/pattern.py`（`PatternVar`/
`PatternSeq`/`PatternCall`）。字面量直接以 `Term` 充当模式（驻留项指针相等即
字面匹配），故模式参数类型是 `Pattern | Term`，不引入包装类型。

- **入口分道**：parser 增 `pattern=` 通道，`?x`/`??x` 与调用构造产出 `Pattern`；
  普通通道遇 `?x` 显式 `ParseError`——模式变量因此进不了项层（不变量 2 的机制，
  不只是类型声明）。规则 DSL（LHS/RHS/guard）经此通道解析（`loader.py`）。
- **实例化**：`instantiate` 从 `termpath`（Term 级，项层无洞故无意义）移入
  `pattern.py`，产出 `Term`；模板里未绑定的洞**显式报错**，不再把模式变量漏回项层。
- **匹配**：`match.py` 在 `Pattern` 层次分派，字面量走驻留项指针相等快通道
  （AC 规范化的红利：`p in terms` 即置换匹配）。规则索引键 `root_key` 移到模式层。
- **渲染**：`pprint.pat_to_str` 输出可重解析的 DSL 形（`exp(?a) * exp(?b) ->
  exp(?a + ?b)`），`repl rules` 改走此通道（原先 `to_str` 会把 Pattern 打成 `repr`）。
- **无兼容残留**：`term.py` 删除 `PatVar`/`PatSeq`/`PV`/`PS` 与相关 `sort_key`
  分支；`termpath` 删除 `instantiate`/`_instantiate_raw`；契约测试
  `test_module_graph.py` 按 v4 更新（不留别名）。

验收：`tests/` 62 passed + 2 xfailed；`stress/` 10 passed（41 条性质）。


## 已完成（v3 实现基线，稳定全绿）

### 地基
- **L0 驻留项层**（`cas/term.py`）：不可变 hash-consing 树，AC 拉平+排序，绑定变量（de Bruijn），纯句法无域语义；And/Or 句法折叠（真值常元吸收、排中/矛盾律坍缩）
- **ℚ 字面算术**（`cas/qarith.py`）：`fold` 显式折叠（含普适恒等 b^1=b）+ `eval_exact` 环层精确求值
- **域系统**（`cas/domains/`）：`Domain` 协议（normalize/equal/member，`equal` 返回 `bool|None`——None 为非成员越界，片段内无 UNKNOWN）+ `Ring` 协议（含系数导数 `deriv`）。**能力字段**（架构 3.2）：`is_field`/`is_ordered`/`is_euclidean`，算法按能力分派不按类型特判
  - ℤ：`ZZRing`（带余除法/gcd/扩展gcd）+ `ZDomain`——有序欧几里得整环，非域；丢番图可判定碎片的宿主
  - ℚ：`QRing` + `QDomain`
  - ℚ(i)：`QIRing` + `QIDomain`（`cas/domains/qi.py`）——第一个代数扩张 = ℚ[z]/(z²+1)：元素为 (re, im) 标准形对（结构判等），除法走共轭×范数；成员通道 = 闭项 i↦z → ℚ(z) 有理函数 → 模 z²+1 约化（Maxima 代数量模式）；i 常数身份由图书馆声明在投影层注入，不做名字嗅探；能力 is_field=True / **is_ordered=False（复数无序，序判定按能力查表拒绝）** / is_euclidean=False（欧几里得结构属于 ℤ[i]）。参照经验见 reference.md"已消化经验"
  - K[x₁..xₙ]：`PolyDomain`，稀疏系数字典，泛 Ring 协议，单变量欧几里得 GCD + 域系数精确除法 + **域导数 `p_deriv`**；能力：单变量+域系数才是欧几里得
  - K(x₁..xₙ)：`RatFuncDomain`，交叉相乘判等 + 单变量 GCD 约简 + **域导数 `rf_deriv`（商规则）**；能力：恒为域，单变量欧几里得
- **判定契约**（`cas/verdict.py`）：Verdict ADT（`Yes(proof)/No/Unknown(reason)`），理由枚举 FRAGMENT/GUARDED/UNDECIDABLE/BUDGET，and3/or3/not3 传播首个 Unknown 理由
- **域投影层**（`cas/project.py`）：成员测试阶梯 ℤ → ℚ → **ℚ(i)** → K[x] → K(x)——域由投影赋予，不做叶嗅探；`zero_of` 判零快捷通道（常数格统一走域判等，任意常数域泛化）
- **判定管线**（`cas/decide.py`）：全通道返回 Verdict；区间通道（BFS 链查询已修）、结构符号引理、图书馆常数界与函数值域界（端点语义按算子分治）、深度上限 BUDGET 诚实
- **图书馆**（`library/`）：`ConstantDecl`/`FunctionDecl` 冻结 dataclass + 注册表 + 定义域条件注册
  - 常数：π, e, i, γ（正性、粗界、实性声明）
  - 函数：sin, cos, tan, exp, log, sqrt, abs, atan, sinh, cosh, tanh（印名、元数、值域界、定义域条件）
  - **导数模板作为数据**：每函数声明 `deriv` 模板（de Bruijn `DB(0)` 占位）；无条件恒等式才入册；分支破裂者以 Piecewise 容器如实声明（`Abs` 导数 = `piecewise(1 if u>0, -1 if u<0)`，u=0 无支即不可导）
  - 规则声明（exp_add 等）经统一规则引擎装配
- **规则引擎**（`cas/rules.py`）：单引擎；守卫经 decide Verdict；auto 规则仅限无守卫（防 decide↔simplify 互递归）；`autosimplify` 严格代价下降保终止
- **工作流**（`cas/workflow.py`）：Step DAG（七字段：id/content/derivation/guards/status/target/reads/clears/domain）+ **八种**推导类型（Claim/BothSides/Rewrite/Solve/Subst/Split/Diff/**Integrate**）+ 守卫指针去重与 Split 清偿 + 死步骤级联
  - **验证器-求解器独立**：Solve 验证器只做回代判官（代入+投影判零，不重跑求解）；Diff 验证器用域层导数交叉复核项层结果；Integrate 验证器用微分层复核原函数、定积分再核端点差；Rewrite 复核图书馆规则产物；Split 排中律覆盖验证
  - 域归属：步骤内容经投影记录所属域（步骤展示 ∈K[x]/K(x)/Q）
- **战术层**（`cas/tactics.py`）：线性求解战术 + 丢番图碎片——线性丢番图（扩展欧几里得，裴蜀证书+周期参数化）、单变量整数根（有理根定理完备候选）+ **分段方程求解**（`solve_piecewise`）。线性分类内核 `_lin_core` 在**投影标准形**上裁决（语义判据非形状判据）：恒零→恒等式/区域解、无变元非零→矛盾/无贡献、恰一次→-b/a 证书、其余（非线性/多变量/域外）拒答；分段求解逐支消费同一分类（闭式支走判零通道），任支超出片段整体拒答保完备性；只交证书，验证独立
- **公共算法机器**：
  - 线性代数（`cas/domains/linalg.py`）：域上高斯消元、秩、零空间基、方程组求解（特解+齐次基/不相容判定）、Bareiss 整数行列式
  - 结式与无平方（`cas/domains/polytools.py`）：结式（余式序列递归，共根判据+求值锚点）、Yun 无平方分解（monic 因子×重数）
  - 一维 CAD（`cas/cad.py`）：单变量多项式条件 → 有序互斥胞腔（开区间+点），Sturm 根隔离精确定符号；条件非单变量多项式分区按 FRAGMENT/UNDECIDABLE 拒答
  - 积分骨架（`cas/integrate.py`）：多项式幂规则不定积分、分段逐支；定积分遵定义域∩[a,b]（缺口不对 0 积分、点洞拒答）；`verify_antideriv` 微分层独立复核
- **微分**（`cas/diff.py`）：任意数域系数 × 任意已声明函数域的结构微分——线性/莱布尼茨/幂-指数-一般幂规则/图书馆模板实例化×链式法则；缺模板、绑定体内微分诚实抛 `DiffError`。**分段求导审慎通道**（`differentiate_piecewise`）：逐支求导 + 分段点（点胞腔）显式列出未验证——开区间胞腔上导数成立，分段点可导性须极限层（未建），绝不逐支冒充整体导数
- **分段容器**（`cas/piecewise.py`）：`Piecewise(v,c,...)` 语法容器（非数值域）——求值语义为**有序首中**（if/elif/else，`⊤`=否则支；每点至多落一支 → 取值天然唯一，无求值层冲突）：`select` 取值、`coverage` 覆盖、**`collapse` 点塌缩**（任意深度的分段子项按有序首中塌缩为支值，数值点回代判定的公共通道）；分支体**独立投影**无共享宿主（`project_pw`）；运算**逐支笛卡尔提升**（`lift`，`(f⊕g)(x)=f(x)⊕g(x)`，条件取合取、空组合丢弃）；`conflicts` 作**顺序无关性 lint**（交叠处值不等→提示收紧为互斥守卫，判不动即 Unknown，不作求值闸）；`domcond` 对分段产出条件化守卫 ¬cond∨支约束；`fold_nested` 嵌套展平、`domain_cells`/`connected_components` 定义域胞腔与连通分量；`Abs` 导数据此以 Piecewise 如实入册（`sign`，u=0 无支）
- **REPL**（`cas/frontend/repl.py`，根目录 `repl.py` 为入口壳）：claim/both/norm/solve/subst/**split/diff/rules/apply/integrate/int**/check/steps/undo——solve/diff 对分段自动路由：分段方程逐支求解（点解入账走回代判官、区域解/条件解如实报告）、分段求导走审慎通道（分段点未验证标注）；check 对含分段项点塌缩后判零
- **压力台架**（`stress/`）：41 条性质，全自证无外部真值（随机、覆盖数学性质全域）
- **钉子库**（`tests/`）：57 条确定性单测（退化形态、修过的 bug、职责边界；失败定位到断言）
  - 图书馆查询出口、印名展示形/源码形分离、回代判官各分支、域注册集中化与作用域机制、全模块独立导入、decide 公理层兜底
  - 与 stress/ 分工：stress 管"数学没错"，tests 管"结构与契约没退化"；CI 两步都跑
  - P1-P4：折叠保真、幂等指针、区间真值表、回代判官
  - P5-P9：多项式往返、判等完备、交叉相乘、GCD 整除
  - P10-P13：项层微分 × 域层导数交叉、线性/莱布尼茨/商规则恒等、泰勒 h¹ 系数、验证器独立性
  - P14-P17：秩-零化度、相容/不相容判定、Bareiss 乘法性、丢番图证书（裴蜀/周期本原/整数根全集）
  - P18-P20：结式求值锚点、共根判据×对称性（结式 vs GCD 双算法交叉）、无平方往返
  - P21-P24：分段投影逐支独立、选支语义（具体点参照扫描）、运算逐支提升×逐点一致、守卫条件化+重叠一致性
  - P25-P28：CAD 胞腔排序互斥覆盖、样本点符号一致、拒答理由（FRAGMENT/UNDECIDABLE）、点胞腔符号（Sturm 消没判定）
  - P29-P31：分段归一化往返、连通分量划分、缺口断开
  - P32-P35：不定积分往返+两通道、可加性/FTC、分段定积分、积分拒答边界
  - P36-P38：分段求导两通道交叉+分段点定位、分段解方程独立参照（含区域解/拒答）、工作流端到端（真解入账/伪解否决/Diff 逐支交叉验证）
  - P39-P41：ℚ(i) 双通道交叉（环对偶运算 vs i↦z→ℚ(z)→模约化成员通道）+域公理、成员边界+规范化幂等、阶梯×判零×能力字段×积分常数通道

### 阶段1-5：分段通道（CAD 地基 → 解方程/求导 → REPL 接线）
- 阶段1：最简 CAD——一维实根隔离（Sturm）+ 胞腔分解（开区间/点），条件符号精确判定
- 阶段2：分段归一化（`fold_nested` 嵌套展平）+ 定义域胞腔提取（`domain_cells` 消费 CAD，Undefined 切断）
- 阶段3：手通道定/不定积分骨架——多项式片段 + 独立验证器（微分层复核），定积分定义域诚实边界
- 阶段4：分段求导（审慎通道：逐支导数 + 分段点显式未验证）+ 分段解方程（常值支区域解/线性支条件裁决/非线性拒答）
- 阶段5：REPL 接线（solve/diff 分段自动路由）+ 工作流验证器分段感知——Solve 回代判官经 `collapse` 点塌缩（任意深度分段 + 定义域外判非解），Diff 验证器逐支域层导数交叉；端到端台架 P36-P38

### 架构整修（2026-08-27）
- 裸 `T3` 三值全部替换为带理由的 Verdict ADT
- 废除 `cas/domain.py`、`cas/structure.py`、`cas/domain_decls.py`——域操作支持矩阵的伪登记与叶嗅探分支政策清除
- decide/workflow 中的叶嗅探域判定改为投影层成员测试
- 异常吞没清除；`_chain_query` BFS 陈旧状态 bug 修复
- `term.py` 潜在 NameError（`_fold_bool_ac` 缺失）与 `poly.py` 缺失 `RingError` 导入修复

### 硬编码语义驱逐
- 常数单例从 `cas/term.py` 移至 `library/constants.py`
- `_CONST_BOUNDS` 表从 `decide.py` 移至图书馆 `const_bounds`
- `t is PI or t is E` 特判改为 `library.const_positive/const_real`
- simplify 的 Exp 合并特判删除，规则作为图书馆数据声明
- parser 常数表从图书馆导入

### 审查修正（2026-09-01）
- **Diff 推导关闭等式通道**：等式两边求导不保真（点解方程 x=3 会推出 1=0），REPL 与 workflow 验证器一律拒答/否证；隐函数求导留作带依赖声明的独立命令
- **注册纪律机制就位**：`Domain.scoped` 标记 + `domain_scope()` 作用域注册（退出即注销、重名即拒）+ `lookup()`。当时机制已建但**零消费者**（`lookup`/`domain_scope` 全项目无调用、`scoped` 无域声明），属空壳；2026-09-03 的职责唯一化把它接上真消费者，见下节
- **library→内核反向依赖消除**：规则 DSL 解析从 `library/api.py` 移至消费方 `cas/rules.py` 装配点，图书馆回归纯数据
- **parser 双通道合一**：raw（quote 保 held 形）与正常通道共享一套文法，仅构造原语分通道；顺带清除除法解析的 ×1 残余（两通道语义漂移）
- **整数根候选枚举** O(|a₀|) → O(√|a₀|)（复用 `realroot.divisors`）
- **工程**：stress 台架 pytest 收集层（`stress/test_stress.py`，台架脚本零改动）、pyproject.toml、CI 工作流；`qarith.fold` 驻留分支子项折叠归一

### 职责唯一化（2026-09-03）

审计发现一类反复出现的结构病：**同一职责有两个负责人——设计上的那个是空壳，实际干活的那个是硬编码**。本轮逐项收敛，原则是每个职责唯一负责人。

| 职责 | 原设计负责人（空壳） | 原实际负责人 | 收敛后 |
|---|---|---|---|
| 域的注册 | 各域模块自注册（4 处，内容取决于谁被 import） | 同左 | `cas/project` 唯一注册点，域包纯声明、零导入副作用 |
| 域的取用 | `lookup()`（0 调用） | `project` 自建单例 | 阶梯常数格经 `lookup()` 取用 |
| 参数化域 | `poly` 运行时按变元集灌注册表（无界增长）；`ratfunc` 从不注册 | — | 两者同策略：只走工厂缓存，不进注册表 |
| 常数印名 | `library.print_name`（只查函数，不查常数） | `pprint._SYM_REPR` | 图书馆补 `const_by_name`/`is_const_name`，`print_name` 覆盖常数；废 `_SYM_REPR` |
| 常数按名查询 | 无此出口 | `parser._CONSTS` 硬编码 | 查 `library.const_by_name`；`infinity/true/false` 是句法原子，留内核 |
| 定义域条件 | `domcond.DOM_HOOKS`（恒空） | `library._DOMAIN_CONDS` | 废 `DOM_HOOKS`，只留图书馆通道 |
| 回代判官 | `workflow._piecewise_aware_zero`（私有） | `repl` 内联副本 + 盗用私有 | 新建 `cas/judge.py`，两处共用一套 |
| 树遍历 | 两份同构 `_postorder` | pprint / simplify 各一份 | 归一到 `cas/termpath.postorder` |

- **判官裁决权威归一**：此前 repl 先试 `eval_exact`、workflow 只走 `zero_of`，两处通道顺序已分叉。现裁决一律走 `zero_of`（域标准形，覆盖严格广于环层 `eval_exact`），`eval_exact` 只取展示值。差分验证 1432 例零冲突
- **模块图修复**：`term.py` 末尾回接 `termpath` 改为 PEP 562 惰性 `__getattr__`。此前 `import cas.termpath` 基线即 ImportError，而注释却称"无导入环"。现全部 34 个模块均可独立导入
- **印名两种用途分清**：展示形吃图书馆 `print_name`（π/γ），`src=True` 源码形输出内部名（`pi`/`gamma`）——此前 `src=True` 承诺"可解析源码形"却输出词法不认的 π，往返断裂
- **死代码**：删 `RuleSet.for_term`（0 调用）、`domcond.DOM_HOOKS`、`pprint._SYM_REPR`
- **decide 公理层保留**：审计初判为死代码，实测否——屏蔽 `_cmp_interval` 后仍能正确裁决 `pi>3`/`e>2`/`sin(x)>2`。它是可用兜底，与区间通道同源数据但覆盖更窄，已在分派处写明关系并由 `tests/` 锁定
- **钉子库 `tests/` 建立**：此前只有 `stress/` 的随机压力测试（41 条性质），失败粒度是整个脚本、无单测级定位。现 `tests/` 放确定性钉子，与 stress 分工（stress 管随机性质全域，tests 管退化形态/bug/职责边界），57 条、CI 两步都跑。覆盖：图书馆查询出口、印名展示形与源码形分离、回代判官各分支、域注册集中化与作用域机制、全模块独立导入、公理层兜底

## 未完成（地基优先——Risch 门控）

用户指令：完整 Risch（含参数积分与超越数积分，参照 FriCAS）是最终目标，但**地基完工前不启动**。地基 = 下述算术与结构机器全部就位。

### 交互通道
- [ ] √(u²)→|u| 改写规则：Piecewise 容器与 Abs 导数就位后，尚缺实性假设通道（u 为任意实数才成立），入册前须先接通
- [ ] 工作流序列化与回放（**DSL 保存/复现**：步骤/守卫/证据/分支，文本即推导文档，可回放同一推导链）
- [ ] 撤销/重做的真正实现（当前只移动指针不删步骤）
- [ ] 版本化上下文折叠（读写双向索引）
- [ ] Split 分支的后续求解（切完未消费）

### 战术层
- [ ] 二次方程求解（判别式分支切割）
- [ ] 循环方程求解（多前驱 DAG + 线性系统）
- [ ] 一般丢番图按定理拒答接线进工作流（UNDECIDABLE 理由通道）
- [ ] 多参数函数偏导、绑定体内微分（依赖量词/积分地基）

### 数域扩展（Risch 前置）
- [ ] 隐函数求导命令：依赖声明（y 关于 x）入上下文 + 求解导数（Diff 已拒等式，入口已留）
- [ ] ℚ(i)[x]/ℚ(i)(x) 系数环挂载：poly/ratfunc 的闭项系数吸收通道（Ring 吸收 ℚ(i) 常数子项）+ project 多环阶梯（ℚ[x] 落空后试 ℚ(i)[x]）；消费方审计（cad/tactics/workflow 的 Q_RING 硬编码处按能力改派）
- [ ] ℤ[i] 高斯整环：范数带余除法 + gcd（欧几里得）+ 高斯因式分解（参考 fricas gaussfac.spad）
- [ ] ℚ(α) 代数扩张通用化（mod-m 余式 + Thom 编码；元素表示取模 minpoly 多项式形——参考 fricas algext.spad SAE 的 Rep := UP）
- [ ] ℚ(α) 代数扩张（mod-m 余式 + Thom 编码）
- [ ] 参数分式域 ℚ(t₁..tₙ) 作系数环
- [ ] 多变量 GCD（接入 ratfunc 约简标准形）

### 序与根比较（arch §7.4 分层，消费 CAD/判定管线）
- [ ] L2 区间算术比较层：可计算超越函数的任意精度区间求值，分离即判、重叠即 Unknown（接 decide 管线常数比较通道；裸浮点禁止入符号通道）
- [ ] L3 图书馆序引理：单调性/零点集/周期/凸性作为 FunctionDecl 数据入册（准入纪律同导数模板：无条件可证才入册）
- [ ] L4 超越根对象：(方程, 隔离区间) + 加细协议；等号仅在可证时成立
- [ ] 条件化答案容器：端点序未决时按参数条件分支给出答案 + 完备性声明 complete/partial（arch §7.5 出口 1）

### 公共算法机器（Risch 前置）
- [ ] Zassenhaus 因式分解（ℤ 提升）
- [ ] 部分分式、Hermite 约化
- [ ] 子结式链（结式的序判定推广，Thom 编码依赖）
- [ ] 超越塔结构（tower 表示 + 初等扩张判定）——FriCAS 对应层；微分塔上先行，积分塔随后

### 远期
- **终极目标三项**：完整 Risch（参数积分与超越数积分，地基完工前不启动）；完整 CAD（一维胞腔 → 多变量实代数投影 + 胞腔分解）；Gröbner 基方法（理想属员/方程系统/代数预处理，属公共算法机器层）
- 定积分、极限级数、求和差分、ODE、不等式求解（消费上述地基）
- transseries
