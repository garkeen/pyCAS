# Progress

当前实现状态与下一步。设计裁定以 `cas_v4_arch.md` 为准，工程纪律以 `AGENTS.md`
为准。v3 架构文档已删除，其仍有效的章节（语言契约、验证独立性、判定与验证、验收
方法论）已并入 `cas_v4_arch.md`。

**文档语言约定：本文档与 `AGENTS.md`、`cas_v4_arch.md` 等设计文档一律用中文；
「代码与注释统一英文」只约束源码（`.py` / `.dsl`），不约束文档。**

## 目录结构

| 路径 | 内容 |
|---|---|
| `cas/syntax/` | `term`（驻留项）、`pattern`（模式元语言）、`match`、`termpath`、`abstract` |
| `cas/kernel/` | `verdict`、`model`、`evidence`、`scope`、`context`、`commit`、`store`、`services`、`ids`、`mode` |
| `cas/workflow/` | `workflow`、`command`、`artifact`、`task`、`event`、`constraint`、`branch`、`ids` |
| `cas/math/domains/` | `base`、`z`、`q`、`qi`、`poly`、`ratfunc`、`polytools`、`linalg`、`module` |
| `cas/math/` | `context`、`project`、`qarith`、`decide`、`diff`、`integrate`、`cad`、`realroot`、`tactics`、`piecewise`、`domcond`、`rules`、`simplify`、`judge`、`constraints`、`loader`，以及 `base/`、`elementary/`、`calculus/`、`solving/` |
| `cas/runtime/` | `registry`（RuntimeBuilder）、`runtime`（Runtime、new_workflow）、`bootstrap`、`algorithms`、`services` |
| `cas/frontend/` | `parser`、`pprint`、`session`、`repl`；根目录 `repl.py` 是入口外壳 |
| `cas/api.py`、`cas/errors.py` | 前端计算门面；共享异常 |

## 依赖方向

由 `tests/test_v4_invariants.py` 机械强制：

- `syntax` 只依赖标准库与 `cas.errors`。
- `kernel` 只依赖 `syntax`：不导入任何具体 math / workflow / frontend 模块，且
  不含工作流概念名。
- `workflow` 只依赖 `syntax` + `kernel`：checker、判定服务与算法由 runtime 注入，
  故其中不存在 `cas.math` 导入。
- `math/domains` 依赖 `syntax`；其余 math 模块可用 `syntax`、`kernel`、`workflow`
  与 `math/domains`。math 永不导入 `runtime`。
- runtime 是装配者：`bootstrap()` 装入全部 math 模块，把声明查询面与装配配置
  收进 `MathContext` 返回（不写模块句柄）；应用显式接收返回的 `Runtime`。
  import 期与装配期都不修改全局状态。
- 前端显式接收 `Runtime` / `Session`：parser、printer、API 不读取进程级 runtime；
  math 模块注册 `CommandSpec`，Session 构造时绑定 callable `CommandDescriptor`。

## v4 迁移状态

| 阶段 | 内容 | 状态 |
|---|---|---|
| 1 | syntax 拆分；模式元语言（PatternVar/PatternSeq 不是 Term） | 完成 |
| 2 | 内核模型：Scope / Judgment / Requirement / Evidence / StepProposal / commit / CheckerRegistry | 完成 |
| 3 | 废除 Derivation ADT；命令产出提案，checker 验证实例而非重跑搜索 | 完成 |
| 4 | Artifact / Task / Event 三图分离 | 部分：三图与约束已有真实消费方，历史截断与 Applicability 缓存尚未建 |
| 5 | 持久化 Scope 树取代可变 Context | 完成 |
| 6 | math 模块归入 `cas/math`，显式 `install(builder)` 装配 | 完成 |
| 6b | 声明查询面与装配配置显式传参（`MathContext`），取代装配期写模块句柄 | 完成 |

不变量 1 / 2 / 14 / 16 / 18 已绿，另有四条依赖与引用方向门禁、两条 C3 门禁
（math 层不得持有模块级装配状态；被删句柄不得回潮），以及数学语义 head 字面量、
求解器内嵌验证器、声明 DSL 准入三条全库门禁；无 xfail 项。
「红灯先挂」策略现在只适用于确有跨阶段迁移待做之处。

## 实现纪律

`AGENTS.md` 载有六条硬约束：禁止硬编码、禁止特判（案例导向或简化实现）、严格按
能力字段做域分派、自动化算法只做可判定内容、职责单一、名字对得起语义。

据此已落地：

- 数学语义 head（初等函数与常数）在 `math/elementary/declarations.dsl` 声明并经
  builder 装配。该文件还承载解析层别名（`ln -> Log`、`sqrt -> Sqrt`）与算法角色
  （`logarithm -> Log`），故 parser 与微分器都不写死函数名。准入纪律对 DSL 文本
  机械化检查。
- 签名 head（Plus/Times/Power、各比较、And/Or/Not、Quote/Piecewise）在算法中仍可
  分派：它们是项语言自身的结构。
- 具体域单例改为能力查询（`find_domain`）：CAD 取唯一有序域，丢番图碎片取唯一
  欧几里得整环，投影基域同法选取。K[x]/K(x) 的系数环由装配期选定并随上下文传参，
  域包不自举缺省环。
- 声明与装配配置只有一个通道：`MathContext`（声明查询面 + `eq_stages` + 投影阶梯
  + 系数环）作为首参数显式传给算法；`project.build_ladder` 值化产出阶梯
  （`ProjectionStage` 是数据，不是注册项），math 层不持有任何模块级装配状态。
- 检查器由工厂装配（`register_checker(id, factory)`，上下文在 runtime 组装完成后
  注入），新增 math 模块不必再改第二处硬编码清单。
- 积分验证器住在 `math/calculus/integration/verify.py`，与求解器分家；门禁拒绝任何
  checker 导入自己的求解器模块。
- 工作流步骤记录命名为 `WorkflowStep`，与内核 `Step` 区分。
- runtime 不保存进程级装配槽；REPL 通过显式 `Runtime` 创建 `Session`，Session 在构造时
  校验完整的 command handler 表，REPL 只按 descriptor handler 通用分派。

## 已实现地基

- 驻留项层与 AC 规范形；模式元语言与项层分离；绑定抽象/实例化基于 de Bruijn 索引。
- 精确有理字面算术；域系统 ℤ、ℚ、ℚ(i)、K[x]、K(x)，带能力字段与投影阶梯。
- 判定管线返回 `Verdict` ADT 与四种 `Reason`，片段外诚实未决。
- 内核：追加式账本、带可见性与逃逸检查的作用域树、条件生命周期（清偿与否证）、
  十步 commit 及其可证明的四步特化。
- 规则引擎由声明规则驱动；auto 规则无守卫，并按成本严格下降终止。
- 一维 CAD（Sturm 实根隔离）、有序首中语义的分段容器、审慎的分段求导、分段方程
  求解、多项式片段积分与三值独立验证器、线性代数（行阶梯、秩、核、求解、Bareiss
  行列式）、结式与 Yun 无平方分解、线性丢番图碎片与整数根、项上约束求解、分支
  分裂/合并、带卫生检查的声明/定义。
- REPL 覆盖 claim/norm/solve/subst/split/diff/rules/apply/integrate/check/steps/show/
  focus/undo，以及两种非项行形式 `u := x^2`（定义）与 `A : Real`（声明），
  一律经前端门面；命令接受 `#N` 步骤引用，未给引用时作用于焦点。

- 定义展开是**唯一的自动代换通道**（`math/definitions.py`）：别名图无环（定义期检查）
  ⇒ 展开必停机，超预算 `BudgetExceeded`；计算入口与所有 checker 在比较前展开，`Quote`
  内容不展开（held 数据），`d/d(定义)` 与 `solve 定义` 拒答。等式永不自动展开。
- 判定层：账本等式的**闭包通道**（`math/base/equality.py::closure_decide`，并查集 +
  同余 + 类代表定向重写）取代了双向盲目代换；`decide` 没有搜索深度参数（改用已访问
  事实环保护），`No` 只在有证据时给出（闭合值不同 / 匹配 `Ne` 事实）；三值恒等
  `identity_verdict` 取代 `equal()`，使"不可复核"不再被报成"被否证"。
- 步骤引用：`Command.premises` 是元组（内核 Step 本就多前驱）；REPL 支持 `#N`、
  `show #N`、`focus [#N]`；`check` 由前驱图回溯定位原始方程（缓存指针 `self.original`
  已删除），守卫按该步所在作用域的假设帧判定（`wf.assumptions_of`）。
- 焦点与会话光标分离：`focus` 只是默认引用，每条步骤记录自己实际用过的前驱。

- 作用域为**版本链**：`extend` 产新 id（Γ 对每个 id 冻结，分支从固定版本父分叉），
  `lineage_of`/`head_of` 区分谱系与版本；引入者反向索引与否证反向索引消除每 commit 全扫。
- 真 undo/redo：事件视图是带 redo 栈的分支指针（`visible()` 有真实消费方），workflow 的
  scope 指针随 revision 回退，declare/define 记为事件。
- 语言表面全声明化：无隐式大小写折叠；binder 由 DSL `binder <Head>` 声明并经注入通道交给
  语法层；`src` 打印形态有往返清单测试。
- 分段提升有预算（`BudgetExceeded` 诚实拒答）与相邻同值支合并。
- 投影元由域自身消费（`element_is_zero`/`element_to_term`），投影层不嗅表示；多项式视图
  同为能力查询（`element_poly` 消失视图 / `element_as_poly` 元素本身），消费方不按类型
  识别表示；序比较按值域证据分派（非实常数上诚实拒答）。

阶段 0–3 的判定、定义、步骤引用和回归钉子已完成；阶段 4–7 已落地：

- 手动等式代换：`equality.trans` 与 `congruence.lift` 独立 checker，声明驱动
  `lift` 策略，Piecewise 分支条件、Power 整数指数、Derivative/Quote 禁止、绑定体
  再抽象和积分边界条件均进入证据/Requirement 通道。
- 参数化线性求解：`cas/math/linearform.py` 成为唯一线性形式实现；`solve_linear`
  允许其它符号作为系数，`solve_linear_with_condition` 显式返回斜率非零条件。
- 前端命令注册面：数学模块注册 `CommandSpec`，Session 将其与 handler 绑定为不可变
  `CommandDescriptor`；REPL 通用分派，`apply` 无路径时列出全部匹配位置；`split` 接真实
  分支作用域并提供 `enter`/`merge`。
- 判定和维护：`is_zero`/`back_substitute` 传播假设帧，定义展开读依赖进入
  `TrackedContext`，`ScopeServices` 使用按 scope 版本键控的有界缓存。
- 文档、DSL 准入门禁、随机同余/参数求解台架和 REPL 冒烟测试已同步。

阶段 3 历史验证：`python -m pytest -m "not random"` 为 317 passed、12 deselected；
`python -m pytest -m random` 为 12 passed、317 deselected；合计 329 项全绿。

### 四阶段类型与数据模式迁移验收

- 阶段 1–4 的类型与数据模式迁移已完成：frontend 显式注入、Session handler 装配和旧入口清理已落地。
- 阶段 3 的历史验收证据保持记录；阶段 4 新增 frontend 边界、动态属性和核心注解 AST 门禁。
- 架构收敛与硬约束治理落地：
  - 静态门禁与声明通道：修复 ruff 格式化；显式导出 `CommandSpec`；DSL 为 binder（如 `Integral`）增加 `print` 符号声明与 `lift` 策略；积分 checker 与 pprint 彻底消除写死 head 清单。
  - 核心命名与未决常量：`_A` → `_assumption_frame`、`_ok` → `_accepted`、`conditional` → `conditionals`，特殊未决常量统一为 `T.UNDEFINED`，移除 `Applied.subst` 别名。
  - 缓存边界化与防泄漏：`poly.py`、`ratfunc.py` 的单例域缓存设上限与淘汰；`pattern.py` 的模式变量驻留表设上限与淘汰；`tests/contract/test_v4_invariants.py` 追加模块级缓存有界性静态门禁。
  - 既有能力导出与死代码裁定：REPL 接入 `redo` 命令并注册进命令表；`api.py` 导出 `solve_diophantine_linear` 和 `integer_roots`；删除无用的 `TaskStore.subtasks` 与 `KernelStore.all_judgments`；裁定保留对应 CAD/Risch 后续路线图的 `abstract.py`、`connected_components`、`is_linear`。
  - 契约门禁转绿：落实并强化不变量 3、4、5、6、11、13、14、16、18、21。
- 本轮按会话纪律未重新运行测试、mypy、Ruff、compileall 或其它验收命令；因此不把阶段 4 写成已重新验收。

## 未实现（下一步）

- 交互通道：工作流序列化与回放；带版本的上下文折叠；后续求解消费已分裂的分支。
- 战术层：带判别式分支的二次求解；循环方程求解；一般丢番图拒答接入 UNDECIDABLE；
  多变量与绑定体内微分。
- Risch 之前的数域：poly/ratfunc 的 ℚ(i) 系数吸收；高斯整数；一般代数扩张；参数化
  分式域；多变量 gcd。
- 序与根比较：区间算术层；声明的序引理；超越根对象；条件答案容器。
- 公共算法机器：Zassenhaus 因式分解；部分分式与 Hermite 归约；子结式链；微分塔。
- 三角/指数展开与同类项收集。正是这一能力缺口让循环 exp/sin 积分停在「未决」：
  微分层能验证它，但判零通道还不能把差值展开为零。
- 未决设计：分支合并在不引入蕴含引入规则（Γ, C ⊢ P 推出 Γ ⊢ C → P）的前提下，
  无法独立复核「各支都回答了 P」。这是一条尚未采纳的新内核规则。

## 已知缺陷（已定位，未修）

阶段 4 已消除旧的 runtime dispatch、隐式 parser/printer/API 和后绑定 handler 接口。仍待
处理的是上述长期能力缺口与工作流序列化、分支蕴含引入规则。源码与测试不保留旧命令/旧分类兼容包装。

## 语言与引用纪律

源码（`.py` / `.dsl`）一律英文，且不得引用设计文档：理由以直述方式写清，不把读者
指向某份文档去追。两条都是 `tests/contract/test_v4_invariants.py` 里的机械门禁
（`test_source_is_english_only`、`test_source_cites_no_design_document`），覆盖
`cas/`、`tests/` 下全部源文件。**文档不受此约束**：设计文档与本文档
保持中文。
