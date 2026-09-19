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
| `cas/math/` | `project`、`qarith`、`decide`、`diff`、`integrate`、`cad`、`realroot`、`tactics`、`piecewise`、`domcond`、`rules`、`simplify`、`judge`、`constraints`、`loader`，以及 `base/`、`elementary/`、`calculus/`、`solving/` |
| `cas/runtime/` | `registry`（RuntimeBuilder）、`runtime`（Runtime、new_workflow）、`bootstrap`、`dispatch`、`algorithms`、`services` |
| `cas/frontend/` | `parser`、`pprint`、`repl`；根目录 `repl.py` 是入口外壳 |
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
- runtime 是装配者：`bootstrap()` 装入全部 math 模块并绑定只读查询面，不存在
  import 期全局状态修改。
- 前端只经 `cas/api.py` 与 `cas/runtime/dispatch.py` 触达计算，不导入
  `cas.math` 或 `cas.kernel`。

## v4 迁移状态

| 阶段 | 内容 | 状态 |
|---|---|---|
| 1 | syntax 拆分；模式元语言（PatternVar/PatternSeq 不是 Term） | 完成 |
| 2 | 内核模型：Scope / Judgment / Requirement / Evidence / StepProposal / commit / CheckerRegistry | 完成 |
| 3 | 废除 Derivation ADT；命令产出提案，checker 验证实例而非重跑搜索 | 完成 |
| 4 | Artifact / Task / Event 三图分离 | 部分：三图与约束已有真实消费方，历史截断与 Applicability 缓存尚未建 |
| 5 | 持久化 Scope 树取代可变 Context | 完成 |
| 6 | math 模块归入 `cas/math`，显式 `install(builder)` 装配 | 完成 |

不变量 1 / 2 / 14 / 16 / 18 已绿，另有四条依赖与引用方向门禁；无 xfail 项。
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
  欧几里得整环，投影基域同法选取。K[x]/K(x) 的缺省系数环由装配期注入，不再由
  域包自举。
- 投影阶梯以 `ProjectionStage` 注册，而非写死 if 链。
- 积分验证器住在 `math/calculus/integration/verify.py`，与求解器分家；门禁拒绝任何
  checker 导入自己的求解器模块。
- 工作流步骤记录命名为 `WorkflowStep`，与内核 `Step` 区分。
- `cas/runtime/dispatch.py` 以模块 `__getattr__` 转发到已装配的 runtime，取代逐方法
  手写转发。

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
- REPL 覆盖 claim/norm/solve/subst/split/diff/rules/apply/integrate/check/steps/undo，
  一律经前端门面。

- 作用域为**版本链**：`extend` 产新 id（Γ 对每个 id 冻结，分支从固定版本父分叉），
  `lineage_of`/`head_of` 区分谱系与版本；引入者反向索引与否证反向索引消除每 commit 全扫。
- 真 undo/redo：事件视图是带 redo 栈的分支指针（`visible()` 有真实消费方），workflow 的
  scope 指针随 revision 回退，declare/define 记为事件。
- 语言表面全声明化：无隐式大小写折叠；binder 由 DSL `binder <Head>` 声明并经注入通道交给
  语法层；`src` 打印形态有往返清单测试。
- 分段提升有预算（`BudgetExceeded` 诚实拒答）与相邻同值支合并。
- 投影元由域自身消费（`element_is_zero`/`element_to_term`），投影层不嗅表示；序比较按
  值域证据分派（非实常数上诚实拒答）。

验证：`tests/`（unit/contract/integration/regression）通过；`tests/random/` 10 个台架通过（各台架自证若干条数学性质）。测试按种类分目录、按 marker 可筛（`pytest -m <kind>`）。

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

- 打印机的数值因子合并不完整：含多个数值因子的 `Times` 只保留最后一个，故
  `to_str(parse("-2*x")) == "2*x"`（丢符号）、`to_str(parse("x^-2")) == "x^(2)"`。
  交互路径不受影响（REPL 先 `fold`），程序化打印会丢信息；修法是把数值因子按精确有理数
  收敛后再渲染（既有 `3/4` 形态已是这套约定）。
- `cas/math/tactics.py::_lin_core` 仍对投影元做 `isinstance(RatFunc/Poly)` 分派：新表示的
  多项式域会被它拒答（诚实拒答，不致命）。修法是给域协议加「单变量多项式视图」查询。

## 语言与引用纪律

源码（`.py` / `.dsl`）一律英文，且不得引用设计文档：理由以直述方式写清，不把读者
指向某份文档去追。两条都是 `tests/contract/test_v4_invariants.py` 里的机械门禁
（`test_source_is_english_only`、`test_source_cites_no_design_document`），覆盖
`cas/`、`tests/` 下全部源文件。**文档不受此约束**：设计文档与本文档
保持中文。
