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

已知容忍的结构债：workflow→math 顶层依赖（v3 遗留，目标位置 math/*/checkers.py，阶段6 迁移；已挂 xfail 门禁）；syntax/termpath、match → `cas/errors`（基础设施，留根）。

**已清除的债（§四 引用方向）**：kernel → 具体数学模块（`kernel/context.py` 原先在
`check_and_assume`/`branch`/`decide`/`contradicted` 里惰性导入 `cas.math.decide`）。
判定操作移居 `cas.math.decide.check_and_assume` / `branch`（math → kernel 引用
`Context`/`Branch`，方向合规），`Context` 只留纯数据与记账。内核侧不再定义
`ArtifactId`/`TaskId`/`EventId`/`RevisionId`；新增门禁
`test_依赖方向_syntax不依赖上层`、`test_依赖方向_kernel不依赖数学与工作流`、
`test_引用方向_内核不认识工作流概念`。

## v4 迁移路线图（v4 §十一 六阶段）

| 阶段 | 内容 | 状态 |
|---|---|---|
| 1 拆语法（模块落位） | 语法入 syntax/，前端入 frontend/ | ✅ 2026-09-10 |
| 1 拆语法（模式元语言） | PatVar/PatSeq 移出 Term（Pattern 独立层次） | ✅ 2026-09-10（本次，不变量 2 转绿） |
| 2 新内核模型 | Scope / Judgment / Evidence / StepProposal / commit / CheckerRegistry | ✅ 2026-09-10（2a 模型+协议，2b 接线） |
| 3 拆除 Derivation ADT | 命令只生成 proposal；checker 语义 id；规则实例验证不再搜索 | ✅ 2026-09-10（不变量 14 转绿；checker 阶段6 归位 math/*） |
| 4 Artifact/Task/Judgment 分离 | workflow 三图分离 | ⬜ 未开始（不变量 16 红） |
| 5 持久化 Scope 树 | 可变 Context → 父指针树；undo/redo 移 revision 指针 | ✅ 2026-09-10 |
| 6 数学模块迁移 | library → math/*，install(builder) 装配 | ✅ 2026-09-10（`library/` 已删除） |

不变量 CI 门禁（`tests/test_v4_invariants.py`）：**1/2/14/16/18 全部转绿**；另有
§四 依赖方向/引用方向门禁 4 条（其中 workflow→math 债务 1 条挂 xfail，阶段6 转绿）。

### 执行模式落位（AGENTS.md §四.2，2026-09-10）

`cas/kernel/mode.py` 定义 `ExecutionMode`（interactive 默认 / derivation / audit），
`commit` 与 `TrackedContext` 接受模式。落位的是**记账粒度**，不是正确性：

- **interactive**：不记读依赖（`Step.reads` 为空）；**清偿登记推迟**——条件照判
  （否则被否证的守卫会被静默放过，那是正确性问题），只是暂不把已证条件记成
  `Discharge`，故 `applicability` 报 `Conditional`。
- **derivation**：读依赖按 Step 粒度去重；提交时清偿。
- **audit**：读依赖保留每次出现（read 粒度）；提交时清偿。
- 读依赖以 `TrackedContext` 的记录为准（§6.11 的唯一通道），不再用 checker 自报的
  `Accepted.reads` 二次合并（原先那次 merge 是冗余的，还会造成重复计数）。

门禁（`tests/test_kernel_model.py`）：`test_执行模式不改变结论`（三模式下结论
proposition 与 requirements 逐位相同——§四.3 的机械检查）、
`test_条件被否证在各模式下都拒绝`、`test_interactive不记读依赖也不登记清偿`、
`test_audit保留每次读取而derivation去重`。

未落位（属可追溯性层，不影响健全性，§四.7）：`Applicability 缓存`与
`历史截断 N 代`——历史图在阶段4 才建。

### 阶段 4（有消费者子集）：三图分离（2026-09-10）

按 v4 §8.5 把「计算产物 / 任务 / 操作历史」三张图分开，只建**有消费者**的部分
（v4 §三：「一个模块只有在出现实际代码时才拆分」），不做空壳：

| 文件 | 内容 | 消费者 |
|---|---|---|
| `workflow/ids.py` | ArtifactId/TaskId/TaskCandidateId/EventId/RevisionId | —— 内核不认识工作流概念（§四） |
| `workflow/artifact.py` | `Artifact{id,scope,value,produced_by}` + 追加式 store | 每个步骤的内容即一个 Artifact |
| `workflow/task.py` | `Task{id,scope,request,parent}`、`TaskCandidate{task,artifact,validation}` + store | 有请求形状的命令开任务并登记候选 |
| `workflow/event.py` | `Event{id,command,inputs,outputs,parent_revision}`、`Ref`、EventLog（追加式 + revision 指针 + 倒排索引） | 每步一条事件；undo/redo |

要点：

- **Artifact 无真假、不能作数学前提**（§8.2 / 不变量 4）。「下一步直接吃上一步结果」
  走的是 Artifact 通道（重写吃项），不是结论通道。
- **TaskCandidate 状态由数据推导**（§8.4）：`validation is None` → unverified；
  有验证但适用性非 Applies → conditional；否则 validated。没有可变 `verified=True`。
- **Event.outputs 是跨层引用唯一出口**（§四）：产出物以 `Ref(kind, id)` 标记。
  **为什么要 kind**：`NewType` 运行期只是 `int`，`ArtifactId(1)`/`TaskId(1)`/
  `JudgmentId(1)` 彼此相等，倒排索引会互相碰撞——这是实现时被测试抓出来的真缺陷。
- **undo/redo 只移 revision 指针**，事件列表不删、内核账本不删（§8.9 / §四.5）。
  测试钉住：undo 之后 `len(events)` 与步骤数都不变。
- **applicability 查询接线**（§6.10）：`Workflow.applicability_of(step)` 由工作流
  提问、内核按作用域计算——原先内核算了但没人问。
- `inputs` 记前驱的**步骤 id**（工作流侧编号），`outputs` 记内核 id —— 内核对
  产生零感知，方向合规。

已补（见下两节）：§8.8 Branch（含 `NeedsSplit` 开分支接线）与 §8.6 Constraint。

验收：`tests/test_workflow_graphs.py` 8 条；全量 104 passed + 1 xfailed；stress 10 passed。

### 阶段 4 收尾：约束求解（不可信侧）+ 一个真缺陷（2026-09-10）

**求解器** `cas/math/constraints.py`：从等式约束提取未知量的线性系统并求解。
- `_decompose`：**句法**线性形式分析（`Σ cᵢuᵢ + c₀`），不靠化简器、不靠语义判零，
  因此对超越系数同样有效；`sin(u)`／`u⁻¹`／`u·u` 一律拒答（非线性不硬凑）。
- `TermField`：把**项**适配成域接口（`is_zero` 走域投影、四则走域标准形），
  从而直接复用 `linalg.solve_system` 的通用高斯消元，不重写消元器。
- `Workflow.solve_constraints(unknowns)`：求解 + 逐条经 `constraint.satisfied` 复核。
  求解器自报不算（§7.3）。

修掉两个自己引入的缺陷（都是测试/实测抓出来的）：
1. `Times` 分解漏乘同因子里的常数部分，把 `-1·v` 的系数算成 `+1` → 整个系统判成
   不相容。已加回归测试 `test_系数带常数因子不丢号`。
2. 系数归一前就交给消元器（`0 + 1` 这类未折叠形式），使主元判零与除法失效。

**真缺陷（既有代码，非本次引入）**：`integrate._judge_zero_diff` 在判零通道覆盖不到
时返回 `False`，等于**把「判不了」报成「不是原函数」**——伪造否证，违反
「未找到与不存在是两个结论」。触发点正是 v4 §9.5 自己的例子：`∫e^x sin x dx` 的
原函数 `(e^x(sin x − cos x))/2` 经微分层求导后是
`1/2e^x(cos x + sin x) + 1/2e^x(sin x − cos x)`，需**展开合并同类项**才能看出等于
`e^x sin x`，而三角基归零阶段尚未重建（`decide.py:994` 的 TODO），三条判零通道
（`fold` / 域投影 / ratfunc 判等）全部落空。

修法：`_judge_zero_diff` 与 `verify_antideriv` 改为**三值**（True/False/None），
`None` 只表示能力缺失；`calculus.antiderivative` checker 把 `None` 映射为未决而非
rejected。于是循环积分那条链现在是「求解成功、验证诚实未决」，而不是「正确解被判
dead」。stress 调用点同步改为只认 `is True`。

**未做（真实缺口，需立项）**：三角/指数表达式的**展开与同类项合并**（原 `cas.trig.
trig_reduce` 已随函数结构层拆除而未重建）。不补它，§9.5 的原函数永远只能到
「未决」——这是能力缺口，不是纪律问题。

验收：`tests/test_constraint_solver.py` 5 条；全量 117 passed + 1 xfailed；stress 10 passed。

### 阶段 5：持久化 Scope 树接管可变 Context（2026-09-10）

删除 v3 的可变 `Context`（`entries` 列表 + `marks`/`rollback` 位置指针撤销），
职责一分为三，各归其位、互不重复：

| 角色 | 位置 | 说明 |
|---|---|---|
| 权威 | `kernel/scope.py` `Scope` + `ScopeStore` | 不可变、父指针；谁绑定什么、哪些假设可见 |
| 判定层投影 | `kernel/scope.py` `Assumptions` | `extended` 产生新对象；无克隆、无撤销 |
| checker 读通道 | `kernel/context.py` `TrackedContext` | 每次读取进入 `Step.reads` |

迁移要点：

- `math/decide.py`：`ctx` → `assumptions`（73 处重命名）；7 处 `for e in ctx.entries:
  f = e.fact` → `for f in assumptions:`（`kind`/`origin` 从未被读，故载体只需假设项）。
- 三处「克隆 + 就地写入」改为 `extended`：`satisfiable`、`piecewise._agree`、
  `decide.branch`。`check_and_assume` → `extend_checked`（返回新假设集，不改原对象）；
  `branch` 返回 `[(条件, 该支假设集|None, 状态)]` 三元组。
- `workflow/checkers.py` 的 `WorkflowServices` 直接 `Assumptions.of(scope_store, scope_id)`，
  **Scope → Context 的桥接消失**。
- `decide.py` 里 `kernel.context ↔ decide` 的延迟导入环随之拆掉（默认上下文构造
  移出 decide）。

**没有 marks/rollback 是设计而非缺失**：撤销由 revision 指针完成（§8.9），假设集
本身不可变，所以「回退」不需要可变状态。门禁 `test_阶段5_旧可变上下文已删除`
钉住 `Context`/`Entry`/`Branch` 不得复活。

验收：全量 119 passed + 1 xfailed；stress 10 passed（41 条性质）。

### 阶段 6：显式装配（`library/` 删除，v4 §7.1）（2026-09-10）

按 v4 §7.1 建 `cas/runtime/`，删除整个 `library/` 包，**三处 import 期全局状态全部消除**：

| 旧（import 期自注册） | 新 |
|---|---|
| `library/__init__.py` 的 `load_all()` | `math/elementary/module.py` 的 `install(builder)` |
| `project.py` 的模块级 `_install_base_domains()` + lookup 回填 | `math/domains/module.py` 的 `install(builder)` + `project.bind_domains` |
| `decide.py` 的模块级 `register_eq_stage("ledger_decide", ...)` | `math/base/module.py` 的 `install(builder)` + `decide.bind_eq_stages` |

`cas/runtime/`：`registry.py`（`RuntimeBuilder`，**唯一写入口**，只设确有内容的五类
注册表——空注册表就是空壳）、`runtime.py`（`Runtime` 只读查询面，取代原 library 查询面）、
`bootstrap.py`（`bootstrap()` 显式装配，顺序即依赖：常数 → 域 → 阶段）、
`dispatch.py`（运行期查询入口，首次调用触发装配）。

**依赖方向（§四）在实现层面被遵守**：`runtime → math`（bootstrap 拉全部数学模块），
反向禁止。所以 math 模块读声明由**装配期注入**（`bind_runtime`），不能自己 import
runtime；未注入时查询**报错**而不是返回 None——静默 None 会把「忘了装配」变成难查的
错答案。frontend 允许 import runtime，故 parser/pprint 直接用 `dispatch`。

**入口必须显式 bootstrap**：`repl.py` 与全部 stress 脚本都加了 `bootstrap()`，
`tests/`、`stress/` 各加 `conftest.py`。这一步由**响亮失败**验证过——漏加 bootstrap 的
两个 stress 脚本立刻报「未装配」，而不是静默降级。

改名：`rules.library_ruleset()` → `rules.declared_ruleset()`（语义来源不再是图书馆）。

门禁新增 `test_依赖方向_math不依赖runtime`、`test_import数学模块不产生注册副作用`
（干净进程里 import 数学模块后常数表/域阶梯/判等阶段/注入面都须为空）。

**未完成的既有缺口（非本次引入）**：AGENTS.md §二 要求「常数、函数、导数模板、
定义域条件的声明必须统一进 **DSL 数据文件**，禁止 Python 代码直注册」。当前这些声明
仍是 Python（`math/elementary/module.py` 里的 `builder.declare_function(...)`），
旧 `library/elementary.py` 亦然——所以该条从来未兑现。要做需先定声明 DSL 的语法
（现只有规则行 DSL），属设计决定。

验收：全量 123 passed + 1 xfailed；stress 10 passed（41 条性质）；pyflakes 干净。

### 阶段 6 尾项：checker 归位 `math/*/checkers.py`，`workflow → cas.math` 债务清零（2026-09-10）

checker 验证的是**数学**，住在 workflow 里会让 `workflow → cas.math` 反向依赖
（§四 禁止）。按 v4 §三 的目标位置归位：

| 模块 | checker |
|---|---|
| `math/base/checkers.py` | assumption.entry / both_sides.operate / equality.normalize / rule.instance / substitute / branch.split / branch.coverage / constraint.satisfied |
| `math/base/equality.py` | `normal_form` / `equal`（域标准形即判定过程，§零.1 的实现落点） |
| `math/calculus/differentiation/checkers.py` | calculus.derivative |
| `math/calculus/integration/checkers.py` | calculus.antiderivative |
| `math/solving/equations/checkers.py` | solve.back_substitute |

`cas/workflow/checkers.py` 删除。workflow 侧改为**注入**三样它需要但不能自己取的东西
（都由 `cas.runtime.new_workflow()` 装配）：

    store        内核账本（含 kernel 自带 + math 各模块的 checker）
    services     判定服务 ScopeServices（按作用域判定，条件清偿在正确分支上下文进行）
    algorithms   算法门面 Algorithms（domain_of 投影、solve_linear_constraints 求解器）

于是 workflow 源码里**没有一行 `cas.math`**（门禁 `test_依赖方向_workflow不依赖具体
数学模块` 从 xfail 转绿）。缺注入时构造即报错，不做静默降级。

前端同样不直连 math（§四：frontend → api/workflow/runtime）：REPL 的 `norm` 命令经
`dispatch.domain_normal_form` 转发。

**v4 §十二 门禁现状：1/2/14/16/18 加 §四 依赖方向/引用方向全部转绿，无 xfail。**

验收：全量 **124 passed（0 xfailed）**；stress 10 passed（41 条性质）；pyflakes 干净；
REPL 端到端正常。



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

### 阶段 2a：内核模型与提交协议（2026-09-10）

按 v4 §6 建内核数据模型与 `commit`，**尚未接旧验证器**（2b 才接线，届时
不变量 16 具备转绿条件）。新增 `cas/kernel/`：

| 文件 | 内容 |
|---|---|
| `ids.py` | ScopeId/RequirementId/JudgmentId/StepId（NewType，防互串） |
| `model.py` | Declaration/Definition/Assumption、Requirement(+Reason)、Judgment、Step、ContextReadSet、Discharge、`Applicability` 封闭层次 |
| `scope.py` | `Scope`（不可变、父指针）+ `ScopeStore`（可见性、定义可见表、局部符号逃逸检查） |
| `evidence.py` | Evidence、`CheckResult` 封闭层次（Accepted/Rejected/UnknownResult）、Checker 协议、`CheckerRegistry` |
| `services.py` | `KernelServices` 协议 + `NullServices`（诚实缺省：一律 Unknown）+ `DecideChecker` + 显式装配 `register_core_checkers` |
| `store.py` | `KernelStore` 追加式账本（结论/条件/步骤/清偿/否证）+ 按作用域计算 `Applicability` |
| `commit.py` | `StepProposal` / `GuardPolicy` / `CommitResult` 封闭层次 / 十步 `commit` |

要点（均有测试钉住）：

- **未验证候选不落地**：checker 返回 Unknown 时任何 GuardPolicy 都不写账
  （不变量 16 的内核机制）。`GuardPolicy` 只管**条件清偿**的未决（§6.9 第
  7–9 步 Proved/Refuted/Unknown），不是「结论没验过也放行」。
- **清偿不修改原结论**（§6.10）：条件全部记在结论上，清偿只新增 `Discharge`，
  查询时 applicability 变 `Applicable`；被否证则变 `Inapplicable`，原结论保留。
- **作用域权威**：前提不可见（子→父、兄弟分支）拒绝提交；祖先对后代可见。
- **不 import 具体数学模块**（v4 §四）：判定经 `KernelServices` 注入，内核
  源码只依赖 syntax。
- 无条件、无前驱的情形走四步特化（AGENTS.md §四.4），是十步的可证明子集。

验收：`tests/test_kernel_model.py` 16 条；全量 78 passed + 2 xfailed。

### 阶段 2b：接线（2026-09-10）

把工作流的验证从「自己验」改成「交 `kernel.commit` 验」，并删除旧验证器。

- **`cas/workflow/checkers.py`（新）**：八个旧 verifier 搬成 checker adapter，
  签名改为 v4 §6.7 的 `check(proposal, context, services) -> CheckResult`。两处
  实质变化：不再读工作流内部状态（前驱命题由 `commit` 解析前提后回填到
  `proposal.premise_propositions`，checker 不得信任调用方自报）；守卫由 checker
  判定并回报（`Accepted.direct_requirements`），内核据此建 Requirement、尝试
  清偿、并从前驱自动继承——不再逐类型手工 push。
- **`workflow.py`**：删除 `_verify` 的 isinstance 分派与八个 `_verify_*`、
  `_cross_diff`、`_collect`；`add` 组装 `StepProposal` 交 `commit`。状态由提交
  结果决定：`open`（Committed）/ `dead`（Refused）/ **`unverified`**（Undecided
  或 NeedsSplit）。**删除前驱 dead 的级联销毁**（v4 §6.10 反向修正：原结论保留，
  适用性由内核按作用域计算）。`Step` 去掉 `reads`/`clears`，新增 `judgment`
  （内核结论 id）。手工/交互通道用 `ALLOW_CONDITIONAL`（显式应用允许条件性结论），
  `REQUIRE_PROVED` 留给自动化简。
- **条件不再在化简中丢失**：`ClaimChecker` 回报表达式自身的定义域条件，
  故 `x/x` 断言即带 `x != 0`，后续重写经内核继承（v4 §9.1）。此前该条件在
  `norm` 后被丢掉。
- `repl.py` 的 `_normalize_eq` 改从 `checkers` 导入（旧实现已随验证器搬走）。

不变量 16（未验证候选不参与可信推导）**转绿**：checker 未决的候选状态是
`unverified` 而非 `open`，且不持有内核结论、不对账本产生任何写入。

验收：`tests/` 79 passed + 1 xfailed（不变量 14 红灯）；`stress/` 10 passed；
REPL 端到端冒烟（claim/diff/norm/solve/split/rules/apply/steps）正常。

依赖债延续并记录：`workflow/checkers.py` 仍依赖 `cas.math.*`（v3 遗留的
workflow→math 顶层依赖），v4 §三 的目标位置是各 `math/*/checkers.py`，阶段6 迁移。

### 阶段 3：命令只生成 proposal；checker 验实例而非搜索（2026-09-10）

按 v4 §十一 阶段3「先保留旧命令名称，但命令只负责生成 proposal」拆除
「命令类型 → 验证器」的功能特化分派。

- **删除 `_CHECKER_FOR` 类型分派表**。每个命令自带 `checker_id()`——它给出的是
  **主张的种类**，不是命令的类别。同一条重写命令按是否指定规则给出两种不同主张
  （标准形 / 规则实例），这正是「步骤无子类、分派走注册表」的落点。
  v4 §三 的 `Step` 无子类已满足；命令类保留为**参数记录**（前端命令的形状），
  内核不含它们，也不再被任何验证分派逻辑引用。
- **checker id 语义化**：`assumption.entry` / `both_sides.operate` /
  `equality.normalize` / `rule.instance` / `substitute` / `solve.back_substitute` /
  `branch.split` / `calculus.derivative` / `calculus.antiderivative`（+ 内核自带
  `kernel.decide`），不再是 `wf.*` 这种按命令命名的占位。
- **规则重写改为验证实例**（不变量 14 的修法）：`Rewrite` 携带
  `(rule, path, substitution)`——由**提出方**（REPL 的候选搜索）给出；checker
  只做四件事：规则查表、给定替换确为该位置的一个匹配、结果确为该模板的实例化、
  前驱其余部分原样保留。**不遍历路径、不导入 `apply_rule`**。
  原先 `_verify_rewrite` 遍历全部路径重跑规则搜索，那是「验证器重跑求解算法」。
- `RewriteChecker` 拆为 `NormalizeChecker`（rule=""）与 `RuleInstanceChecker`。

验收：`tests/` **81 passed（0 xfailed）**；`stress/` 10 passed；REPL `apply`
端到端正常（`exp(x)*exp(y) + apply exp_add → exp(x + y)` open，替换不符/路径
越界 → dead）。

一处**收紧**（有意为之，记录在案）：规则实例核验用指针恒等
（`replace_at(pred, path, inst) is content`）而非域判等——「内容就是这个实例的
结果」按句法身份判定。当前唯一提出方（REPL）正是这样生成内容的，故无行为变化；
若将来出现「手工写入等价但不同形的结果」的需求（v4 §9.2 derivation 模式），
再决定是否放宽为域判等。





### v3 残留清剿与接轨（2026-09-11）

按 AGENTS.md §六 债务零携带逐条复核 v3 遗留，并把 v4 已规定、此前无人接线的
机制接通。

**删除（v3 遗留 / 可被强实现替代）**

- `syntax/term.py` 的 `NORM` / `register_norm`：v2「驻留即规范化」的遗留扩展
  点，从未被 `mk` 读取；注释称 mk 内建 L0 环规范化也是假的（实测 `Plus(0,x)`、
  `Times(1,x)`、`Power(x,1)` 全部原样保留）
- `mk` 的互补对消解（`c ∨ ¬c → ⊤`）：那是对「是否恒真」的判定，属语义层；
  改由 `branch.coverage` checker 独立判定（v4 §2.1 禁止驻留期判定语义）。账本
  里记下的命题因此是**被验证的那个互补析取**，而非构造期坍缩出的 ⊤
- `realroot.isolate_squarefree`（被同文件 `real_roots_intervals` 取代）、
  `simplify.expand` / `_mul_expand`（生产路径不消费；stress_qarith 的 P4 改走
  `poly.from_term → to_term`）
- `workflow/constraint.py` 的重名死类 `ValuationCheck`（活的是 command.py 工厂）
- 与既有等价 API 重复的 7 个死导入；`tests/` 的 121 个非 ASCII 标识符全改英文
  （`cas/` 生产代码为 0）

**接轨（v4 已规定、此前无人调用）**

- 不变量 15 逃逸检查：`ScopeStore.escapes` + `commit` 第 1 步强制。旧的
  `escapes_to_parent` 契约是错的（符号在本作用域出现不构成逃逸，会误报）且
  从未被调用，已由正确实现取代
- §6.2 声明/定义：`Workflow.declare` / `define`，四项检查齐全——符号新鲜 /
  不形成非法递归（含互递归，新增 `_alias_cycle`）/ 右侧顺序可见且不引用外部
  作用域的局部符号 / 结论不得逃逸
- §8.8 分支合并：`Workflow.merge_branches` 五条检查 + `BranchMergeChecker`；
  `commit` 增 `inherited_reads`，合并步读集 = 各支读集之并 ——
  `ContextReadSet.merge` 因此有了消费者
- §四 依赖方向：`is_eq` 三份副本合成 `syntax/term.py:is_eq`；新建 `cas/api.py`
  作为前端访问计算设施的唯一出口；新增门禁
  `test_dependency_frontend_only_api_workflow_runtime`

**修掉的 bug**

- `TrackedContext.read_set` 与 `ContextReadSet.merge` 的去重键只用了 kind，
  同类的多次读取（两条假设、两次判定）被压成一条 → 读依赖丢失。改为按
  `(kind, key)` 整项去重，merge 变真并集
- `simplify()` 实测是恒等函数（`mk` 不做代数折叠），docstring 的「构造即规范化」
  是假的，据实改写（函数保留：它仍承担输入规模的预算把关）

**定义语义更正（参考实现取证）**

v4 §6.2「右侧在父作用域中良好绑定」一度被读成「不得引用本作用域局部符号」，
等于禁止同作用域链式定义。参考实现一致反对该读法：Maxima
`tests/rtest_allnummod.mac:1796`（同一 block 内 `expr` / `W_subst` 顺序使用）、
FriCAS `src/input/arrows.input:7-12`（`delta := p2-p1` → `len := … delta`）、
Reduce `vsl/alg.tst:32`（`a(0):=1$` 后 `a(i):=i*a(i-1)`）、yacas
`scripts/standard.ys:25`。各家的卫生纪律针对的是**逃逸**（Maxima 的 `block`
退出还原、Mathematica 的 `Module` 靠改名防捕获），不是同作用域引用。已更正为
「顺序可见 + 不得引用其他作用域的局部符号」。

**未决（需裁定，不要自行发明）**

- 分支合并的「每支确实回答了 P」这一环目前由工作流按**内核记录**核对——checker
  无法独立复算，因为不变量 8 禁止分支结论作为父作用域前提。要让内核独立复核，
  需 `commit` 支持「蕴含引入」规则（Γ,C ⊢ P ⟹ Γ ⊢ C⇒P）。这是内核新规则，
  动不变量 8 的边界，未落
- §四 表允许 `frontend → api/workflow/runtime`，但 parser/pprint 依赖 syntax 是
  既有事实，字面执行需把解析/打印移出 frontend。门禁目前只禁 frontend→math/kernel

验收：`tests/` **148 passed**、`stress/` 10 passed、REPL 端到端正常、pyflakes
除既有 unused-import 债务外干净。



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
