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

不变量 1 / 2 / 14 / 16 / 18 已绿，另有四条依赖与引用方向门禁、一条 C3 门禁
（math 层不得持有模块级装配状态），以及数学语义 head 字面量、求解器内嵌验证器、
声明 DSL 准入三条全库门禁；无 xfail 项。断言「某个名字/某个文件路径不会回来」的门禁
已按裁定全部删除（见末节）。
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

## 项层：预计算规范序 + 结构判等 + 表达式不驻留

这一轮把项层的两处根本性质换掉，换完性能提升约 8 倍，同时修掉两个正确性缺陷。

**动机。** profiling 查明 `differentiate` 的 64% 时间花在 `Term.__lt__` 上：`sort_key()` 每次
比较都从头递归重建整棵排序键树，而 `_h` 早已是 O(1) 整数。另外 `_EXPRS`/`_BOUNDS` 两张
`WeakValueDictionary` 在 AC 构造路径上先排序、后查表，命中比重建还慢——驻留表在买不到正确性，
只买到一点点共享。

**改动。**

- `Term` 的规范序键与结构 hash 都在**构造期**算好（`__slots__` = `("_h", "_key", "_sh")`），
  从子项已有的键组合，代价是 O(元数) 而非 O(子树)。`__lt__` 变成读两个已有对象；
  `sort_key()` 保留为字段读取的访问器（`pattern.py` 在用）。
- `__hash__` 返回结构 hash `_sh`；`__eq__` 改为结构比较（先做身份快路径）。哈希与判等因此
  一致，不再依赖驻留。
- **表达式节点不再驻留。** 只保留有限词表（符号、常数、声明的 special、de Bruijn 索引），
  规模由程序自身的声明决定。`_h` 降级为「本对象的唯一序列号」，供定点遍历使用；
  **凡以 `_h` 作键的重建映射仍按对象键入**，因为定点循环需要把「本轮重建出的对象」和
  「原对象」暂时分开存放。（本节初稿还写 `_h` 兼作 union-find 代表元的 tiebreaker；
  那是把分配序号当成了项的性质，已在下一节改为结构性代表元序。数值字面量的驻留表
  `_NUMS` 同样在本节被记漏，它已随下一节一并去掉——有限词表清单里本来就没有数值。）

**修掉的两个正确性缺陷。**

1. 弱表驱逐条目后，重建等值项得到**不同对象、不同 `_h`**，于是 `a == b` 对等值项为假，
   以 Term 为键的 dict 把一个表达式拆成两个槽位。有界淘汰会重新引入同一缺陷，因此
   AGENTS.md §四.6 改为区分「派生缓存必须有界」与「驻留表不是缓存」。
2. AC 路径先 `sorted()` 再查驻留表，驻留收益被排序成本吃掉。

**去掉驻留后暴露的 15 处身份依赖**（原本靠驻留「碰巧」成立）已逐一改为结构判等或
对象判别，两类不可混用：

- 判定层：`decide.equivalent` 的开头短路（这一处是根因：投影读不懂的项——`Piecewise`、
  引号子式——会掉成 `Unknown` 而不是判为自身）、`_facts_lookup` 三处（分支假设清偿不了
  守卫）、六处 `args[0] is t`。
- checker 层：分支合并的「各支未回答同一命题」、分支覆盖前提、规则实例结果、约束赋值、
  传递性中间项与结论、解方程的解变量/解值/声明条件。
- 定点循环：`simplify.rebuild` 的 `following is previous` 永不成立（**会死循环**），
  `termpath` 两处、`equality._representative_rewrite`、`definitions.expand` 同样如此。
  统一改为「子节点未变则返回原对象」，顺带保住「重建只分配真正改变的节点」这一性质。
- 其它：`workflow.branch` 互补检测、`linearform` 的 `x^1` 识别。

**性能（单次测量，同机器同输入）。** `differentiate` wide sum 16370 → 1940 us（8.4x），
medium deg20 8488 → 1110 us（7.6x）；`mk(Plus, 50)` 535 → 42 us。结构判等的代价经实测
可忽略：身份快路径吃掉绝大多数，元组比较走 C 层，2 元到 50 元基本持平（0.21 → 0.20 us）。

**验收（补跑于本轮项层改造之后的同一 HEAD）。** `python -m pytest -m "not random"` 为
342 passed / 12 deselected；`python -m pytest -m random` 为 12 passed（`random_qarith`、
`random_qi` 改过的 P2/P40 断言已确认通过）；`ruff check`、`mypy`（91 文件）与
`mypy --strict cas`（CI 用的是 strict）、`compileall` 全绿。`ruff format --check` 报 91 个
文件待格式化，HEAD~1 同样如此，是全库既有风格漂移而非本轮引入，故未在本轮处理。

**补测的未测路径与内存曲线**（本机单次最优值，20 次取最小，us；与上节自报值不同机器/负载，
不可直接比较，本机数值更低）：`differentiate` 40 项和 1205、20 次多项式 614、`mk(Plus,50)` 20；
Sturm `x^20-x` 隔离 811（实根恰为 0 与 1，隔离区间严格分离且升序）；CAD
`resolve_partition`（`x^2-2>0` ∧ `x<3`，7 个胞腔）2385，标签含全真胞腔；commit 路径经
REPL 门面 6 条命令（claim/norm/diff/solve/claim/integrate）3 ms，`norm` 报 committed、
`integrate x^2` 得 `x^3/3`。内存：项数 50→400 时峰值 105→268→583→1216 KiB，8 倍输入只涨
11.6 倍，未见二次增长；测量结束仍占 820 KiB（含 runtime、session 与脚本自持的项）。

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

项层改造遗留的三项待办（随机套件、内存曲线、CAD/Sturm/commit 路径）已在上节补跑完毕，
结论均为绿。补跑过程中查出一条与该项层改造直接相关的缺陷，已在本轮修掉，见下节。

## 数值字面量不驻留：去掉 `_NUMS` 与它掩盖的身份依赖

**缺陷。** `cas/syntax/term.py` 的 `_NUMS` 是按数值键的强引用 dict，键空间由计算量而非
程序声明决定：实测构造 20 万个互异有理数后 `_NUMS` 达 200002 项，运行期无任何淘汰
（`clear_interning` 只有测试门禁调用）。这与 `term.py` 自己的注释、AGENTS.md §四.6
「驻留表只限有限词表（符号、常数、声明的 special、de Bruijn 索引）」以及「本系统不再有
无界的项表」这条裁定都不符——数值字面量不在那份清单里。原有门禁只断言 `_NUMS` 是普通
dict、`_EXPRS`/`_BOUNDS` 不复活，不给它设上界，故表在无界增长时门禁仍绿。

**改动。** `N()` 直接新建字面量，`_NUMS` 删除（连同 `clear_interning`/`interning_size`
里的对应项），`term.py` 的表注释写明「按值的表键空间由计算决定」这段理由。等值字面量仍是
不同对象，但结构判等使它们在 set/dict 里折叠为一个槽位——这一条由
`test_term_hash_is_structural_and_stable` 覆盖，不需要另写「`_NUMS` 不得复活」的钉子。

**去掉驻留顺带暴露的 20 处身份依赖**（原本靠「同一个 `1` 只存在一个对象」成立）。判据仍是
上一轮定的两类：问形状的用 `==`，定点遍历里问「这轮有没有换新对象」的保留 `is`。全库按此
扫过一遍，剩下的 `is` 全部属于第二类（`new is old`、`following is previous`、
`__eq__` 的身份快路径），无需再动。

- `math/decide.py`：10 处 `is T.ZERO`（序规则表 7 处、精确差通道 2 处、投影零测 1 处）、
  `_same` 与序链 BFS 的同项判等、区间通道 3 处「本事实是否在给 `term` 定点」；两条证据
  detail 里的「pointer-identical」措辞随之改为「一个项不会严格大于或小于自身」。
- `syntax/match.py`：6 处模式与目标的比较（字面量模式、恒等元吸收、绑定一致性、head）。
  字面量模式原先靠驻留才匹配得上 `0`，规则索引与全扫描因此不一致。
- `math/piecewise.py`：相邻同值支合并与「两支同值」快路径。
- `math/base/equality.py`：`_Union` 改按结构 hash 建表（并查集的元素是结构等价的项，
  不是对象），代表元改由 `_representative_order` 选。
- `math/calculus/differentiation/checkers.py`：交叉验证的差为零判定、分段支条件同一性。
- `tests/integration/test_constraint_solver.py`：解值断言由 `is` 改为 `==`，所断不变。

**顺带修掉的潜在缺陷：闭包的代表元原来由分配序号决定。** `_Union` 的代表元 tiebreaker 是
`(子树的 postorder 长度, _h)`，而 `_h` 是**分配序号**，不是项的性质：同一段推导里 `1`
若恰好先于 `x` 被创建，`x` 就会被归约到 `1`，否则归约到 `x`，闭包输出因此依赖会话历史。
去掉数值驻留后事实里的 `1` 变成新对象、序号变大，代表元翻成 `x`，「`x == 2` 在 `x == 1`
下被证否」就从「带子证据（`1 == 2`）的 No」退化成「区间通道给的、cause 为空的 No」——
随机台架 `random_diff` P13 与 `test_refutation_closure` 立刻变红，正好把这条钉出来。
代表元改按结构取：闭项优先，其次子树较小，最后规范序。闭项优先有数学理由：闭包存在的
意义就是把残差方程交给精确/区间通道，框架把变量钉到数值时代表元取数值才判得动。

**验收。** `python -m pytest -m random` 12 passed（`random_diff` P13、
`random_piecewise_workflow` 两条新暴露的回归已转绿）；`ruff check cas tests`、
`mypy --strict cas`（91 文件）、`compileall` 全绿。性能代价（本机 20 次取最小，us）：
`differentiate` 40 项和 1205 → 1327、20 次多项式 614 → 658、`mk(Plus,50)` 20 不变、
Sturm `x^20-x` 811 → 794、CAD `resolve_partition` 2385 → 2409、commit 路径 3 ms 不变，
约 7–10% 的换取是每次 `N()` 都要分配。内存：项数 50→400 峰值 131→328→714→1500 KiB
（去驻留前 105→268→583→1216），仍是 8 倍输入 11.5 倍峰值；有限词表 26 个原子
（去驻留前 433，其中 400 余个是被驻留的数值）。

**不写「名字/路径不会回来」的门禁。**

裁定：「被删句柄不得回潮」「某变量不得复活」这一类断言只把删除这件事钉一遍：第二次回归
的价值为零，代价是一份要永远跟着重命名同步的名字清单。设计意图写在 AGENTS.md 与源码
注释里，由 review 保证，不由测试保证。门禁只保留可机械判定、且不依赖具体标识符的那类：
结构性质、依赖方向、声明准入、缓存有界。AGENTS.md 末节同步记了这条。

本轮删除：`test_interning_is_limited_to_the_finite_vocabulary`（断言 `_NUMS`/`_EXPRS`/
`_BOUNDS` 不存在；等值项折叠为一个槽位已由 `test_term_hash_is_structural_and_stable`
覆盖）、`test_c3_removed_declaration_handles_stay_removed` 及其 `_REMOVED_ASSEMBLY_HANDLES`
名字表（按文件路径 grep 已删标识符）、`test_phase5_old_mutable_context_removed`
（`hasattr` 断言 `Context`/`Entry`/`Branch` 不存在）、本轮那根
`tests/regression/test_numeric_literals_are_not_interned.py`。

保留（不是这一类）：依赖方向与引用方向门禁、`test_term_hash_is_structural_and_stable`、
math 层无模块级装配状态、math 模块级缓存登记且有界、模式层缓存有界淘汰、数学语义 head
字面量、求解器不内嵌验证器、声明 DSL 准入、不变量 3/4/5/6/11/13/14/16/18/21。

## 语言与引用纪律

源码（`.py` / `.dsl`）一律英文，且不得引用设计文档：理由以直述方式写清，不把读者
指向某份文档去追。两条都是 `tests/contract/test_v4_invariants.py` 里的机械门禁
（`test_source_is_english_only`、`test_source_cites_no_design_document`），覆盖
`cas/`、`tests/` 下全部源文件。**文档不受此约束**：设计文档与本文档
保持中文。
