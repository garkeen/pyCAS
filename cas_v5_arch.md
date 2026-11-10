# pyCAS v5

> 目标：正确、高效、灵活、可解释的通用纯符号 CAS。
>

---

## 目录

- §0 文档地位、规范用语与设计边界
- §1 最终架构裁定
- §2 术语与基本数学语义
- §3 目标目录与依赖方向
- §4 纯语法、身份、绑定与结构操作
- §5 类型、声明、定义与语义整理
- §6 不可变上下文与名字环境
- §7 有效代数结构与 parent 协议
- §8 参数族、局部化、特化与分支
- §9 微分域、常数域与扩张塔
- §10 定义域、区域与分段函数
- §11 判定、搜索、失败与证据协议
- §12 命题、规格与可信判断
- §13 可信内核、校验器与原子提交
- §14 条件传播、清偿与适用性
- §15 作用域导出、量化与分支合并
- §16 数学操作与插件协议
- §17 工作簿、对象、任务与四种图
- §18 工作流状态机、调度与历史
- §19 手动交互、选择路径与操作语义
- §20 自动算法、SAINT 策略与解释
- §21 完整交互案例
- §22 多项式、线性代数与 Gröbner 基
- §23 实代数、CAD 与量词消去
- §24 积分、Risch 与定积分
- §25 ODE、PDE 与相邻能力
- §26 Python 类型、不可变性与扩展边界
- §27 性能、预算、缓存与并发
- §28 持久化、重放与外部接口
- §29 命名、职责与工程纪律
- §30 完整能力路线、依赖图与迁移边界
- §31 不变量与验收矩阵
- §32 最终接口闭合表、类型载荷与全程数据流

---

## §0 文档地位、规范用语与设计边界

### 0.1 文档职责

本文设计 pyCAS 的数学对象、有效表示、算法接口、计算管线、验证模型、工作簿和工程终态。设计从数学契约与数据流推导模块，而不是由现有目录或历史实现决定。

- `roadmap.md`：从当前实现走向完整目标的施工路线、算法选择、阶段依赖与交付条件；不记录当前进度或缺陷。
- `AGENTS.md`：项目定位、目标、代码风格、语义要求、实现纪律，以及当前进度与缺陷。
- `progress.log`：只追加的已完成施工、验收与经验教训记录；不记录计划、未实现项或下一批工作。
- `reference.md`：数学依据和参考源码证据。
- `risch.md`、`cad.md`：保留细粒度工具与研究线索，实施时核对对应算法的具体前提。

§30 表达数学能力之间的依赖，roadmap 表达施工次序；两者层次不同。需求对应的设计和验收入口见 roadmap §1。

本文中的目标路径表示未来职责，不声称这些文件当前已经存在。除明确标为“示意语法”的交互片段外，本文中的类型名与协议名具有统一含义。

### 0.2 规范用语

- **必须**：健全性或互操作性要求，不得用模式开关绕过。
- **禁止**：会破坏语义边界的行为。
- **默认**：用户或请求可以显式选择其他已定义策略，选择必须进入请求快照。
- **可选优化**：不改变数学承诺，不改变输入解释，不扩大已声明的覆盖范围。
- **片段**：有明确输入结构、系数范围、结果语言与终止/完备性契约的一类问题。
- **完整**：在所声明片段与前提下履行完整契约，不是“解决任意数学问题”。

本文给出模块级算法职责、输入输出与证书要求，不把数百个具体算法的全部伪代码复制进架构文件。算法实现必须另有可核对的数学依据，但不能以“算法细节”为由留下对象语义与接口空白。

### 0.3 产品目标

pyCAS 是校验型、可交互的通用 CAS：

1. 精确计算可判定片段内的问题。
2. 在未覆盖、条件不足、资源耗尽时明确停下。
3. 用户可以编辑表达式、建立问题、提出方程、变换、换元、分部积分和选择策略。
4. 自动与手动产生同类数学任务和操作记录。
5. 用户能够检查结论、条件、来源与推导层次。
6. 数学机器可以单独调用，不要求先建立工作簿或证明历史。

非目标：

- 不把任意逻辑证明搜索作为默认产品能力。
- 不保证任意超越常数判零、任意微分方程或任意整数方程可判定。
- 不用近似相等、采样相等或搜索失败冒充数学结论。
- 不通过隐藏条件让界面看起来“什么都能算”。

### 0.4 运行时威胁模型

可信边界防止错误候选、错误证书数据、失效上下文和普通编程误用进入可信结果。

它不承诺防御已经获得宿主进程任意 Python 执行权的恶意插件。未受信任的外部程序通过数据协议或隔离进程提交候选；不能让其直接修改内核对象、安装可信 checker 或访问 store 写接口。

### 0.5 完整设计与分期实施

目标是一个完整的纯符号 CAS：有效系数结构和正交参数扩张、各结构的规范化/判等、代数与微分扩张、Gröbner 和方程组、CAD/QE、Risch 与 RDE/PRDE、分段及定积分、可判定微分方程子类，以及完整手动/自动工作簿和可恢复工程运行时。

每个数学承诺相对于输入语言、结构能力和结果类定义。算法的数学可行性、当前实现覆盖和本次资源预算分别记录；这样既能规划全部可行能力，也能精确解释某次调用的结果。

已有代码和文档都是待检验的设计材料。优化时保留有效的数学结构，重设不合适的接口和数据流；依据是整体一致性、可实现性与复杂度，而不是一律推翻或一律维持原状。§30 描述最终能力图，roadmap 给出可执行的建设顺序，§32 展开跨层的数据通道。

---

## §1 系统结构与计算模型

### 1.1 编译式数学管线

pyCAS 将表达式整理为适合算法的有效代数表示，在该表示中完成计算，再将结果及其数学关系带回用户层。

```text
文本/对象 + 语义 frame + 用户意图
       ↓ 解析、绑定、定型、定义展开
固定 ProblemSpec + AlgebraRequest
       ↓ 结构选择与具有数学含义的转换
AlgebraView[E] = parent + value + 映射/定义域信息
       ↓ 域内算法；局部数组、稀疏表、矩阵和扩张塔
候选值 + 数学规格 + 证书/算法分解
       ↓ 独立核验与条件处理
可信规格 + 原问题的覆盖报告
       ↓ 一次用户级发布
对象/候选/历史 + 可读结果
```

工作簿组织这条管线，而不是在每次系数运算时介入。代数库可以独立调用；手动、脚本和自动策略在请求边界汇合。

### 1.2 三个计算平面

| 平面 | 数据与职责 | 成本位置 |
|---|---|---|
| 数学计算 | 已绑定 parent 的元素、矩阵、理想、塔、胞腔；执行精确算法 | 位复杂度、项数、次数、分支与胞腔数 |
| 数学核验 | 问题、候选、区域、证书；重建被证明的关系 | 独立残差、恒等、秩/根计数/覆盖等检查 |
| 交互编排 | 对象版本、任务、动作、假设、策略、历史 | 快照、引用解析、发布与显示 |

核验和计算共用可信基础算术，不共用被核验的候选搜索。内核负责规格、支持和作用域的结合；数学 checker 负责该规格对应的数学算法。

### 1.3 关键数据选择

1. **表达式与值分离。** Term 保留语言结构，域元素采用自己的有效表示；两者通过显式映射联系。
2. **对象与关系分离。** g 是中性数学对象，HasDerivative(U,f,x,g) 是关系。对 g 再计算不自动扩大它与 f 的既有关系。
3. **固有定义域与核验区域分离。** 显式函数对象固定其定义域；一种表示可只在局部有效；某项关系还可能只在更小区域已证。
4. **角色按请求固定。** 结构工厂和语义库在装配后冻结，系数、参数、目标及导子按本次问题选择。
5. **结果按数学承诺分类。** 一个解、完整解集、泛参数公式和全参数分类各有对应规格。
6. **不可变边界、可变工作区。** 对外数学值和快照不可变，算法内部可以批量积累并一次正规化。
7. **完成性是查询。** 它由原问题、已验证规格、适用性与覆盖派生，不由算法写一个 success 字段。

### 1.4 设计取舍与实施方法

Python 静态类型用于约束结构和载荷，运行时 parent/作用域检查用于动态身份，数学算法及证书用于正确性；三者互补。
采用模块化可信计算基础，而非将所有计算翻译为基础逻辑证明。这样能直接实现标准 CAS 算法，同时在可复核的数学边界交付结论。

性能首先由表示和算法决定：多项式批量收集、分式自由/模方法、系数控制和结果复用优先于历史记账优化。对核验成本单独测量，选择合适证书，不预设它一定便宜。

完整对象和工作流语义在本文定义，实施按 roadmap 的数学消费者逐步接通。接口改造以整个数据通道的契约为单位，避免只加字段而没有生产者/消费者，也避免因当前功能少而把接口永久固定为求导专用。

---

## §2 术语与基本数学语义

### 2.1 核心术语

| 名称 | 唯一含义 |
|---|---|
| `Term` | 不带类型、上下文、定义域或证据的不可变语法树 |
| `SymbolId` | 自由符号的稳定身份，不是显示名称 |
| `TypedExpr` | 在指定意义环境中完成类型与绑定检查的表达式视图 |
| `FunctionValue` | 参数绑定、固有定义域、值域及一个或多个带有效区域的函数表示 |
| `Proposition` | 完成命题类型检查、具有明确绑定和意义环境的公式 |
| `SemanticFrame` | 不可变声明、定义、假设及其词法环境 |
| `Parent` | 一个明确的有效代数结构及其表示协议 |
| `AlgebraValue` | parent 与其成员表示的对外组合 |
| `AlgebraRequest` | 本次计算的域、变量角色、解释和参数模式 |
| `ProblemSpec` | 输入、目标变量、区域、结果语言及覆盖要求 |
| `Artifact` | 工作流中持有的中性数学数据，不蕴含真假 |
| `Candidate` | Artifact 相对于一个 ProblemSpec 的待验证答案 |
| `Judgment` | 可信内核发行的带作用域和开放条件的命题 |
| `Obligation` | 一个结论成立尚需满足的条件 |
| `InferenceRecord` | 一次可信推理的输入证明、结论和证书关联 |
| `Task` | 寻找满足 ProblemSpec 的结果的工作单元 |
| `ConstructionRelation` | 候选结果之间的构造约束，不是假设或定理 |
| `WorkspaceRevision` | 一次不可变的用户工作区状态快照 |
| `OperationEvent` | 用户或策略执行一次动作的历史记录 |

v5 不使用一个 `Step` 同时表示推理边、用户动作、任务进展与屏幕行。

### 2.2 六种相等不能混用

| 关系 | 问题 | 可采用的方法 |
|---|---|---|
| 结构相等 | 两棵 Term 的结构是否相同？ | 结构比较，哈希仅加速 |
| 域内相等 | 两个已知成员是否为同一域元素？ | parent 的精确判等 |
| 当前取值相等 | Γ 是否保证 t=s？ | 假设下的判定 |
| 区域上的函数相等 | 在 U 内两者都定义且值相同吗？ | 带区域的恒等验证 |
| 偏函数相等 | 定义域相同且其上值相同吗？ | 定义域等价与值相等 |
| 问题等价 | 两个问题的解集合是否经指定映射对应？ | 解集双向包含或问题变换证书 |

`a` 不是 `Q[a]` 的零多项式，不等于 Γ 能推出每个实际取值都满足 `a≠0`。

`x/x` 与 `1` 是 `Q(x)` 中相同元素，不等于两者作为原始实偏函数具有相同定义域。

### 2.3 开放公式的判定含义

对合法命题 P：

```text
Yes      表示 Γ ⊨ P
No       表示 Γ ⊨ ¬P
Unknown  表示当前程序尚未证明上述任一方向
```

`No` 不是“没有证明 P”，也不是“P 不被所有可能的上下文蕴含”。

因此，无假设查询自由实变量命题 `x=0`，不能因为多项式 x 非零而回答 No。

`IdentityIn(Q[x], x, 0)` 是另一个明确的命题，可被域算法否定。

对 `ForAll(x∈U, P)` 的否定，可以由 U 中经验证的反例给出；这仍不同于证明 U 上处处 `¬P`。

### 2.4 定义性先于真假

表达式可以是偏函数。类型错误、绑定错误和未定义的输入不自动解释成数学假命题。

- `IllTyped`、`UnboundSymbol`、不合法的索引或字段属于请求错误。
- 已证明除数为零，属于定义性失败。
- 尚不知道除数是否非零，属于条件阻塞。
- 经确认合法的命题才进入 Yes/No/Unknown。

### 2.5 正确性不等于完备性

验证一个候选答案只说明该候选满足指定关系。

- 一个根，不等于全部根。
- 一个原函数，不等于已经描述全部原函数。
- 一个 ODE 解，不等于基本解系。
- 一组胞腔，不等于覆盖完整空间。
- 一个泛参数答案，不等于全部参数取值的分类。

覆盖、唯一性、存在性、成员正确性必须使用分别有定义的命题。

### 2.6 名称对照与旧名退出

同一概念在本文只用一个名字。下列对照固定下来，文档与实现都照此命名，旧名在迁移完成后退出（§30.6）。

| 概念 | 本文名称 | 不得再用 |
|---|---|---|
| 代数结构的完整描述 | `ParentSpec` | 用裸 `Parent` 指描述 |
| 按描述建立、接受成员并执行运算的结构 | `Parent`（实例） | —— |
| 描述的稳定身份 | `ParentId` | 用对象地址、名称或单个 hash 当身份 |
| 逐符号的声明 | `SymbolDeclaration` | —— |
| 数学语义声明库（函数、常数、导数定律、定义域条件） | `SemanticLawCatalog` | 与 `SymbolDeclaration` 共用“声明”一词 |
| 完成类型、绑定与意义环境检查的表达式视图 | `TypedExpr` | 与工作簿对象混称 |
| 工作簿中的表达式对象 | 持有不可变 `TypedExpr` 版本的 `Expression` 对象 | —— |
| 结论成立尚需履行的义务 | `Obligation`（Judgment 的 `obligations` 字段；口语称“条件”） | v4 的 `Requirement` |
| 已发行结论的引用 | `JudgmentRef` | —— |
| 校验会话内未发行的证明回执 | `LocalReceipt` | 当作 `JudgmentRef` 使用或持久化 |
| 装配期准入的可信数学依据 | `BasisRef` | —— |
| 带作用域的显式用户公理 | `AxiomRef` | 当作 `BasisRef` |
| 条件处置策略 | `ConditionPolicy` | v4 的 `GuardPolicy` |

---

## §3 目标目录与依赖方向

### 3.1 目标目录

```text
cas/
  foundation/
    ids.py                 # 稳定标识与隔离的 ID 类型
    immutable.py           # 不可变容器约定
    budget.py              # 共享计算预算与取消
    errors.py              # 程序错误与请求错误分类
  syntax/
    term.py                # 纯语法与结构相等
    binding.py             # de Bruijn 的 shift/open/close/substitute
    traversal.py           # 明确顺序的遍历与路径
    pattern.py             # 与 Term 分离的模式
    matching.py            # 结构匹配，不猜数学等价
    surface.py             # 保留书写顺序的表面 AST
    parser.py
    printer.py
  language/
    sorts.py               # 数学类型、形状与函数签名
    signatures.py          # 稳定语言签名
    declarations.py        # 声明、规则和定律的数据契约
    propositions.py        # 命题封装与结构逻辑接口
    problems.py            # ProblemSpec 与结果语言
    decisions.py           # Verdict 和证据引用协议
  algebra/
    protocols.py           # Ring/Field/Euclidean 等有效结构协议
    parents.py             # parent 描述、身份与工厂
    morphisms.py            # 嵌入、同态、表示转换
    integers.py
    rationals.py
    finite_fields.py
    polynomial/
    fractions/
    algebraic/
    linear/
    factor/
    groebner/
    real_algebra/
    differential/
    series/
    ore/
  semantics/
    frames.py              # 不可变上下文数据与名字解析
    elaborate.py           # 语法到有意义对象
    definitions.py         # 词法定义与无环展开
    dependencies.py        # 变量依赖与参数角色
    definedness.py         # 消费声明与规则的定义性分析
    regions.py             # 区域描述，不实现 CAD 搜索
    algebra_bridge.py      # Term 与 parent 元素之间的有条件转换
    specialization.py      # 参数特化的语义检查
    services.py            # 注入的判定与数学能力协议
  kernel/
    model.py               # Judgment/Obligation/InferenceRecord
    context_rules.py       # 假设、弱化、作用域引入与导出
    evidence.py            # 证书封装与 checker 协议
    checkers.py            # 核心结构 checker 注册
    commit.py              # 唯一可信发行边界
    applicability.py       # 条件解析与适用性
    store.py               # 追加式可信数据
    transaction.py         # 校验后的原子发布
  operations/
    protocols.py           # 开放 OperationSpec 与提案协议
    registry.py            # 类型绑定和装配
    plans.py               # 数学子任务、结果槽和候选组合
    traces.py              # 数学解释配方，不是证明历史
  math/
    core/                   # 基础代数命题、关系和校验器
    logic/                  # 公式处理、逻辑服务及其证书
    elementary/             # 函数/常数/导数/分支的 DSL 声明
    rewriting/              # 数学改写、同余与改写证书
    equations/              # 问题变换、解集与求解接口
    inequalities/           # CAD/QE 组织层与解公式
    calculus/
      differentiation/
      integration/
      limits/
      series/
    differential_equations/
    discrete/               # 求和、差分、递推的独立能力
    strategies/             # SAINT 风格建议与启发式
  workflow/
    objects.py              # Artifact 与 ObjectVersion
    tasks.py                # Task 与 Candidate
    relations.py            # ConstructionRelation
    branches.py             # 用户研究分支与参数情形
    selections.py           # 对象版本绑定的选择
    events.py               # OperationEvent
    revisions.py            # WorkspaceRevision 与 undo/redo
    scheduler.py            # 子任务和候选组合调度
    application.py          # 操作编排与事务协调
    views.py                # 用户可理解的状态投影
  runtime/
    builder.py              # 显式装配
    bootstrap.py
    services.py             # 将协议接到具体实现
    storage.py              # 内存及持久化事务适配
    serialization.py        # 版本化数据编解码
  frontend/
    session.py
    repl.py
    commands.py
    rendering.py
  api.py
```

目录是职责边界，不要求每个小算法都拆成新文件。子包内可按实际复杂度合并实现，不得为了符合目录图创建空壳层。

### 3.2 静态依赖

| 层 | 允许依赖 | 禁止依赖 |
|---|---|---|
| foundation | Python 标准设施 | 全部上层 |
| syntax | foundation | 域、上下文、工作流 |
| language | foundation、syntax | 具体求解器、工作流 |
| algebra | foundation | Term、SemanticFrame、Judgment、工作流 |
| semantics | foundation、syntax、language、algebra、注入服务协议 | 具体 math 求解器、kernel store、workflow |
| kernel | foundation、syntax、language、semantics 的数据与协议 | 具体搜索器、workflow、frontend |
| operations | 基础类型、语义对象、kernel 证书接口 | workflow store、frontend |
| math | algebra、semantics、language、operations、kernel checker 接口 | kernel 写接口、workflow、frontend |
| workflow | kernel 公共入口、semantics、operations 协议 | 具体数学搜索实现和代数内部表示 |
| runtime | 各模块的装配入口 | 无反向依赖它的底层模块 |
| frontend | API/工作流门面与格式化协议 | 私有 store、私有代数算法 |

`semantics` 需要数学判定时调用注入的接口，不导入 `math/decide.py` 一类全知模块。`workflow` 需要积分时调用操作注册表，不导入积分器。

### 3.3 证明数据和对象引用方向

- Term 不引用任何上下文、Artifact、Task 或 Judgment。
- 代数元素不引用工作流。
- Judgment 可以引用语义环境和可信证明，不引用 ArtifactId 或 TaskId。
- 工作流对象可以引用 JudgmentId 表示验证状态。
- 证书可以包含输入数学数据的快照，但其真实性由 checker 验证，不能因为带有 ArtifactId 就被信任。
- OperationEvent 可以引用输入输出对象、任务和已发行证明，用于解释和重放。

### 3.4 数学语义归属

函数名称、导数定律、分支、特殊常数、积分规则属于 `math` 的声明与算法模块。

语言的绑定、布尔结构、函数应用和类型构造属于 `syntax/language`。

环、域、多项式及其精确算法属于 `algebra`。这是一项对 v4 “所有数学必须放在 math/*”目录纪律的明确调整，不改变其数学语义不可散落到内核与前端的原则。

---

## §4 纯语法、身份、绑定与结构操作

### 4.1 Term 变体

核心语法采用不可变的封闭结构变体：

- 精确整数与有理数文字；
- 布尔文字；
- `SymbolRef(SymbolId)`；
- `BoundVar(index)`；
- `Apply(operator, arguments)`；
- `Binder(signature, arity, body, syntax_annotations)`；
- 引用语法值 `Quote(term)`。

`Apply.operator` 可以是已解析的函数符号或合法的函数表达式，不局限于字符串 head。未知函数作为 operator 出现时同样参与自由符号、依赖和逃逸检查。

Binder 的显示名不是语义字段；参数个数、作用域位置和绑定方式必须由语言签名确定。多变量绑定明确规定索引顺序。

`syntax_annotations` 若包含类型标注，其内容仍是类型的语法表达式，不是已推导的 ValueSort 或上下文对象；计算后的参数类型放在语义视图中。签名的低层身份使用基础 ID，不让 syntax 反向导入 language。显示 hint 保存在表面语法映射中，不参与结构相等。

### 4.2 构造器不做数学化简

Term 构造器只保证结构合法和文字表示规范：例如有理数分母非零、符号约到分子、分子分母约分。

禁止在纯语法构造期执行：

- `x/x→1`；
- `0*f→0`；
- 含未知定义性表达式的消去；
- 对所有 `Times` 无条件交换排序；
- 函数求值、域推断和声明规则。

尤其不能在知道运算类型之前，把矩阵乘法和标量乘法按同一 AC 规则处理。

v5 的纯语法保留操作数顺序。经类型确认的交换环表达式可在数学正规化层获得 AC 表示；域内多项式有自己的规范表示。这不要求用户书写顺序与内部多项式单项式序相同。

### 4.3 三种身份

- `NodeId`：可选的进程内对象序号，仅用于诊断、局部 DAG 遍历与对象引用。
- 结构 hash：用于 dict/set 加速，允许碰撞，必须配合结构相等。
- 结构值：相等的真正依据，包括自由 SymbolId 与绑定结构。

禁止 `dict[hash(term), value]` 充当以项为键的映射。必须使用 Term 作为键，或在哈希桶内完整比较。

结构序键必须稳定且不依赖对象分配顺序。输出规范序与持久化哈希不得使用 Python 的进程随机化 hash。

### 4.4 不可变性与共享

Term 的参与相等、哈希和排序的字段在创建后不可修改。

可以采用弱引用或有容量上限的结构共享；任何缓存被清空后，重建同结构 Term 仍须相等且 hash 相同。

用户符号、自动生成局部符号和任意大 de Bruijn 索引不是“天然有限词表”。除固定语言签名外，不设置永久强引用的全局驻留表。

### 4.5 绑定原语

`syntax/binding.py` 提供且只提供精确定义的结构操作：

| 操作 | 约定 |
|---|---|
| `shift(term, cutoff, delta)` | 只移动指定 cutoff 外的 de Bruijn 索引，禁止产生负索引 |
| `open_binder(binder, fresh_symbols)` | 用真正新鲜的 SymbolId 打开，绝不用显示 hint 当身份 |
| `close_binder(body, symbols)` | 按身份抽象指定符号，保留其他自由符号 |
| `instantiate_binder(binder, arguments)` | 捕获规避实例化，正确提升替换项并调整外层索引 |
| `substitute_free(term, mapping)` | 同时代换自由符号，不把新插入的符号递归再代换 |
| `well_scoped(term, binder_depth)` | 检查不存在游离或越界绑定索引 |

“同时代换”与“逐项顺序代换”必须是不同 API；默认只做同时代换。

多参数 binder 的绑定位置由签名声明：签名按参数出现顺序列出哪些位置是绑定位置，同一 binder 内的多个绑定位置按该顺序依次对应索引 0…k-1；跨 binder 时索引按嵌套深度向外递增（与 `Bound`/`BoundVar` 的既有约定一致）。非绑定位置（积分的上下限、求和的端点等）与外层同深度，因此不能引用被绑定变量，也不额外加深任何索引。注解属于外层环境，不增加绑定深度；其中参与语义的符号仍须计入可见性/依赖检查，纯显示 hint 才不参与数学自由符号。

涉及 binder 的子项视图携带 binder depth 和局部参数类型。路径取出后得到的不是一个可以无条件放回任意环境的裸子项。

### 4.6 自由符号与依赖

`free_symbols` 遍历 operator 与 arguments，按绑定签名处理 binder。Quote 的内容作为语法数据，不向外贡献数学自由符号；引用操作需要的环境另行显式携带。

语法自由符号不等于微分依赖：`a` 出现在表达式中，但可以相对 D_x 为常数；`y(x)` 的微分依赖由函数应用与声明确定。

### 4.7 路径与遍历

- `preorder`、`postorder` 按真实输出顺序命名。
- DAG 去重遍历与树出现位置遍历分开。
- 路径使用显式步骤：operator、argument(i)、binder_body、binder_annotation 等。
- 修改 operator 不伪装成修改普通参数。
- 数学改写必须检查从根到替换位置的全部祖先语义；检查最近一层不够。
- Quote 下的结构编辑不产出数学同余证明。

---

## §5 类型、声明、定义与语义整理

### 5.1 三层输入

```text
文本
  → Surface AST：保留名称、位置、用户顺序
  → 解析后的 Term：名称解析为 SymbolId，绑定结构明确
  → TypedExpr / Proposition：具有意义环境、类型与定义性描述
```

解析成功不等于表达式可进行任何数学运算。

### 5.2 数学类型与计算 parent 分离

基础 ValueSort 包括：

- Integer、Rational、Real、Complex；
- 有限域元素等显式带 parent 的值类型；
- 向量、矩阵、张量及其形状；
- 函数类型，含参数与结果类型；
- 集合、区域、命题和语法数据；
- 尚未确定足够信息的形式标量类型。

`Real` 是数学值的范围，不是任意实数的有效表示域。一个 Real 表达式可能被表示在 Q、实代数数域、形式参数多项式或某个微分扩张中。

类型提升必须由明确嵌入支持。矩阵维数、函数元数等不变量在语义整理边界检查。

### 5.3 SymbolDeclaration

一个声明至少固定：

```text
symbol_id
surface_name
value_sort / function_signature
lexical_owner
dependency_contract
origin
```

参数、未知量、消元变量、微分变量是请求角色，不永久写入 SymbolDeclaration。

`dependency_contract` 描述独立性或函数参数关系，不允许通过“不是当前变量”无条件推出导数为零。

### 5.4 未声明符号的默认策略

普通交互允许先输入未声明名字，但在执行数学任务之前必须产生明确声明。

默认工作簿使用可见的“实标量数学”配置：新的普通标量名字解析为实标量；新的函数名不自动获得任意导数或连续性，而必须有签名或得到受限的形式函数声明。

用户可以显式选择形式代数、复分析或其他配置。配置固定在语义快照中，不追溯改变旧对象。

Python 低层 API 不使用隐藏的会话默认。缺少必要的声明或 AlgebraRequest 时返回 NeedsInformation 或 InvalidRequest。

对于 D_x 请求，其他显式独立标量可以被确定为相对 x 的参数；依赖未知的函数符号不能擅自当作常数。界面展示本次采用的变量与参数角色。

### 5.5 定义

定义是带词法捕获的不可变绑定：

```text
DefinitionBinding(symbol_id, typed_body, defining_frame, dependencies)
```

- 右侧无环；普通别名不得递归。
- 右侧名字在定义时解析，不在使用时按当前同名对象重新解析。
- 自动展开仅沿定义方向。
- 定义保持对原独立变量的依赖。
- 改写一个已有显示名的定义会创建新绑定身份和新 frame；旧对象仍指向旧定义。
- 递归函数需要单独的定义机制及良定义性，不通过别名循环偷渡。

### 5.6 方程与假设

`u=x²` 默认是公式数据，不是定义。

用户必须通过动作选择它的用途：建立待解问题、加入假设、提出待验证命题或作为坐标映射的定义关系。

加入假设是扩展 frame 的动作。若 P 含偏函数，假设包必须明确包含将 P 解释为真所需的定义性前提；这些也是假设，不能标成已证明。界面显示完整假设包。若某个定义性前提在当前 frame 中已闭合证明为假，则拒绝该假设、不创建 frame；若这组假设导致当前 frame 出现闭合的矛盾证明，则 frame 状态置 `Inconsistent`（§6.6），普通计算停止并报告，而不是让任意命题继续显示为已解决。两者的分界是“单个前提被否证”还是“整个 frame 已判定不一致”。

### 5.7 声明 DSL

数学声明以数据文件描述：

- 函数签名、作用域与 binder 位置；
- 定义域与值域；
- 复分支或实解释；
- 导数与其他数学定律；
- 每条定律的条件与可信依据；
- 同余、连续性、可微性等可供算法消费的性质；
- 打印别名与角色。

导数定律允许有条件。例如平方根导数必须声明比函数自身定义域更严格的可微区域。禁止用“导数模板必须无条件”迫使实现忽略边界。

DSL 是数据格式，不是证明机制。用户加载一条 `rule ...` 不自动把它提升为全局真理：只有已验证定理、受信任标准库依据，或显式带作用域的用户公理可以支持可信应用。三者分别对应 §12.4 的引用：已验证定理走 `JudgmentRef`，标准库依据走装配期准入的 `BasisRef`，用户公理走引入它的 frame 中的 `AxiomRef`。用户公理可以支持该 frame 下的肯定或否定结论，两者都保留其作用域和来源；它不能作为全局无条件依据或准入到标准库 TCB。

---

## §6 不可变上下文与名字环境

### 6.1 三种环境

| 环境 | 内容 | 生命周期 |
|---|---|---|
| `MeaningWorld` | 语言签名、数学声明、可信规则与解释约定 | 装配后冻结 |
| `SemanticFrame` | 声明绑定、定义、假设、父 frame | 不可变版本 |
| `AlgebraRequest` | 本次 parent、变量角色、导子、参数模式 | 单次请求快照 |

不存在一个可变的“全局数学上下文”同时承担三者。

### 6.2 SemanticFrame 字段

```text
frame_id
world_id
parent_frame_id
new_declarations
new_definitions
new_hypotheses
name_bindings_delta
compiled_environment_key
```

Hypothesis 有独立身份、命题、定义性前提和来源。frame 中的名字映射不改变符号本身。

### 6.3 作用域包含

只有祖先 frame 的语义可以通过弱化进入后代。兄弟分支之间不存在自动可见性。

历史 revision 引用确切 FrameId，不通过“此分支最新 head”重新解释旧历史。

新增声明与假设产生后代；撤回假设或改变意义需要回到旧 frame 后创建新分支，不就地修改旧 frame。

### 6.4 自由符号可见性

每个非语言内建 SymbolId 必须有可见声明。禁止“从未被声明过的名字反而不受逃逸检查”。

局部符号不能因为外层存在同名字符串就被认为可见。绑定索引与自由符号分别检查。

### 6.5 更改世界

修改函数语义、默认复分支、可信定律或类型解释会产生新 MeaningWorld。

旧世界中的结论不可静默移入新世界。允许复用的仅是经明确意义兼容检查的结构与数学对象；否则重新整理输入并重新验证。

算法优化版本可以不改变数学意义，但证书解码和重放必须记录相关 checker/codec 版本。当前 `World`/`Frame`/`Declaration`/`Definition`/`Hypothesis` 已提供基于规范序列化的 SHA-256 内容摘要；`Revision.frame_digest`/`Event.frame_digest` 记录该摘要，摘要不使用进程内 WorldId/FrameId。

### 6.6 上下文一致性

frame 状态为：

- `Unassessed`：尚未证实一致或不一致；
- `ConsistentForFragment`：在明确片段内有一致性证据；
- `Inconsistent`：有闭合的矛盾证明。

“没有发现矛盾”不等于已证明一致。

当前实现只提供 `Unassessed` 与 `Inconsistent`；在能够验证片段证据的 checker 建立
之前，不提供 `ConsistentForFragment` 的记录入口，避免把任意证据当成一致性证明。

普通自动计算遇到 Inconsistent frame 停止并报告矛盾，不把任意命题绿色显示为已解决。逻辑内核可用矛盾证明关闭一个不可能的分类分支，且必须明确保留该分支为空的意义。

### 6.7 编译与缓存

父链是语义版本结构，不要求每次查询线性遍历。可以按 FrameId 缓存解析后的名字、定义 DAG、假设索引和自由符号摘要。

缓存有界，可清空；正确性由不可变 frame 和明确 key 保证，不依赖缓存存在。

---

## §7 有效代数结构与 parent 协议

### 7.1 有效结构的准入

一个 parent 对其接受的成员必须提供明确且终止的基础运算。结构不同，必需运算不同；不把所有环强行升级成域。

最小环接口包括零、一、加、负、乘、精确相等、成员表示规范化和特征信息。这里的“成员表示规范化”指把元素化为该 parent 的合法表示（可作键、可比较、不含冒充分量），不承诺唯一范式；是否另有一个唯一规范形由 §7.4 决定。

扩展能力分成独立协议：

- 整环；
- 域与非零除法；
- Euclidean 算法及其度量；
- gcd；
- 因式分解；
- 有效顺序与符号判定；
- 指定导子；
- 有理数、整数或其他基结构的明确嵌入。

不存在“默认返回零”的导子，也不存在“未实现判零就返回 False”的接口。

### 7.2 ParentSpec 与身份

parent 的完整描述至少包含其基结构、生成元身份、关系、所需的结构证明和表示选择。

例如：

```text
PolynomialParent(base=Q, generators=(A,X), monomial_order=...)
FractionParent(base=PolynomialParent(...))
AlgebraicFieldParent(base=K, irreducible_polynomial=p, root_embedding=...)
```

ParentId 是这个完整描述的稳定身份，不是任意域名称，也不是对象地址。缓存按完整描述比较，不能只按摘要值比较。

两个表示不同但同构的 parent 不自动混用。需要表示转换或指定同构。

### 7.3 成员与表示

对外使用 `AlgebraValue(parent, representation)`；高频内部循环可以在已绑定 parent 的算法对象中直接传表示。

多项式元素的生成元顺序、系数 parent、单项式序由所属 parent 固定。禁止为同一裸 Poly 任意传一个不匹配的 ring 来计算。

系数类型可通过 Python 泛型约束；成员有效性在创建边界检查，而不是每次乘加重复检查。

### 7.4 判等

`equal(a,b) -> bool` 和 `is_zero(a) -> bool` 只接受已知成员。在这个边界内不返回 Unknown。

从一般表达式转换失败属于桥接层问题，不能制造一个“可能有未知判等的域”。

唯一规范形不是所有 parent 的硬要求。若使用非约分分式，交叉相乘仍可提供精确判等；但名称不得声称已经获得约分规范形。

### 7.5 多项式结构

必须区分：

- `K[x₁,...,xₙ]` 的多元多项式；
- 把一个变量作为主元、其余变量属于系数环的递归多项式；
- 系数在域上和系数在非域环上的除法；
- 精确除法、带余除法和伪除法；
- 普通偏导与微分结构下的总导数。

多元 leading coefficient 相对于主变量通常是系数环元素，不是任选一个单项式的数值系数。

### 7.6 商结构与代数数

`K[t]/(p)` 只有在相应条件得到保证时才可作为域。不得把“构造了商”直接解释成“p 不可约”。

- 不可约性由可信算法或可复核证书建立。
- 约化商环可能有零因子。
- 参数关系形成非素理想时，保留商环结构或分解为情形。
- 实代数嵌入需要定义多项式及根选择，不只需要抽象代数商。

### 7.7 嵌入与转换

明确区分：

| 映射 | 性质 |
|---|---|
| `Embedding` | 单射结构保持映射 |
| `Homomorphism` | 保持相应运算，但不保证单射 |
| `RepresentationIsomorphism` | 同一结构的可逆表示转换 |
| `Specialization` | 参数取值映射，通常只在某局部化上定义 |

混域运算必须找到请求指定或唯一可证明的共同目标与映射。多个合法但不等价的选择出现时返回 NeedsInformation，不按注册顺序偷偷选择。

### 7.8 语义桥

`AlgebraView` 至少包含：

```text
source_typed_expression
parent
value
symbol_to_generator_map
interpretation
validity_conditions
conversion_witness
```

其中 interpretation 明确是形式域元素、参数族、某个具体嵌入下的值，还是区域上的函数表示。当前实现的 `ConversionWitness` 固定 `kind`、`injective`、`preserves_equality`、`preserves_nonzero`、`preserves_definedness`；`typed_view` 消费这些标志，而不是只看 `ConversionKind`。表示同构与嵌入要求四个标志全部为真；一般同态可以失败。带有显式 `source_domain`/`valid_on` 的视图必须使用保留定义性的 witness，否则 `typed_view` 以 `conversion_witness` 拒绝；全定义视图没有区域声明，非保定义同态仍可在单射且保等号时传递等式。`source_domain`/`valid_on` 在发行时校验类型与子区域关系。

实现切片（2026-11-09，定义性保留 witness）：`ConversionWitness` 增加 `preserves_definedness`；表示同构/嵌入要求该标志为真，`representation_isomorphism()` 固定为真。`AlgebraView.__post_init__`、`_issue_view` 与 `_admit_view_relation` 在视图携带 `source_domain`/`valid_on` 时要求 witness 保留定义性，`typed_view` 以 `ViewRefused(missing={"conversion_witness"})` 拒绝不保留定义性的区域视图；全定义视图不发明定义性声明，非保定义同态仍按单射/保等号规则传递等式。多项式桥、参数多项式桥与有理桥继续发行 `preserves_definedness=True` 的表示同构。嵌入/同态的具体实现、混域消解与 `AlgebraRequest` 的嵌入字段仍未建。

实现切片（2026-11-09，解释与 witness 一致性）：`semantics.bridge` 新增 `_interpretation_witness_refusal`，由 `AlgebraView.__post_init__` 与 `_issue_view` 共同消费。`EMBEDDED` 只允许 `EMBEDDING`/`REPRESENTATION_ISOMORPHISM` witness，`HOMOMORPHISM` 与“值是嵌入像”矛盾；`PARAMETER_FAMILY` 只允许 `REPRESENTATION_ISOMORPHISM`，`EMBEDDING`/`HOMOMORPHISM` 不足以声称形式参数族表示；`FORMAL` 保留三种 kind，仍由 witness 的 `injective`/`preserves_equality`/`preserves_nonzero`/`preserves_definedness` 标志决定可传递事实。`_issue_view` 在建造前以 `ViewRefused(Reason.FRAGMENT, missing={"interpretation_witness"})` 拒绝，直接构造边界抛 `ValueError`。该规则与区域/定义性保留规则独立叠加；具体嵌入/同态桥、混域消解与 `AlgebraRequest` 嵌入字段仍未建。

转换必须保留原表达式的定义域信息。约去因子不会消除 source 的孔洞。

代数幂与表达式幂要通过解释桥区分：环内 a^0=1 是幺半群定义（含 a=0），而当前实/复偏函数解释的 Power(0,0) 未定义。将 Power(f,0) 投影为环元素 1 时，必须保留 f 定义且非零的条件或在该桥片段拒绝；不能据此发行无条件的函数导数/等价规格。当前多项式桥采用保守片段：只有底数是全局非零常数时才投影，形式参数不算全局非零；其他情形诚实拒答。空代数乘积为 1，语法层是否允许空参数由签名决定。

转换回 Term 必须使用原符号映射或显式引入的新生成元绑定，不自行发明全局同名字母。

### 7.9 AlgebraRequest

请求包含：

- 系数 parent 或可解析的 parent 描述；
- 多项式、消元、积分和求解变量角色；
- 允许的嵌入；
- 参数解释模式；
- 形式值或函数值解释；
- 必要时的导子与实嵌入；
- 目标表示要求与共享预算。

planner 可根据已声明类型与操作需求构造请求，但必须把结果固定并可查看。禁止通过遍历叶节点猜测整个任务的数学域。

实现切片（2026-11-09）：`AlgebraRequest.differential` 已作为请求局部导子载荷落地；缺省 `None` 表示该请求不假设任何导子（不以零导子兜底），存在时必须是 `DifferentialStructure`，并由请求唯一固定本次计算使用的导子。`DifferentiationView`/`SpecializationView` 只接受与请求同一对象的 `DifferentialStructure`。嵌入、参数关系、实嵌入与 `VariableRoles` 绑定位置与 binder-aware 角色仍未建；目标/参数排序已由后续切片闭合（world 已固定），不能把本切片写成完整 §7.9 请求载荷。

实现切片（2026-11-09，世界作用域角色）：`VariableRoles` 增加 `world: WorldId | None`，`ProblemSpec` 与 `AlgebraRequest` 都拒绝未绑定 world 的角色集；`SimplePolynomialBridge`/`ParameterPolynomialBridge`/`RationalFunctionBridge` 在 `to_view` 中先于角色/generator 检查，以 `ViewRefused(Reason.FRAGMENT, missing={"request_world"})` 拒绝 `roles.world` 与源 `TypedExpr.meaning.world` 不一致的请求。`SymbolId` 仍是 world 内的局部身份，不建立跨 world 的全局符号表；嵌入、参数关系、实嵌入与绑定位置及 binder-aware 角色仍未建；目标/参数排序已由后续切片闭合。

实现切片（2026-11-10，请求角色排序与解释要求）：`VariableRoles` 增加 `target_sort: Sort | None` 与 `parameter_sorts: tuple[Sort, ...]`，按 target/parameters 是否存在校验；`AlgebraRequest` 要求目标排序和与参数数量匹配的参数排序。`AlgebraRequest.interpretation_requirement` 是 `Interpretation` 到语言层 `InterpretationRequirement` 的唯一映射，`ProblemBuilt`/`ExecutionRequest` 要求它与固定问题的 `ProblemSpec.interpretation_requirement` 一致。`ProblemSpec` 还要求输入 `BindingView` 中与角色同名的符号排序一致。嵌入、参数关系、实嵌入、完整绑定位置与 binder-aware 角色、近似精确性仍未建（目标/参数排序已闭合）；本切片不声称完整 §7.9 请求载荷。

实现切片（2026-11-10，系数范围与值域）：`AlgebraRequest` 增加必需的 `coefficient_domain: ValueDomain`，由装配显式声明而不是从 parent 类型嗅探（当前 Q 基座全部声明 `RATIONAL`，Z 测试声明 `INTEGER`）；`value_domain` 由 `roles.target_sort` 经语言层 `value_domain_of_sort` 单一映射派生（`INTEGER`/`RATIONAL`/`REAL`/`COMPLEX`，其他排序精确 `ValueError`）。`ProblemSpec.domain_requirement` 的 coefficient/value 两半与 `ProblemBuilt`/`ExecutionRequest` 绑定同一请求，`problem_mismatch` 消费固定请求的 coefficient/value domain。嵌入、参数关系、实嵌入、完整绑定位置与 binder-aware 角色、一般值域代数仍未建（目标/参数排序与 coefficient/value domain 已闭合）；本切片不声称完整 §7.9。

---

## §8 参数族、局部化、特化与分支

### 8.0 基系数、参数空间与函数域正交

参数不是与 Q、有限域、数域并列的特殊数域，而是请求角色。对每个已建立的有效交换环 K 都可构造 K[A]，其有限多项式判等归约到 K；K 为整环时可构造相应分式域，K 为域时得到通常的 K(A)。基环有零因子时不能无依据赋予分式域能力。

例如 K0=Q(α)、α²=2 且指定 α>0，可以建立参数坐标环 A=K0[a,b]、泛参数域 C=Frac(A)、函数域 F=C(x)，并指定 D(x)=1、D(C)=0。数域常数 α、参数 a/b、函数变量 x 属于不同角色；角色由当前请求固定，不由名字或全局符号属性决定。

形式参数结构、参数实际取值空间与本次算法的系数 parent 分开记录。K(A) 中形式非零不等于每个特化非零；D_x 下常数也不等于 D_a 下常数。交换目标与参数需要新的请求和明确映射，而不是修改旧 parent。

正交不等于所有扩张自动交换，也不等于所有能力自动继承：关系理想可能产生零因子，特化可能降低次数/秩，实嵌入需保持选根。参数化环算术、泛点算法、完整参数分类及数值特化是四个独立但共用同一结构/映射系统的层次。完整实现依赖见 §30.10。

### 8.1 一次声明，按任务选择表示

参数符号的身份和取值约束属于 frame；是否作为系数生成元、求解未知量或消元变量属于任务。

同一个 a 可以同时参与不同任务：

```text
对 x 积分：a 是相对 D_x 的常数参数
对 a 求解：a 是目标未知量
对 (a,x) 消元：两者都是多项式生成元
CAD：a 可以是需要保留的自由变量
```

不创建一个不断扩大的全局域。扩张结构不可变，相同描述可共享。

### 8.2 三种参数模式

| 模式 | 承诺 |
|---|---|
| `SpecifiedValues` | 参数已有精确取值或明确有效表示 |
| `GenericParameters` | 在明确的非退化条件下研究形式参数族 |
| `AllParameterValues` | 对声明允许的全部参数值给出覆盖或明确未覆盖部分 |

普通带参数求解任务默认 AllParameterValues。若当前算法只能给泛参数答案，返回显式的 Generic/Partial 结果，不自动把请求改成 GenericParameters。

### 8.3 泛参数计算的解释

`a∈Q` 时可以用形式 `Q(A)` 研究参数族；这不声称实际值 a 是超越数。

但 `A≠0` 作为形式域事实，只能用于该泛点计算，不能直接转成对全部有理参数值成立的命题。

每次泛参数除法、选主元、使用固定次数或选不可约分支，必须有足以说明特化有效性的条件或见证。

### 8.4 局部化与异常集

只收集最终答案的分母不够。中间主元、首项系数、判别式和算法分支也可能影响结论。

`GenericResult` 必须携带：

```text
result
valid_on
excluded_cases
correctness_specification
coverage_claim
```

条件可以保守，但若声称完整分类，就必须处理被排除的所有情形，并证明覆盖。

其中 `valid_on` 是 §10.3 的 `Region`，`excluded_cases` 是若干个 `Region`（是否两两不交可另证，但不作要求）；两者都是已整理的命题公式，不是字符串或自由文本。

允许使用分式自由算法减少人为引入的异常条件；不允许通过忘记中间除法使结果看起来无条件。

实现切片（2026-11-09）：`GenericResult.valid_on`/`excluded_cases` 已使用 §10.3 的 `RegionSpec`，不再保存裸 `Proposition`。`cas.semantics.regions.region_from_proposition` 是现有 Proposition 载荷进入区域的唯一桥：坐标取 `coordinate_symbols(proposition.term)` 的排序结果，因此同一命题总得到确定坐标。`GenericResult` 的构造/覆盖准入、`specialize` 的真值检查以及 `OutsideValidity`/`NeedsRecomputation` 都读取 `RegionSpec.condition`；workspace 在由 `MathematicalProposal` 构造泛结果时经该桥包装，`MathematicalProposal` 的公开字段在本切片仍为 `Proposition`。该切片不建立第二套区域语法，也不声称一般区域代数或完整 S1 闭合。

### 8.5 特化协议

特化输入为：原 AlgebraView/ProblemSpec、参数映射、新 frame 和目标 parent。

处理顺序：

1. 检查映射类型、绑定和所需关系。
2. 检查原局部化所要求的分母或其他前提。
3. 检查所使用的次数、秩或扩张结构是否保留。
4. 在有效时构造映射后的结果及对应证书。
5. 失效时回到原问题，在新参数情形下重算；不得直接代入一个已失效的泛参数公式。

`a→0` 不可能作为整个 `Q(a)` 到 Q 的域同态。API 不提供这种虚假的总操作。

### 8.6 参数关系

参数空间可以有多项式等式、不等式和整数约束。

- 多项式等式可用于商环、理想或三角表示。
- 不等式由有序解释与实代数服务处理。
- 整数约束不是有序实闭域约束的同义词。
- 非素参数关系需要分支或带零因子的结构。
- 未知的超越关系不能被默默当作代数独立。

### 8.7 参数线性方程的标准结果

对实参数 a、b 和实未知量 x，`a*x+b=0` 的完整结果是：

```text
a≠0                 → {-b/a}
a=0 且 b=0          → R
a=0 且 b≠0          → ∅
```

对整数未知量还需检查整数成员或整除条件。

结果中“某分支唯一”“结果有自由参数”“分支覆盖全部参数空间”是三个独立属性，不用一个 complete 布尔值替代。

---

## §9 微分域、常数域与扩张塔

### 9.1 DifferentialStructure

微分结构是一个已有 parent 上的附加结构：

```text
DifferentialStructure(parent, derivation, constant_structure, witnesses)
```

导子满足加法与 Leibniz 法则。没有导子能力时拒绝微分域算法，不使用零导子兜底。`witnesses` 包含系数导子、生成元导数及延拓依据：自由多项式环上的延拓由构造定理保证，商结构还须证明 D(I)⊆I，分式延拓使用商法则及非零分母条件。仅在几个生成元上做采样不能证明任意算法实现满足导子法则。

`constant_structure` 必须区分“已知嵌入常数子域”和“已证明为完整常数域”，并声明算法实际需要的判等、分解、线性相关等能力。不用“没有出现 x”替代一般常数域认定，也不把待解决的常数问题藏在 bool oracle 中。

实现切片（2026-11-09）：当前 `DifferentialStructure(parent, derivation)` 仍以私有 seal 限制构造，`polynomial_structure`/`rational_structure` 是唯一入口；它已作为 `AlgebraRequest.differential` 的请求局部载荷，由 `DifferentiationView`/`SpecializationView` 按对象同一性消费。`witnesses`、完整常数域、导子塔、商结构 `D(I)⊆I` 证明与持久化/重放载荷仍未建，不能用本切片宣称一般微分域能力。

### 9.2 系数扩张与函数扩张

典型塔为：

```text
C0 = Q(α)
C  = C0(a,b)
F0 = C(x), D(x)=1, D(a)=D(b)=0
F1 = F0(t1)
F2 = F1(t2)
```

系数扩张与函数扩张共用代数 parent 和嵌入机制，差异由导子及当前任务决定。

对 x 为常数的 α、a、b，在另一个导子下不一定为常数。

### 9.3 扩张类型

| 扩张 | 代数描述 | 导子数据 |
|---|---|---|
| 有理自变量 | K(x) | 指定 D(x)，通常为 1 |
| 代数扩张 | p(t)=0 | 从关系与可分性求 D(t) |
| primitive 扩张 | t 超越于 K | D(t)=u∈K |
| exponential 扩张 | t 超越于 K | D(t)/t=u∈K |
| 其他已支持扩张 | 明确的结构契约 | 明确 D(t) 及所需算法 |

代数扩张中，特征零可分情形满足：

```text
D(t) = -D_coeff(p)(t) / p'(t)
```

分母可逆性来自结构前提，不是对任意商环都成立。

### 9.4 生成元不是任意独立的新字母

引入生成元之前必须确定算法需要的代数独立性、关系和常数扩张条件。

例如：

- exp(2x) 与 exp(x) 不应被无条件当作独立生成元；
- 新 primitive 的导数已是基域内某元素的导数时，可能产生新常数；
- log(x²) 的分析解释不能仅由形式导数相同确定为 2log(x)。

塔构造输出 admitted extension 或明确阻塞，不输出“先假设独立”的可信塔。

### 9.5 表达式与塔的转换

转换记录：生成元的原表达式、依赖层级、导数、基域嵌入、代数关系和解释区域。

塔内回代验证分为：

1. 域内表示的正确性；
2. 导子解释的正确性；
3. 实/复函数分支和定义域的正确性。

三个层次不能通过一次结构比较合并。

### 9.6 多导子与未知函数

普通 ODE 请求使用一个指定导子。PDE 请求可以使用多个导子，但必须声明其作用与是否交换。

未知函数 y(x) 可形成形式导数节点；声明其函数签名不等于已证明可微。需要可微性时产生明确假设或义务。

把 y(x) 当作微分不定元的微分多项式算法，与把 y 解释成某个实际函数的解验证是不同桥接层次。

### 9.7 有效常数域边界

Risch 等算法只能接收真正提供了所需精确算法的常数域。

不接受一个会在内部返回 Unknown 的“布尔判零 oracle”冒充完整能力。

对于无法建立的超越常数关系：可以保留未验证形式对象或在显式形式独立假设下研究，但不能把形式结论无条件解释成原始初等函数结论。

---

## §10 定义域、区域与分段函数

### 10.1 定义性与函数表示

`Definedness` 描述已整理表达式的定义条件。显式 `FunctionValue` 固定参数绑定、固有定义域和值域；它可以有多个表达式/代数表示，每个表示记录自己的有效区域。

五种区域信息分别保存：

| 信息 | 含义 | 消费者 |
|---|---|---|
| 固有定义域 | 函数在哪些点有值，是函数对象身份的一部分 | 求值、偏函数相等、延拓 |
| 表示有效区域 | 当前表达式/代数元素在哪些点表示这个函数 | 转换、局部计算 |
| 关系核验区域 | 已证明 f、g 之间某关系成立的区域 | 关系应用、推导组合 |
| 正则性区域 | 连续、可微、可积等性质成立的范围 | 微积分 checker |
| 原问题目标区域 | 用户请求要覆盖的范围 | 完成性/残余问题 |

一个中性表达式 g 可以在 U 外有意义，同时只在 U 上被证明是 f 的导数。把 g 当独立表达式求导是新问题；要得到 f 的二阶导数关系，需要组合两条关系并核验共同区域。这个区分比给所有表达式附一个混合语义的 region 字段更准确。

固有定义域与表示有效区域彼此独立。源表达式可以在整个片段上有定义（`source_domain=None`），而选定的代数表示只在某个真子区域上等于它（`valid_on` 非 None）；这时记录为 `SUFFICIENT`，桥的 `ConversionWitness` 就是该充分区域的证据，不伪造 `SubregionCertificate`。只有源本身带有非平凡固有域、且表示只在它的真子区域上有效时，才需要并携带 `SubregionCertificate`。`TOTAL` 仍是两个区域都为 None，`EXACT` 仍是固有域存在且表示区域为空或与固有域相同。

精确域描述与充分子域证据分别标识。SamePartialFunction 使用完整域等价；充分子域只支持 EqualOn。

区域坐标空间可以大于源的绑定视图：`Definedness` 要求每个区域的坐标包含源的全部自由符号，但允许额外坐标，并保留区域自己的坐标顺序。两个区域若同时存在，必须在同一意义环境（同一 world 与 frame）中读取；每个区域所在 world 必须等于源所在 world。区域可以在源 world 的后代 frame 中读取，但不同 frame 的两个区域不能配对成同一视图的固有域与表示区域。

实现切片（2026-11-09，区域绑定视图）：`AlgebraView` 增加 sealed `region_bindings: tuple[FreeSymbol, ...]`，默认取 source binding view；它必须覆盖源自由符号与每个现存区域的自由变量，否则 `_issue_view` 以 `ViewRefused(Reason.FRAGMENT, missing={"region_bindings"})` 拒绝、直接构造抛 `ValueError`。`AlgebraView.definedness` 用该绑定视图的坐标与排序构造 `RegionSpec`，因此后代 frame 引入的额外坐标不再被压回源绑定视图；严格子区域需要 `SubregionCertificate` 而绑定排序非稠密时抛精确 `ValueError`，不静默降级。`Definedness` 已 sealed，只由 `_issue_definedness`/`AlgebraView.definedness` 发行。`VariableRoles.world`、`ProblemSpec.function_inputs` 与函数相等 checker 的 problem binding 已由后续批次实现；`ProblemSpec` 的精确域/解释、`VariableRoles` 目标/参数排序与 `externalizable` 正向路径也已由后续批次闭合；完整绑定位置与 binder-aware 角色、跨 frame 前提弱化、结果语言与嵌入字段仍未建，本切片不声称完整 S1，也不把非稠密/离散区域纳入现有证书片段。

### 10.2 函数与偏函数相等

定义两种独立规格：

```text
EqualOn(U, f, g)
SamePartialFunction(f, g)
```

前者要求 U 内两者定义且相等；后者还要求完整定义域相同。

化简 `x/x→1` 默认输出带原区域 x≠0 的表达式对象，不把结果升级为全域常数函数。用户显式选择延拓时是另一个操作与命题。

### 10.3 区域

区域可以是区间、半代数集、离散集合、复域描述或一般条件公式。

`RegionSpec` 描述区域；`RegionCertificate` 证明非空、覆盖、包含、连通或其他特定性质。

`Region` 本身复用 §12.1 的 `Proposition`：一个已整理、绑定合法、意义环境明确的条件公式。区间、半代数集、离散集合、复域描述都是这个命题公式的解析形式，不引入第二套区域语法。`RegionSpec` 是它的描述，`RegionCertificate` 是它的证明。因此 §12.2 的 `Covers(region, pieces)` 的参数就是命题公式，`GenericResult.valid_on`/`excluded_cases`（§8.4）也是同一类型。

实现切片（2026-11-09）：`cas.semantics.regions` 已建立 `RegionSpec`（有序坐标 + `Proposition` 条件）、封闭 `RegionCertificate`（`NonemptyCertificate`/`SubregionCertificate`/`CoversCertificate`）与 `certify_*`/`verify_region_certificate`。证书只在受限条件片段（ground truth、单原子线性区间、受限蕴含）能证明时发行，验证独立重检而非信任 `method`；一般半代数区域、连通性、内部/边界/相对拓扑和无限覆盖仍未建。`RegionSpec` 的坐标只需包含条件的自由变量，允许比源绑定视图更大的坐标空间；`Definedness` 要求区域坐标包含源的全部自由符号而不要求元组相等。视图发行时还要求每个区域与源同 world，两个区域同时存在时共享同一 `MeaningKey`；`valid_on` 可以在 `source_domain` 为 None（源全定义）时单独存在。

实现切片（2026-11-09，函数表示覆盖）：`cas.math.functions.equality` 用 `RegionSpec`/`CoversCertificate` 把函数固有域与每个表示有效区域统一为区域，并提供确定坐标的 `function_region`、`function_coverage_regions`、`function_coverage_certificate` 与结构匹配的 `coverage_matches_value`。`extend_function` 要求新函数值的表示覆盖其声明固有域，`FunctionEqualityChecker` 独立重检该覆盖并核对证书精确匹配新值。该检查只在受限条件片段成立；一般半代数区域、无限覆盖、表示重叠一致性与最大固有域仍未建。

实现切片（2026-11-09，泛结果区域）：`region_from_proposition` 把现有 Proposition 载荷转换为 `RegionSpec`，坐标固定为 `coordinate_symbols(proposition.term)` 的排序元组；`GenericResult.valid_on`/`excluded_cases` 已消费该类型，`MathematicalProposal` 仍以 Proposition 为公开字段并在 workspace 构造泛结果时转换。该桥只统一现有区域描述，不新增区域语法，也不宣称一般半代数区域运算。

实现切片（2026-11-09，函数区域消费侧修正）：`FunctionValue`/`FunctionRepresentation` 本批只接受总条件（`definedness` 为空），因为 workspace 的定义域检查、函数相等 checker、覆盖 helper 与 `same_partial_function` 仍按条件 term/命题读取；部分条件在构造时以 `ValueError` 拒绝，`FunctionExtensionOperation.propose` 对部分新域/新表示区域返回结构化 `ProposalUnsupported`。`FunctionEqualityChecker._check_equal_on` 先独立发行 claim region，再用 `proved_subregion` 证明它是各固有域与表示区域的全定义子区域；`_check_same` 拒绝带开放前提的完整域参与者；workspace 的 `define_function`/`extend_function` 与 extension operation 使用同一前提感知规则。`proved_subregion` 的 `same_meaning=False` 只供已独立校验同 world/可见 frame 的 checker 比较祖先 frame 区域。`FunctionValue` 的 `RegionSpec` 迁移、声明函数定义域与一般偏函数定义域仍未建。

实现切片（2026-11-09，区域绑定排序与稠密证书边界）：`RegionSpec` 增加按 `SymbolId` 规范化的 `sorts`，非空时必须恰好覆盖全部坐标；`sort_of` 查询单坐标绑定，`is_dense` 只在全部坐标为 `RATIONAL`/`REAL` 时为真（空坐标集 vacuously dense）。`certify_nonempty`/`certify_subregion`/`certify_covers` 在任一参与区域非稠密时返回 `None`，`verify_region_certificate` 对非稠密区域上的证书返回 `False`；`condition_satisfiable`/`is_empty_condition` 的稠密序假设因此只在 `is_dense` 为真时被消费。`function_region` 只为函数参数坐标写入 `FunctionParameter.sort`，条件含非参数自由变量时整体省略 `sorts`，使覆盖证书被诚实拒绝。该切片仍不声称一般半代数区域、离散集合运算或无限覆盖代数。

实现切片（2026-11-10，区域绑定排序一致性）：`AlgebraView.region_bindings` 现在要求与源自由符号同 `SymbolId` 的条目排序等于源 `BindingView` 的排序；`semantics.bridge._region_binding_refusal` 在 `_issue_view` 与 sealed `AlgebraView.__post_init__` 两处拒绝不一致绑定，`_issue_view` 返回 `missing={"region_bindings"}`，直接构造抛 `ValueError`。该规则防止显式绑定把非稠密源坐标（如 `INTEGER`）伪装成 `REAL`，从而让 `definedness` 发行稠密 `SubregionCertificate`；后代 frame 的额外坐标仍由桥声明排序，本切片不为它们推断排序，也不声称一般半代数区域代数。

区间端点可以是精确有理数、实代数数或尚未比较的符号值。比较未决时不能自行排序。

区域的内部、边界、连通分支和相对拓扑必须明确；不能把低维集合上的恒等验证当作全维开集上的多项式恒等验证。

### 10.4 逻辑与偏函数

数学公式的逻辑规则作用于已良定义命题。比较中的偏函数先产生定义性要求。

需要由条件保护后续求值时，统一使用一个节点 `Guarded(condition, body)`：只在 `condition` 成立的区域求值 `body`。它是唯一的目标形式；`If` 与前端短路 `&&` 都解析成它，不产生第二套语义。普通 `And`/`Or` 保持严格求值（两个操作数都必须良定义），因此前端短路标志不得解析成可重排的普通逻辑 `And`。

例如 `x≠0` 保护 `1/x>0` 的定义性，应在整理后的公式中保留保护关系；不能在 AC 排序后丢失。

普通 And/Or 的代数逻辑化简只在其命题操作数已具备相应定义性证明时进行。

作用域导出的 `H→P` 使用守卫蕴含：H 必须在父语境良定义，P 的定义性只在 H 成立的子语境中要求。未闭合的后件定义性导出为 `H→Defined(P)`，不在 H 为假的点提前求值 P。它在双方均良定义时与普通经典蕴含一致，但不得未经定义性检查就改写为严格求值的 `¬H Or P`。

实现切片（2026-11-09，结构定义性前提）：`Proposition` 已记录非正指数整数幂的 `Ne(base,0)` 前提，并对和/积/比较/`And`/`Or`/`Not`/`Implies`/`Guarded`/`Piecewise` 的操作数做结构递归；`Guarded`/`Piecewise` 的分支局部求值语义、声明函数定义域、binder-aware premises 与一般偏函数定义域仍未实现，不能把结构递归当作完整偏函数语义。

实现切片（2026-11-09，条件求值消费侧）：`specialize` 的 `_truth` 先递归求值 `Proposition.definedness` 前提；假前提使条件在该点未定义（有效性区域视为点在外，排除情形视为不适用），未决前提返回 `None` 并转为 `NeedsRecomputation`，只有全部前提为真才求主条件。函数相等/延拓与 workspace 函数区域检查改用 `proved_subregion`，不再直接比较 `Proposition.term`；`ProblemSpec.region`、`OperationRequest.region`、`FunctionValue`/`FunctionRepresentation` 区域与 `MathematicalProposal` 区域等裸 Proposition 载荷在构造器拒绝非空 `definedness`，避免 term 级消费者静默忽略前提。`Guarded`/`Piecewise` 分支局部语义、binder-aware premises 与一般偏函数定义域仍未建。

### 10.5 分段的值语义

Piecewise 使用有序首中语义。第 i 支的实际支集是：

```text
condition_i 且前面各支均未命中
```

不是裸 condition_i。

条件本身的定义性也需要检查。没有命中的点默认为未定义，除非显式 else 分支覆盖。

首中语义保证选择唯一，不等于各个裸条件互斥。互斥化是可验证的变换，不是构造时无依据的假设。

### 10.6 分段运算

逐点加乘可以构造交叉支集，再利用已证明的区域事实简化。组合过程受预算控制。

微分必须分别处理：

- 各支集内部的导数；
- 边界点的连续性与差商；
- 定义域端点的单侧或双侧导数约定。

不能只返回一个全域导数表达式并在日志里说“断点未验证”。未验证区域必须存在于结果的规格与覆盖状态中。

边界正则性未决时的合法结果只有两种：把声明区域收缩到一个已证正则的子区域并把该区域写进规格；或返回 `Unknown(GUARDED)`。不允许返回全域结果再附一条说明性警告。

### 10.7 原函数与分段连接

分支上 D(F)=f，只证明局部关系。

若请求区域是连通区间且 F 在连接点跳跃，不得验证为该区间上的原函数。若请求区域明确排除了连接点，则允许按不同连通分支分别给出原函数。

全部原函数的积分常数应按连通分支组织；不默认所有分支共享一个 C。

### 10.8 积分变换

换元关系至少记录映射、源/目标区域、导数或 Jacobian、端点/边界处理与所用定理。

正向链式构造不一律要求映射可逆；需要反解、参数化解集双向对应或特定积分变换定理时，才要求相应单射、覆盖、多重度或单调分支条件。

---

## §11 判定、搜索、失败与证据协议

### 11.1 Verdict

对有效命题使用封闭联合：

```text
Yes(proof_receipt)
No(refutation_receipt)
Unknown(blockers)
```

Verdict 禁止隐式转换成 bool。调用方必须显式处理变体。

Receipt 引用受验证的数学依据；字符串 detail 是解释，不是证明。

公开 `decide` 可以返回绑定语义快照的受检回执而不写账本。回执不是已发行的 JudgmentRef；其来源、支持与闭合性由验证设施保证，持久化前提必须经过 §13 的发行边界。必要条件尚未在查询 frame 中闭合时，只能返回 Unknown(GUARDED)，不能把条件证明包装成 Yes 或 No。当前实现为 `VerdictYes(LocalReceipt)`/`VerdictNo(RefutationReceipt)`/`VerdictUnknown(blockers)`；`decide` 只调用 `validate_commit`，不调用 `publish_commit`。

### 11.2 Blocker

Unknown 的原因保留四个主类，但增加结构化内容：

| 主类 | 含义 |
|---|---|
| FRAGMENT | 没有覆盖当前输入的已实现片段 |
| GUARDED | 必要前提尚未建立 |
| UNDECIDABLE | 所请求的一般问题类有明确不可判定性边界 |
| BUDGET | 本次资源预算耗尽 |

Blocker 包含目标命题或子问题、所需能力、未决条件、已尝试的片段、预算信息及可采取的下一动作。

UNDECIDABLE 不表示某个具体实例永远无法解决；没有算法或查不到实现通常属于 FRAGMENT。

### 11.3 搜索结果不是 Verdict

搜索接口使用：

```text
Produced(candidate_bundle)
Unsupported(fragment_report)
NeedsInformation(requests)
BudgetExhausted(partial_candidates)
Cancelled(partial_candidates)
InvalidRequest(issues)
```

候选集合为空不是 NoSolutions。部分候选可以保留，但覆盖状态必须未完成。

### 11.4 校验结果

checker 返回：

```text
Verified(checked_specifications, obligations, semantic_supports)
Refuted(checked_negated_specification, witness)
Unverified(blockers)
InvalidEvidence(issues)
```

InvalidEvidence 表示证书结构或引用不合法，不等于已经证明数学规格为假。

Refuted 必须对应明确的规格。例如两个分段表示形式不同只能导致需要进一步比较，不能直接否定函数相等。

### 11.5 可满足性

可满足性是独立问题：

```text
Satisfiable(model_or_witness)
Unsatisfiable(certificate)
Unknown(blockers)
```

不得把“未找到矛盾”返回成 Satisfiable，也不得把“未找到模型”返回成 Unsatisfiable。

### 11.6 判定组织

判定服务按明确片段和解释分派，优先使用直接事实、精确域运算和可验证的逻辑规则。

等式闭包只能使用适用的等式和合法同余。函数恒等、点值等式、偏函数等式不可混用。

循环守卫按完整的语义查询键判断重入：命题结构、frame、解释和必要的绑定信息。禁止使用每次重建都会变化的 NodeId 作为逻辑循环身份。

禁止任意深度截断改变已声称的数学答案；资源限制统一返回 BUDGET。

### 11.7 精确、随机与近似

允许精确有理区间、模算法和经验证的随机搜索。它们不因含“采样”或“随机”就不属于纯符号系统。

要求是：结论由严格算法或证书支持。浮点近似与数值抽样只可作为候选建议或诊断，不能单独提供数学相等与完备性证明。

### 11.8 已知不可判定边界与拒答协议

| 触发情形 | 数学边界 | 理由等级 |
|---|---|---|
| ℤ/ℕ 上一般多项式方程解存在性 | 希尔伯特第十问题 | UNDECIDABLE |
| 一般线性递推数列是否有零项 | Skolem 问题；不能将它等同任意指数多项式整数零点问题 | FRAGMENT（开放的一般范围） |
| ℚ 上一般多项式方程解存在性 | 希尔伯特第十问题的 ℚ 版本 | FRAGMENT（开放） |
| 含充分丰富的 sin/exp/绝对值等函数表达式的恒等问题 | Richardson 型结果，必须保留具体定理的表达式类 | UNDECIDABLE（仅在该准确问题类） |
| 实指数域的一阶理论 | Macintyre–Wilkie 给出 Schanuel 条件下的可判定性，无条件情形开放 | FRAGMENT（开放） |
| 任意闭合初等常数或任意隐式超越根的相等/排序 | 没有本项目统一准入的总算法；不能仅凭“超越”或“无引理”套用 Richardson | FRAGMENT，或在准确子类已有定理时另行分类 |

不可判定、开放、尚未实现分别记录。函数恒等的不可判定性不能直接改写为所有闭合超越常数判零已知不可判定；单个实例仍可能有有限证明。猜想不能成为默认可信基础。理论边界只排除不可能的一般承诺，不删除已经有算法的子类或相邻表示/验证能力。

### 11.9 根与序：可判定性地图与完整表示层次

端点设施分别承担存在性、唯一性/计数、选根、相等、排序、取值和局部正则性；拥有其中一项不自动拥有其余全部。

| 结构/问题 | 可以承诺的能力 | 不可偷换的边界 |
|---|---|---|
| 有理/实代数系数一元多项式 | 根计数、全根隔离、代数根相等/排序及取号 | 区间重叠不直接证明同一根 |
| 有效实代数结构上的多元多项式公式 | 完整 CAD/QE、半代数区域判定 | 不能代替有理/整数域量词 |
| 具体声明的函数与有限证书 | 核验所给单调性/零点/顺序事实及条件 | 有限核验不等于该函数理论整体可判定 |
| 存在唯一性已证的隐式根 | 指定根的符号描述和已有性质 | 不自动产生 OrderedField 或与任意根的总比较 |
| 具有完整有效表示的进一步端点子类 | 按对应终止算法逐项扩充 | 不用数值分不开或缺实现宣称具体实例不可判 |

**用户例子的裁定。** h(x)=x+exp(x) 连续，h'(x)=1+exp(x)>0，且 h(-1)<0<h(0)，所以存在唯一 α∈(-1,0) 使 h(α)=0。这个根可以作为数学对象表达，唯一性有证据后可命名；没有证据时只保存待求根问题或带假设的描述，不能凭空发行数值对象。

α 不是实代数数：若非零 α 为代数数，则 Lindemann 定理使 exp(α) 超越，与 exp(α)=-α 矛盾。因此不能把它塞进实代数数表示。已证 -1<α<0 可以支持有限区间 (-1,α)、(α,0) 的顺序；与另一个任意根比较或在 α 处验证导数，则分别需要新的能力/证据。

最终系统保留以下层次，而不将整个端点语言永久限制为有理/代数数：

- **L0**：有理端点、Sturm 根计数和一维胞腔。
- **L1**：实代数根、Thom/隔离表示、精确算术/排序和多层代数点。
- **L2**：半代数区域与 CAD/QE，连接点、覆盖、包含及空性等服务。
- **L3**：数据化的函数序/正则性引理及其有限实例核验，有条件定律同步传播条件。
- **L4**：有存在唯一性见证的符号根对象，以及有完整有限顺序证据的端点集合；按操作所需证据执行，不伪造全域算术能力。
- **L5**：其他有已证明终止算法的端点/函数子类，逐项登记表示、闭包、判等/排序与定义域契约，再接入同一接口。

精确有理隔离区间是代数根的证明性表示，属于纯符号路线。一般超越函数的无限区间加细是半判定而非完整算法，不能因有预算就变成完整判定；Taylor/Remez 逼近不作为本项目纯代数核心的前置。条件化、有限证明和理论可判定子类的扩充继续保留，不用分析性逼近替代用户要求的代数语义。

### 11.10 Unknown 的三条出口

"任何环节出现 Unknown 就整体拒绝"过粗：它一并禁掉了条件化答案与开放步骤。正确的不变量是：**Unknown 只能沿三条显式出口离开系统，绝不静默消解。**

1. **条件化传播**：未决比较提升为答案中的显式条件（由条件分支结构承载），答案同时携带覆盖状态——完整，或部分（附逐条未决清单）。枚举型通道（契约是"全部解"）任一支未决时，要么整体拒答，要么显式降级为部分并列出未决项；已知解与未决项不得无标注地混在一起。
2. **开放步骤**：验证未决 → 步骤标为未决，永不标为否证。`No` 必须携带 `Refutation`；无证据不得声称否证。
3. **带理由拒答**：按 §11.2 的四类理由分派；定理级边界逐行对照 §11.8。

禁止的消解方式（一律视为作弊）：静默选支（把 Unknown 当真或假使用）、静默丢支（部分解冒充全解）、泛点答案（稠密开集上正确冒充全域正确）、无误差界的数值定序混入符号通道。

用户消解通道：假设与分类讨论是唯一合法的第三方消解——用户为具体实例注入比较事实或假设，帧内重判。其边界是：注入的事实只对该实例生效，系统不得据此把 §11.8 的 `UNDECIDABLE` 行改判为可判。

---

## §12 命题、规格与可信判断

### 12.1 Proposition

Proposition 不是“任意 Term 加一个字段名”。它必须经可信语义整理，保证：

- 命题类型正确；
- 自由符号在 frame 中可见；
- binder 索引良作用域；
- 运算与函数元数合法；
- 意义环境明确；
- 定义性前提已记录。

数学谓词通过声明注册扩展，不把所有未来数学关系写成内核封闭枚举。

实现切片（2026-11-09，结构定义性前提）：`Proposition` 已增加 `definedness: tuple[Proposition, ...]`，由 `propositions.check` 在定型后收集非正指数整数幂的 `Ne(base,0)`，并递归和/积/比较/`And`/`Or`/`Not`/`Implies`/`Guarded`/`Piecewise` 的操作数；`Quote`/`Set` 载荷与 `Binder` body/annotations 明确不检查，声明函数应用只递归参数。前提必须与命题同 `MeaningKey`、不得重复、不得等于命题自身，并参与相等/hash 与 seal。声明函数定义域、`Guarded`/`Piecewise` 分支局部语义、binder-aware premises 与一般偏函数定义域仍未建；这不是完整的 Proposition definedness 语义。

实现切片（2026-11-09，定义性前提的载荷边界）：结构前提已由 `Proposition` 记录，但 `ProblemSpec.region`、`OperationRequest.region`、`FunctionValue.intrinsic_domain`、`FunctionRepresentation.valid_on`、`MathematicalProposal.result_region`/`valid_on`/`excluded_cases` 的当前消费者仍按条件 term 读取，因此这些构造器在 `definedness` 非空时明确抛出 `ValueError`；`Proposition` 本身不被拒绝，`RegionSpec`/`GenericResult`/`AlgebraView` 继续按前提感知规则消费。该保守边界不是 `RegionSpec` 迁移完成；声明函数定义域、`Guarded`/`Piecewise` 分支局部语义与 binder-aware premises 仍未建。

### 12.2 标准规格族

| 规格 | 承诺 |
|---|---|
| `IdentityIn(K,a,b)` | 指定有效代数结构内相等 |
| `EqualOn(U,f,g)` | U 上定义且同值 |
| `SamePartialFunction(f,g)` | 定义域与值均相同 |
| `HasDerivative(U,f,x,g)` | 指定导数约定与区域上的导数关系 |
| `IsAntiderivative(U,F,x,f)` | U 上 F 可微且 D_xF=f |
| `IntegralValue(problem,v)` | 指定积分问题的值，含收敛与解释 |
| `IsSolution(problem,s)` | 候选满足原问题及成员约束 |
| `SoundSolutionSet(problem,S)` | S 中每个元素都是解 |
| `CompleteSolutionSet(problem,S)` | 原问题的每个解都在 S 中 |
| `EquivalentProblems(P,Q,map)` | 在指定映射下解集双向对应 |
| `Covers(region,pieces)` | pieces 覆盖 region |
| `IndependentSolutions(problem,basis)` | 指定意义下的解独立性 |
| `NonElementary(problem,class)` | 在明确函数类与常数域下无初等原函数 |

解集完全正确需要 soundness 与 completeness；单个统一证书可以同时证明两者，但字段不能混淆。

HasDerivative(U,f,x,g) 表示 U 的每个点上，按所选导数约定有 D_x(f)=g。经典导数需要 f 在点的邻域有定义；U 本身可以是闭集或有限点集，函数的固有域和邻域要求另行检查。在 V 上已证的关系可以限制到已证满足 U⊆V 的区域，这是一条明确的规格限制规则。

因此，全局多项式残差为零可以验证任何合法子区域上的同一关系；全局残差非零却未必否定一个受限区域上的关系。要否定后者，需要适配该区域的恒等判定或反例证据。

空区域不是合法的关系声明；请求区域必须是已证区域的子区域，否则操作拒绝，而不是把结果静默收缩到更小的区域。候选记录保留原 `ProblemSpec`；实际达到的区域属于 `OperationResult.region` 与 `VerificationLink.condition`，不写回原问题的 `region`。

实现切片（2026-11-09）：`Covers(region,pieces)` 已由 `RegionSpec`/`CoversCertificate` 在受限条件片段上发行并由 `verify_region_certificate` 独立重检；函数延拓把 `Covers(intrinsic_domain, representation_regions)` 作为新函数值的表示覆盖义务，`EqualOn` 仍只证明旧域上的一致性。一般覆盖代数、无限覆盖、表示重叠一致性与最大固有域未建。

实现切片（2026-11-09，定义性前提消费）：`conditions.premises_proved` 是唯一前提蕴含规则；`regions.premises_proved_from`/`proved_subregion` 要求 `certify_nonempty`/`certify_subregion`/`certify_covers` 与 `verify_region_certificate` 只在区域条件能证明参与命题的定义性前提时发行/接受证书。子区域证书检查子区域自身前提与目标区域前提从子区域条件成立；覆盖证书检查被覆盖区域自身前提与每个 piece 的前提从区域条件成立（严格 Or 读法）。`AlgebraView._issue_view`/`definedness` 与 `DefinednessService.covers` 消费同一规则；未证明前提不会被当作成立。该切片不声称一般半代数区域或完整偏函数定义域语义。

实现切片（2026-11-09，函数区域的前提感知包含）：`proved_subregion` 现在支持 `same_meaning=False`，仅用于调用方已独立校验两个命题同 world 且 frame 可见的情形；`FunctionEqualityChecker._check_equal_on` 用它要求 claim region 是各固有域与表示区域的全定义子区域，`_check_same` 对带开放前提的完整域条件返回 `Unverified(GUARDED)`；`FunctionExtensionOperation.propose` 与 workspace 的 `define_function`/`extend_function` 全部改用 `proved_subregion`。裸 Proposition 区域载荷在构造器拒绝部分条件。该切片仍不声称一般半代数区域、声明函数定义域或完整偏函数语义。

实现裁定（2026-11-10，`Covers` 当前片段）：本片段不建立独立的 `Covers(region, pieces)` Proposition 词汇、checker 或 operation。`CoversCertificate` 只是函数延拓表示覆盖的内部证书：由 `function_coverage_certificate` 在受限区域片段发行，并由 `FunctionEqualityChecker` 在 `EqualOn` 延拓证书中独立重检；它不发行独立 judgment，也没有注册的 `Covers` 规格或操作消费者。注册 `Covers` 规格/checker 属于未来 K1/S1 工作，必须与真实发布消费者同批加入。该裁定是范围明确的实现边界，不声称 §12.2 已完整实现（一般覆盖代数、无限覆盖、表示重叠一致性与最大固有域仍未建）。

### 12.3 Judgment

```text
Judgment(
    judgment_id,
    world_id,
    frame_id,
    proposition,
    obligations,
    inference_id
)
```

其含义是：

```text
Γ(frame), Δ(obligations) ⊢ proposition
```

Judgment 不因未决条件而等于无条件真理。条件性判断可以参与推导，但全部相关条件必须继续传播。

### 12.4 可信依赖

证明支持分成：

- 可见 HypothesisRef；
- 已发行 JudgmentRef；
- 受信任标准库的 BasisRef；
- 核心作用域规则产生的局部证明引用。

ArtifactRef、CandidateRef 和用户提供的裸答案不能作为可信前提。

其中 `HypothesisRef`、`JudgmentRef`、`BasisRef`、`AxiomRef` 是可持久化引用：`BasisRef` 由装配期准入记录（依据类型、版本、作用域与摘要），`AxiomRef` 只在引入它的 frame 及其后代可用。核心作用域规则在校验会话内产生的是 `LocalReceipt`（§12.7）：它只能支持同一会话内的暂存结论，不能跨会话、不能持久化，只有在 §13.9 的批次发布后才转成 `JudgmentRef`。

表达式计算可以把 Artifact 内的数学值作为规格输入快照，而不把该 Artifact 当作“已证明前提”。例如证明 D(x²)=2x 不需要先证明 x²。

### 12.5 InferenceRecord

统一记录：checker 标识与版本、输入支持、结论 JudgmentId、证书、语义快照与必要条件。

不为微分、积分、移项各创建一种内核 Step 子类。数学行为通过注册的规格与 checker 表达；核心作用域规则也使用同一发行记录结构。

### 12.6 不可变性

Judgment 与 InferenceRecord 追加后不修改。条件被清偿、查询上下文变化或对象从工作簿删除，都不重写原结论。

“当前可用”是对 Judgment 和查询 frame 的关系，不是 Judgment 上一个随时变动的布尔字段。

### 12.7 引用、回执、句柄与结果槽

三类“本地标识”容易混淆，这里固定各自含义与生命周期。

| 名称 | 是什么 | 生命周期 | 可否作可信前提 |
|---|---|---|---|
| `JudgmentRef` | 已发行判断的引用 | 持久 | 是 |
| `LocalReceipt` | 校验会话内未发行的证明回执 | 单次校验会话 | 仅在同一批次内 |
| `PlanHandle` | 数学计划内的局部标识 | 单次操作调用 | 否 |
| `ResultSlot` | 构造关系中的结果模板变量 | 单个任务组合 | 否（实例化并验证后才可能成为候选） |
| `ObjectVersionId` | 工作簿对象版本引用 | revision 生命周期 | 否 |

- `PlanHandle` 只存在于 `math`/`operations` 内部，由 workflow 映射成真实任务与 Artifact 身份（§16.3）。
- `ResultSlot` 属于 §17.6 的构造关系层，是模板元变量，不是自由数学变量，不能进入假设集合。
- `LocalReceipt` 属于校验层，进入账本只有一条路径：在 §13.9 的同一原子批次中被编入并发布。

---

## §13 可信内核、校验器与原子提交

### 13.1 内核的职责

可信内核负责：

1. 检查语义世界与上下文的一致性。
2. 检查命题的类型、绑定和符号可见性。
3. 检查假设、前提和证书的真实来源。
4. 调用已准入 checker，绑定它实际证明的规格。
5. 合并、处理并记录所有必要条件。
6. 实施有限的作用域逻辑。
7. 保证证明依赖无环。
8. 原子发行 Judgment 与 InferenceRecord。

内核不负责搜索积分策略、构造 CAD、消元、因式分解、选择用户焦点或维护对象显示名称。

### 13.2 可信计算基础

TCB 明确包含：

- 纯语法的不可变性、绑定原语和语义整理；
- 核心逻辑与作用域规则；
- commit 和可信 store 的不变量；
- 受信任数学 checker；
- checker 调用的精确代数、定义性和微分基础算法；
- 经过显式准入的标准库数学依据。

TCB 不是只有一个十几行的 commit 函数。减少 TCB 应以清楚契约和可验证证书为手段，而不是把实际信任的算法藏在“服务”名称后面。

### 13.3 CheckerSpec

每个注册项绑定：

```text
checker_id
checker_version
certificate_schema
accepted_problem_kinds
accepted_specification_kinds
verification_function
trusted_dependencies
```

证书 schema 与 checker 标识不可任意错配。加载时进行 schema 验证，检查大小与深度预算。当前 `InferenceRecord` 同时记录证书 schema 的 name/version，发布记录因此能说明实际准入的格式。

checker 必须从输入问题、数学数据和证书中得到实际验证的命题；不能只看证书里的 `success=True`，也不能接受任意调用方提供的 conclusion。

若调用方请求的命题与 checker 验证的命题不同，即使候选数值正确，也不得提交。例如回代验证得到 IsSolution，不能提交 `x=s` 作为原方程的必然推论。

### 13.4 校验上下文

`VerificationContext` 由内核根据指定 FrameId 构造，不允许调用方注入另一个 frame 的 context。

它提供：

- 固定 MeaningWorld 与 SemanticFrame；
- 可见的已验证支持；
- 定义展开、类型与定义性服务；
- 受预算约束的判定接口；
- 明确的代数请求与转换接口；
- 支持收集器。

通过判定服务取得并实际使用的事实必须形成语义支持。细粒度读日志可以关闭，作用域、世界版本和必要证明引用不能关闭。当前实现已提供 world/frame/frames、`DecisionService`、`SupportsService`、`BudgetService`、`AlgebraService`、`DefinednessService`、`AxiomRef` 集合与 `readable` 检查；完整支持收集仍按真实消费者逐步补齐。

实现切片（2026-11-10，固定请求 checker 的上下文代数）：`cas.kernel.evidence.context_algebra_mismatch` 是 Derivative/Elementary/Hermite/Linear/Gcd/Resultant checker 消费 `VerificationContext.algebra` 的唯一规则；无 context、context 无 algebra、与 checker 预装配 request 非同一对象分别返回结构化 detail。同一性比较是有意的：`AlgebraRequest` 是冻结的预装配对象，结构相等副本仍可能携带不同 parent/parameter/differential。`Candidate.algebra` 保存提出时的请求快照并由 `check_candidate`/`decide_candidate` 原样重提；函数问题没有代数视图，`FunctionEqualityChecker` 拒绝 algebra 快照，核心逻辑规则不要求 algebra。`validate_commit` 仍只从 `proposal.algebra` 构造上下文，缺失/不同由 checker 报 `InvalidEvidence`。该切片不声称完整支持收集、嵌入、跨 frame `externalizable` 前提弱化或结果语言覆盖。

### 13.5 commit 输入

```text
CommitProposal(
    frame_id,
    requested_specifications,
    premise_refs,
    checker_ref,
    certificate,
    condition_policy,
    budget_ticket
)
```

输入没有“请相信这些 Artifact 已经是真的”这一通道。

`condition_policy` 的类型是 ConditionPolicy，取值为 RequireProved、AllowConditional、RequestCases。默认底层数学断言 API 使用 RequireProved；交互工作簿可显式选择 AllowConditional 并展示条件状态。完整求解任务不会因为允许条件提交就自动变成泛参数任务。

### 13.6 提交流程

1. 固定 world、frame 与预算快照，验证请求来源与版本。
2. 对 requested specifications 做命题类型、绑定和可见性检查。
3. 解析所有前提引用，验证它们已发行、在当前 frame 可用或可作为条件前提。
4. 解码证书并检查它与 checker、问题、输入数学对象匹配。
5. 运行 checker，取得实际验证的规格、支持与新条件。
6. 确认 requested specifications 正是已验证规格，不允许偷换命题类型或量化范围。
7. 收集继承义务、新义务、定义性条件与映射条件，按语义身份去重。语义身份键是 `(compiled_environment_key, proposition)`（§6.2）：意义环境按编译键比较，不按 `frame_id`，也不按文本；只有编译键相同的条件才可能合并，文本相同但意义环境不同的条件不合并。
8. 在同一个查询语境下解析全部条件，应用同一个 condition_policy。
9. 验证证明边、条件清偿边和局部作用域导出不会形成循环。
10. 在暂存区建立完整记录，最终一次性原子发布。

任何阶段失败，都不得留下半个 Judgment 或没有对应支持的清偿记录。

### 13.7 提交结果

```text
Committed(judgment_refs, condition_report)
Deferred(blockers_or_case_requests)
Rejected(issues_or_refutation)
```

Rejected 中必须区分：证书无效、请求不合法、条件被否定和数学规格被否定。当前 `RejectedKind` 明确记录这四类；workspace 对条件否证返回 `UNSUPPORTED` 并保留 `refuted_conditions`，不把它伪装成结论否证或无效证据。

条件被否定不等于目标命题的否定。例如不能使用要求 a≠0 的公式，不代表 a=0 时原方程必无解。

### 13.8 假设引入

假设操作先创建包含 H 的子 frame，再在该 frame 中按核心规则发行 `Γ,H ⊢ H`。

禁止先在 Γ 中提交 H，然后才在工作流里把 H 加入新上下文。

声明和定义同样通过经过检查的上下文扩展入口建立，不允许工作流绕过无环、绑定与可见性检查直接写 ScopeStore。

### 13.9 事务与原子性

昂贵的数学验证在不可变快照上进行，不长时间占用发布锁。

验证完成后内核生成不可修改的 `ValidatedCommitBatch`。工作流事务协调器只能请求发布该 batch，不能改写其中的结论。

checker 内部的判定和条件清偿不递归调用会立即发布的 commit。已有支持使用已发行引用；新取得的回执使用本次验证会话的私有局部句柄。内核核对其来源、world/frame、闭合性和全部传递依赖，将真正被使用的支持按拓扑顺序编入同一 batch；有界代数计算不因此逐个创建证明节点。是否必须成为证明节点的判据是：当且仅当某事实会被某个已提交规格当作独立前提引用时，才为它建节点；只用于内部推进、其正确性由已列入 TCB 的完整算法直接保证、且不对外被引用为独立命题的中间事实不建节点。已固定 parent 的域内加法、乘法、gcd、消元与根隔离属于后者。

局部句柄不是公共 JudgmentRef，不能跨验证会话使用，也不能在发布前流入其他任务的前提。只有整批原子发布后才返回已发行引用。验证或发布失败时，所有未发布支持一并丢弃，不留下“外层失败但内层已提交”的隐藏副作用。

一次用户动作的发布单位包括：

- 可信判断与必要清偿；
- 输出 Artifact/ObjectVersion；
- Candidate 与验证关联；
- OperationEvent；
- 新 WorkspaceRevision。

默认内存实现采用一次状态批量替换；持久化实现使用同一数据库事务。不同 store 的写权限分开，但发布必须原子。

提交时若用户当前 revision 已变化，不把结果强行挂到新焦点上。保存为原快照的结果或显式研究分支，并提示来源。

### 13.10 独立验证的边界

搜索器可以调用相同的低层代数设施，但 checker 不导入其要验证的对应搜索器。

不要求每个可信基础算法重复实现两遍。独立性指验证的逻辑不依赖“搜索器说自己成功”，例如：

- 因式分解候选可通过乘回与不可约性证书验证；
- 原函数可通过独立微分与判等验证；
- 线性系统可通过矩阵关系与秩/空间证书验证；
- Gröbner 基可通过生成理想关系及 S-多项式归约证书验证。

某项完备性如果依赖可信完整算法而不是短证书，必须如实列入 TCB，不能伪称一个轻量 checker 已经证明全部性质。

---

## §14 条件传播、清偿与适用性

### 14.1 Obligation

```text
Obligation(
    obligation_id,
    proposition,
    meaning_frame,
    origin,
    introduced_by
)
```

origin 区分定义域、非零除数、参数特化、分支覆盖、正则性、成员条件等。原因用于解释，不改变数学含义。

两个文本相同但意义环境或绑定不同的条件不可直接合并。

含偏运算的条件本身也须经过定义性整理；条件之间的求值保护关系显式保存在命题结构中。条件集合的去重、排序与共享不能消除这些保护，也不能假定所有条件在无保护时都可求值。

### 14.2 条件继承

使用条件 Judgment 作为前提，继承全部尚需满足的条件。

去重依据是经过解释的命题、绑定与语义环境，不是名称、序号或 hash 单值。可实施的键与 §13.6 相同：`(compiled_environment_key, proposition)`；绑定已进入命题结构（§4.3），因此不需要另加名字比较。

内部可用持久集合和共享节点降低成本；对外必须能展开为完整条件列表。

### 14.3 清偿

清偿引用一个在查询 frame 中可用、且所有条件已闭合的证明。

禁止下列循环：

```text
J 需要 δ
利用 J 证明 δ
再用这个 δ 清偿 J
```

清偿证明的传递支持不得依赖目标条件本身或任何以该条件为未清偿前提的判断。检测规则：设 `S` 为“以 δ 为未清偿义务的判断”与 δ 本身构成的集合，清偿 δ 的证明 `P` 的传递支持集合 `support(P)`（含同一批次内暂存的支持）必须满足 `support(P) ∩ S = ∅`，且清偿关系图本身无环。两项检查都在暂存区完成，因此不需要先发布再回滚。

条件证明如果还有自己的未决条件，不能直接标记原条件已闭合。可以保留条件蕴含关系，但仍须把剩余条件明确传播。

### 14.4 ConditionPolicy 作用于全部条件

| 策略 | 未决条件 | 已否定条件 |
|---|---|---|
| RequireProved | Deferred，不发行目标 Judgment | Rejected |
| AllowConditional | 发行条件 Judgment，显示未决条件 | Rejected |
| RequestCases | 返回可供用户/策略研究的情形请求 | Rejected 或返回失效情形说明 |

该表同时适用于直接条件和继承条件。

构造条件命题 `H→P` 与“在已知 H 为假的语境中强行应用要求 H 的算法”不是同一操作。

### 14.5 适用性结果

```text
Applicable(closed_supports)
Conditional(unresolved_obligations)
Blocked(refuted_obligations)
OutOfScope(scope_or_world_issue)
```

Blocked 表示这条推导当前不能应用，不表示结论必假。

查询另一个 frame 时必须先检查作用域，再处理条件。旧分支的 Judgment 不因条件文本恰好相同就自动进入兄弟分支。

### 14.6 查询与解析分开

- `inspect_applicability`：纯读取已记录支持，返回当前已知状态。
- `resolve_applicability`：可以执行预算内的判定、形成新的闭合证明，再通过 commit 原子记录并返回状态。

用户界面默认调用后者，预算不足时显示未决。

日志模式不得决定是否调用正确性所需的条件解析。缓存命中只省计算，不改变语义。

### 14.7 模式

| 模式 | 永远保留 | 可减少的内容 |
|---|---|---|
| interactive | 世界/作用域、规格、支持、条件、校验结果 | 细粒度读日志、内部搜索轨迹 |
| derivation | 同上 | 部分内部代数细节 |
| audit | 同上 | 尽可能保留全部可复核诊断 |

checker 不读取模式来决定数学返回值。模式只影响已经确定结果之后的额外记账。

---

## §15 作用域导出、量化与分支合并

### 15.1 必需的有限逻辑

核心结构规则包括：

- 假设引用；
- 向子 frame 弱化；
- 蕴含引入与消去；
- 合取/析取的有限结构规则；
- 分类讨论；
- 受限制的全称引入与实例化；
- 经验证的矛盾分支关闭。

这些规则用于保护 CAS 操作的语义，不要求建立一个任意策略的定理证明搜索系统。

### 15.2 条件判断的假设导出

若：

```text
Γ,H ; δ₁,...,δₙ ⊢ P
```

且 P 和导出后的条件不含逃逸局部符号，则可导出：

```text
Γ ; H→δ₁,...,H→δₙ ⊢ H→P
```

不能简单删除 H，也不能把分支 δ 无条件提升到父 frame。

H 表示从父 frame 到源 frame 之间引入的完整假设包，包括定义性前提和局部约束，而不是界面选中的某一条公式。存在多个依次引入的假设时，按其依赖顺序嵌套守卫蕴含；只有证明操作数良定义后，才可合并为普通合取。后件的定义性按 §10.4 一并导出。

局部定义可以在经过验证的保守展开后消去；剩余局部变量必须按合法的量化规则绑定。不能删掉定义或声明记录后让其 SymbolId 留在父 frame 的结论中。

实现必须引用真实子 frame 与真实 Judgment，而不是接收一段声称成立的 P 文本。

### 15.3 全称引入

只有在专门的任意变量子作用域中引入的 eigenvariable，满足不依赖外部固定取值或未导出假设的条件，才可全称化。

例如：

```text
Γ, x:τ ; δ(x) ⊢ P(x)
```

可导出：

```text
Γ ; ∀x:τ.δ(x) ⊢ ∀x:τ.P(x)
```

前提是 x 对 Γ 新鲜，并且所有依赖均经过作用域检查。

由求解器选择的特定根、某个存在性见证、定义别名或已固定参数不能直接当作任意变量全称化。

### 15.4 全称实例化

实例化需要：

- 被实例化对象是真正的全称命题或相应的函数规格；
- 参数类型与定义性满足要求；
- 捕获规避替换正确；
- 原条件同步实例化。

普通自由变量替换不是全称实例化的同义词。

### 15.5 完整情形划分

`CasePartition` 至少包含父区域 U、条件 H_i、覆盖证明和各分支 frame。

- 覆盖是必要的。
- 互斥在声明为 partition 或需要唯一选值时必要。
- 仅进行逻辑分类讨论时，重叠分支也可使用，但不能伪称互斥划分。
- 条件包含局部符号时，必须先绑定或导出，不能直接出现在父区域覆盖公式中。

### 15.6 相同结论的合并

合并输入必须是：

```text
父 frame
覆盖 JudgmentRef
每支的真实 frame 与 JudgmentRef
需要导出的条件
目标 Proposition
```

可信规则检查：

1. 每支对应正确的 H_i。
2. 每个源判断确实在该支有效。
3. 导出的是 `H_i→P` 而不是裸 P。
4. 所有局部依赖已绑定或排除。
5. 覆盖与全部导出证明共同支持 P。
6. 剩余条件为正确导出的条件，而非任意字符串列表。

只提供 `answers=(P,P)` 永远不够。

### 15.7 不同结果的合并

若各支得到不同值，构造分段对象或条件解集，并证明各自规格与覆盖。

不得因为用户要求“合并分支”就强迫各支答案相等。

解集分支合并使用并集与条件区域；函数值分支合并需要唯一选值或经验证的重叠一致性。

### 15.8 两种分支不要混淆

- **研究分支**：尝试不同策略，可处于相同数学 frame；不需要数学覆盖。
- **情形分支**：按 H_i 扩展上下文；声称完整时必须有覆盖。

切换研究分支是历史操作。合并研究历史不会自动生成任何新的数学结论。

---

## §16 数学操作与插件协议

### 16.1 OperationSpec

操作是开放注册项，不是中央功能枚举：

```text
operation_id
input_schema
parameter_schema
result_schema
problem_or_specification_builder
candidate_generator
checker_bindings
explanation_schema
capability_requirements
```

添加一个数学功能主要修改其数学模块和装配声明，不修改 kernel 的变体清单或 workflow 的数学分派。当前 `explanation_schema` 尚未接线：没有记录或渲染解释配方的消费者，因此不创建空字段；待真实消费者出现时与 `MathematicalProposal` 的解释载荷同批建立。

### 16.2 操作输入

操作输入包含已整理的数学值、ProblemSpec、参数、区域与语义快照。

前端的 ObjectVersionId 和选择路径由 workflow 解析成这些输入；数学算法不接收可变工作簿或焦点对象。

例如“移项”在操作层解析成一个明确的方程变换请求，而不是让代数算法知道鼠标选中了第几行。

### 16.3 数学提案

`MathematicalProposal` 可包含：

- 结果数学值；
- 相应规格；
- 证书；
- 条件与未覆盖区域说明；
- 子问题描述；
- 候选构造关系；
- 数学解释配方。

它不是 Judgment，也不自行写任何 store。

数学模块只使用局部计划句柄与结果槽，不导入 TaskStore。workflow 将这些局部句柄映射成实际任务和 Artifact 身份。

### 16.4 trusted 与 untrusted 扩展

扩展分两类：

1. 候选/策略插件：只能输出数据提案，通过已有 checker 校验。
2. 可信数学插件：提供 checker 或基础定律，需显式准入并记录世界版本和信任依据。

普通用户规则默认属于第一类或当前 frame 中的显式假设，不直接取得第二类权限。

### 16.5 规则实例证书

规则应用证书记录：规则身份及版本、变量匹配、目标出现位置、实例化后的条件、祖先语境的提升依据。

checker 验证给定实例，不重新执行全局规则搜索。

结构匹配不等于数学匹配。若匹配依赖交换性、域正规形或其他定理，必须显式使用对应表示和证据。

### 16.6 数学同余

每个需要特殊语境的运算声明相应提升规则。例如：

- 标量代数等式在双方定义时可通过环运算提升；
- 导数位置需要适当区域上的函数关系和正则性；
- 积分位置需要被积函数、区域和可积性契约；
- 分段值位置需要该支实际支集；
- binder 内需要捕获规避与变量条件；
- Quote 不通过普通数学同余。

整个祖先路径都必须可提升，不能因为最邻近父节点是 Plus 就越过外层 Derivative 或 Quote。

---

## §17 工作簿、对象、任务与四种图

### 17.1 用户层对象

工作簿提供用户可命名的数学对象：

| 对象 | 典型内容 |
|---|---|
| 表达式对象 | 标量、矩阵、函数表达式 |
| 公式对象 | 方程、不等式、带量词公式 |
| 问题对象 | 求解、积分、消元、ODE 等 ProblemSpec |
| 结果对象 | 解集、原函数、代数根、区域、候选 |
| 定义对象 | 指向一个不可变 DefinitionBinding 的用户视图 |
| 推导视图 | 一组动作与数学关系的显示，不是新的事实来源 |

输入表达式不自动创建假设或 Judgment。

### 17.2 Artifact 与 ObjectVersion

Artifact 保存中性数学值及其解释快照。

表达式 Artifact 保持中性；函数 Artifact 持有 FunctionValue 的绑定、固有定义域和值域。验证区域属于关系，不自动变成表达式本身的固有定义域。对一个算法结果继续做表达式运算，与继续推进原数学问题，是两个明确的请求。

`ObjectVersion` 把 Artifact 放入用户工作簿的对象历史：

```text
object_id
version_id
artifact_id
created_in_frame
source_operation
presentation_metadata
```

对象名字存放在 revision 的对象名字映射中，不属于数学符号命名空间。对象改名不修改 SymbolId，也不创建 DefinitionBinding；用户编辑表达式产生新版本，不原地修改旧值。ObjectVersion 的显示元数据只保存该版本的排版和来源定位等信息。

对象引用使用与数学符号不同的显式语法，例如 `@E`。执行时它解析为当前 revision 中 E 对应的不可变数学值快照，不是会追随未来编辑的动态变量，也不把公式对象提升为真。要建立数学别名，必须另行执行定义动作。当前 `Session.parse` 已支持在公式中嵌入 `@LABEL`：先用私有占位符解析，再用捕获规避替换嵌入对象 term；缺失/隐藏 label 拒绝，`@LABEL` 不进入数学符号命名空间。`Artifact`/`ObjectVersion` 已作为 `Expression`/`FunctionObject` 的不可变类型视图接入；现有对象记录仍是唯一存储权威。

### 17.3 ProblemSpec

一个问题必须固定：

- 问题类别；
- 输入数学对象；
- 目标变量或函数及其绑定；
- 参数及其依赖角色；
- 系数范围与允许值域；
- 定义区域；
- 允许结果语言；
- 精确性、覆盖与完备性要求；
- 参数模式；
- 是否接受条件答案；若接受，则显式列出允许外置的前提集合 `externalizable_premises`（一组 §10.3 的 `Region`）。该集合必须是可枚举、可比较的显式数据；`CompletedConditional` 的判定就是“所有未闭合义务 ⊆ 该集合”（§18.1）。空集合表示不接受任何外置前提。

预算属于执行请求，不是数学问题本身。相同问题在更大预算下重试不改变其语义。允许保存条件 Judgment 的 ConditionPolicy 不会改写问题对完整答案的要求。

求解目标变量在问题中显式绑定。输入方程不会因为成为 ProblemSpec 就被加入 frame 假设。

实现切片（2026-11-09，函数问题绑定）：`ProblemSpec` 增加 `function_inputs: tuple[FunctionValue, ...] = ()`，固定函数问题所涉及的 `FunctionValue` 对象身份：参数绑定、固有域和每个表示区域都是函数身份的一部分，裸表示项不足以标识被证明的函数。非空时要求 `roles.target is None`；每个固有域与表示区域必须与类型化输入同 world。`roles.world`、`region` 与每个 `externalizable` 前提也必须与输入同 world。`compare_functions`/`extend_function` 的 `build_problem` 已传入解析载荷中的函数值。精确域/解释、`VariableRoles` 目标/参数排序与 `externalizable` 正向路径已由后续切片闭合；完整绑定位置与 binder-aware 角色、跨 frame 前提弱化、结果语言与一般完备性字段仍未建，不能把本切片写成完整 §17.3，本切片不声称完整 S1。

实现切片（2026-11-10，精确性、解释要求与稠密区域绑定）：`ProblemSpec` 增加 `exactness: Exactness = EXACT` 与 `interpretation_requirement: InterpretationRequirement | None = None`；`APPROXIMATE` 在构造期以 `ValueError` 拒绝（没有近似 checker），函数问题不得携带解释要求。`VariableRoles` 的目标/参数排序被 `ProblemSpec` 要求并与输入 `BindingView` 的同名符号排序核对。`ProblemSpec` 从输入绑定、角色与函数参数建立已知排序表，要求 `region` 与每个 `externalizable` 前提（含定义性前提）的自由变量都在表中且排序为 `RATIONAL`/`REAL`；未知、整数、复数或未绑定坐标在构造期拒绝。系数范围/值域字段与 `externalizable` 正向路径后由同日后续切片闭合；嵌入/实嵌入、参数关系、结果语言、完整绑定位置与 binder-aware 角色、注册 `Covers` 规格/checker 与一般完备性仍未建；本切片不声称完整 §17.3。

实现切片（2026-11-10，`externalizable` 正向路径）：`define_problem` 不再因 `problem.allows_unresolved()` 整体拒绝问题；它保留外部前提的 world、稠密排序与 frame 可读性检查，并把请求的显式 `externalizable` 集固定进唯一的 `ProblemSpec`。`apply`/`_apply` 增加显式 `externalizable` 参数；`operation.build_problem` 返回 `ProblemBuilt` 后，workspace 用 `dataclasses.replace` 把固定问题的集合替换为请求的显式集合，再执行维度检查、构造 `ExecutionRequest`、提案与提交。operation 自己构造的集合不构成第二权威；`run_task` 传入 `task.problem.externalizable`，`_same_problem` 继续精确比较该集合。该集合是可枚举、可比较的显式请求数据，不是 kernel obligation，也不是第二套 `ProblemSpec`。跨 frame 前提弱化、注册 `Covers` 规格/checker、嵌入/实嵌入、参数关系、结果语言、完整绑定位置与 binder-aware 角色、一般完备性仍未建；系数范围/值域字段由同日后续切片闭合，本切片不声称完整 §17.3。

实现切片（2026-11-10，系数范围与值域）：`ProblemSpec` 增加 `domain_requirement: DomainRequirement | None`，固定语言层系数范围 `coefficient` 与允许值域 `values`。有 target 的问题两者都必需，且 `values` 必须等于 `VariableRoles.target_sort` 经 `value_domain_of_sort` 的映射；函数问题固定 `coefficient=None`、`values=REAL` 且无 target；既无 target 又无函数输入的核心/实用问题保持 `None`。解析后的系数 parent 仍在 `AlgebraRequest`，问题不导入具体 Parent。`ProblemBuilt`/`ExecutionRequest` 要求 problem 与 algebra 的 coefficient/value domain 相等；`problem_mismatch` 消费固定请求值。跨 frame 前提弱化、注册 `Covers` 规格/checker、嵌入/实嵌入、参数关系、结果语言、完整绑定位置与 binder-aware 角色、一般完备性仍未建；本切片不声称完整 §17.3。

实现切片（2026-11-10，固定问题比较闭合）：`workspace._same_problem` 在既有 operation/输入/roles/function_inputs/region/result_language/coverage/externalizable 比较之外，精确比较 `ProblemSpec.exactness`、`interpretation_requirement` 与 `domain_requirement`；`run_task` 仍只通过该唯一比较器接受执行重建的问题，重建出不同答案标准、解释要求或系数/值域的执行被记录为 blocked。该切片只闭合工作流对固定 `ProblemSpec` 的比较，不新增第二套比较器，也不声称 §17.3 全部字段或 S1 终态已闭合。

### 17.4 Task 与 Candidate

Task 持有 ProblemSpec 和固定语义 frame。最小不可变记录为：

```text
TaskRecord(
    task_id,
    problem_spec,
    world_id,
    frame_id,
    created_by_event
)

CandidateRecord(
    candidate_id,
    task_id,
    result_artifact_refs,
    proposed_specifications,
    source_event
)
```

Candidate 的 proposed specifications 是搜索方声明要验证的承诺，不是已成立事实。验证关联单独追加，记录候选、确切规格、校验结果、查询 frame、证书以及成功发行的 JudgmentRef。一个候选可以有多个验证关联，不因后来增加完备性证明而改写原 CandidateRecord。

验证映射按规格索引，而不是只有一个 `validated=True`：同一答案可以已经验证成员正确，但尚未验证完备性。适用性与覆盖状态从这些记录及原请求导出，缓存不是第二份权威状态。

实现切片（2026-11-09）：函数延拓的 `Candidate` 证书携带 `CoversCertificate`；`FunctionEqualityChecker` 在核验 `EqualOn` 时独立重检覆盖并核对它精确匹配候选的右函数值。覆盖失败是 `InvalidEvidence`，不是 `Refuted`；普通 `EqualOn`/`SamePartialFunction` 证书不要求覆盖，`SamePartialFunction` 携带覆盖字段时明确拒绝。该覆盖只证明声明固有域被表示区域覆盖，不证明表示重叠一致性或最大固有域。

实现切片（2026-11-09，checker 绑定函数问题）：`FunctionEqualityChecker` 在 `problem_mismatch` 之后、按规格分派之前，要求 `compare_functions` 证书的左右 `FunctionValue` 精确等于 `problem.function_inputs` 的两项，`extend_function` 证书的旧函数等于唯一函数输入；缺失或不匹配是 `InvalidEvidence`，不是 `Refuted`/`Verified`。`EqualOn` 在 problem 有区域时把 `claim.region` 交给 `problem_mismatch`，由同一子区域规则检查 `problem.region ⊆ claim.region`；`SamePartialFunction` 在 problem 有区域时要求该区域可证位于两侧完整固有域内。每个 `FunctionValue` 的每个表示区域必须是其固有域的可证子区域；非稠密参数排序返回 `Unverified(GUARDED)`，claim region 含非参数自由变量返回 `Unverified(FRAGMENT)`。该切片不声称一般函数定义域语义或完整 §17.4 闭合。

实现切片（2026-11-10，候选代数快照）：`Candidate` 增加 `algebra: AlgebraRequest | None`，记录候选被提出时的精确预装配请求；非空时要求 `algebra.roles == problem.roles` 与 `algebra.target == problem.target`，函数问题（`problem.function_inputs` 非空）必须为 `None`。workspace 在 `_apply` 保存 `execution.algebra`，`edit_candidate` 在清除证书时保留该快照，`_candidate_proposal` 原样提交，因此 `check_candidate`/`decide_candidate` 复核同一 target/parameter/interpretation/differential，而不是重新装配另一个视图。该字段是候选数据，不是第二套角色权威；`externalizable` 正向路径已由同日后续切片闭合；跨 frame 前提弱化、注册 `Covers` 规格/checker、嵌入/实嵌入与结果语言仍未建，本切片不声称完整 §17.4 闭合。

Draft 属于尚未完成整理的 TaskDraft；整理成功后才创建具有完整 ProblemSpec 的 TaskRecord。不用一个可为空的 problem_spec 字段让运行中任务混入未整理输入。

### 17.5 解集表示

标准表示至少包括：

- 空集；
- 有限点集；
- 区间或区域；
- 参数化族，含新参数的绑定与允许区域；
- 条件集合；
- 集合并；
- 指定 parent 上的代数集合；
- 明确标为残余问题的隐式描述。

隐式重述原问题不自动满足“给出显式解”的请求。结果语言是 ProblemSpec 的一部分。

其中“参数化族”引入的新参数是真正的 `SymbolId`，绑定在结果对象与结果 frame 里：不属于父 frame，不出现在父 frame 的结论中，因此不触发逃逸检查，但必须有显式值域，并声明其相对当前导子的常数角色（积分常数、ODE 自由常数即此类）。它们与 §15.3 的 eigenvariable 不同：eigenvariable 是可合法全称化的任意变量，解族参数只是结果描述中的自由符号。

### 17.6 ConstructionRelation

构造关系描述若干任务结果槽之间必须满足的关系。

```text
ConstructionRelation(
    relation_template,
    typed_result_slots,
    source_plan,
    frame,
    region
)
```

结果槽属于专用元变量/模板层，不是普通 Sym，也不是可以进入假设集合的自由数学变量。

实例化所有结果槽后，得到候选组合。该组合必须验证原问题规格。当前已实现 `function_extension` 构造关系：`extend_function` 在独立 `EqualOn` checker 成功后记录 source/target 对象版本、specification 与 frame；一般多结果槽联立关系仍待真实消费者。

### 17.7 四种图

| 图 | 节点与边 | 是否允许环 |
|---|---|---|
| 可信证明 DAG | 判断、条件支持、推理依赖 | 禁止 |
| 执行依赖 DAG | 必须先完成的任务与子任务 | 禁止 |
| 构造关系超图 | 候选结果槽之间的联立关系 | 允许 |
| revision 历史 DAG | 工作区版本、分叉与显式合并 | 禁止 |

“积分 I 依赖 J，J 的构造又提到 I”进入构造关系图，不创建一个永远互相等待的执行依赖环。

调度器可把联立构造关系的强连通部分交给求解任务，得到候选后统一验证；不能通过递归调用重复打开同一个任务来假装解决循环。

### 17.8 Focus

Focus 只是界面指向：对象版本、某个任务、候选或出现位置。

它不隐式改变数学上下文。操作执行时必须把焦点解析成固定输入快照。

### 17.9 Revision 与事件记录

工作区快照至少包含：

```text
WorkspaceRevision(
    revision_id,
    parent_revision_ids,
    world_id,
    active_frame_id,
    object_version_map,
    object_name_map,
    visible_task_ids,
    visible_candidate_ids,
    verification_links,
    construction_relation_ids,
    execution_event_refs,
    focus,
    producing_event_id
)
```

普通 revision 有一个父版本，显式研究历史合并可以有多个；对象与任务集合采用持久化映射共享，不复制整本工作簿。引用其他分支的结果仍保留其原 frame，出现在工作区不等于在当前 frame 可用。当前内存实现把可见的 `TaskRecord`/`Candidate` 版本作为 revision 快照保存，undo/redo 因此不会把未来状态泄漏回旧视图；`Occurrence` 选择记录同时携带 path 与 expected subterm。`Revision.object_names` 记录对象版本的稳定显示名；`Event.actor_kind` 区分用户、脚本与策略，`operation_version` 固定注册操作版本。

动作记录至少包含：

```text
OperationEvent(
    event_id,
    operation_ref,
    actor_kind,
    input_revision_id,
    frame_id,
    input_refs,
    parameters,
    output_refs,
    verification_refs,
    execution_report,
    explanation_ref,
    output_revision_id
)
```

operation_ref 包含操作版本；actor_kind 区分用户、脚本与策略。输入与输出引用固定对象版本、任务或候选身份，不保存“当前焦点”这样的可变引用。执行报告记录成功、未覆盖、预算耗尽、取消或错误，不产生数学真假。

区分工作区动作与执行观测。一次改变对象、假设、候选可见性或分支的用户级动作产生一个不可变 OperationEvent 和对应 revision；undo/redo 以这种动作作为单位。长任务的开始、进度、耗时和取消通知归属于 ExecutionAttempt 的观测记录，通常不创建工作区 revision。需要发布阶段候选或用户显式 checkpoint 时，才形成新的工作区动作。

任务的固定问题、尝试的生命周期与候选的数学验证分别记录。任务摘要由已有结果派生；并发计算仍属于启动快照，用户移动历史或焦点后不会被进度通知改写语义状态。

只有 workflow application 建立这些工作流记录；可信验证关联只能引用内核已发行或同一原子批次即将发行的判断。验证关联是状态与出处边，不进入可信证明 DAG，也不构成执行依赖；证明依赖只由内核的推理记录承担（§12.5），所以工作区里引用一个判断不会制造证明环。后一种关联在暂存区使用私有批次句柄，对外可见时必须已经转换为真实已发行引用。事件引用输出、输出记录来源事件属于出处关系，不作为证明或执行依赖边，因此不制造逻辑循环。

---

## §18 工作流状态机、调度与历史

### 18.1 Task 状态

```text
Draft → Ready → Running
                  ├─ WaitingForSubtasks
                  ├─ Blocked
                  ├─ PartiallySolved
                  ├─ Completed
                  ├─ CompletedConditional
                  └─ Cancelled
```

- Draft：还未完成语义整理。
- Ready：问题已合法且执行前提明确。
- Blocked：需要输入、条件或尚未实现的能力。
- PartiallySolved：有结果，但原请求的覆盖未完成。
- Completed：原请求的必需规格均已验证，必要条件在请求 frame 中闭合。
- CompletedConditional：原请求明确允许相应条件答案，必需规格已条件验证；不得显示为无条件完成。
- Cancelled：执行取消，已有候选可以保留。

这是用户视图的主状态图，不是把数学完成性与执行生命周期压成一个可变枚举。每次执行尝试单独记录 Ready/Running/Waiting/Blocked/Finished/Cancelled 等状态；一个已经完成的任务不因后续尝试取消而丧失已有证明。部分结果与取消可以同时展示。

任务完成只能相对于 TaskRecord 固定的 ProblemSpec 和 frame 判断，不能改用用户当前更强的子 frame。进入 a≠0 分支后，条件公式可以在该支适用，但不会使原 AllParameterValues 任务变成完整。

缩小参数区域或增加假设时，创建新的受限问题与任务，并显式记录它和原问题的限制关系。原问题仍保留尚未覆盖的参数情形，直至取得相应覆盖证明。

CompletedConditional 只接受原请求允许外置的前提；必须分类的参数退化情形、解成员条件和结果区域不能被移成外部义务来冒充完整覆盖。泛参数答案对全参数请求仍是 PartiallySolved，无论用户是否允许保存条件 Judgment。

“无解”不是任务失败状态，而是经验证的完整空解集结果。

状态由验证记录与请求派生，不由搜索器赋值：

| 状态 | 派生条件 |
|---|---|
| Draft | 语义整理未完成，尚无完整 ProblemSpec |
| Ready | ProblemSpec 完整、执行前提明确、尚无任何尝试结果 |
| Blocked | 没有任何已验证规格，且存在 blocker（需要输入、条件或未实现能力） |
| PartiallySolved | 至少一项已声称规格得到验证或存在候选，但覆盖未完成 |
| Completed | 请求要求的全部规格都有闭合支持，且不存在未处理的必需情形 |
| CompletedConditional | 请求显式允许外置前提，未闭合义务 ⊆ `externalizable_premises`，且所有必需分类情形已处理 |
| Cancelled | 执行被取消（已有候选保留） |

Blocked 与 PartiallySolved 的分界是“有没有任何已验证规格”；CompletedConditional 与 Completed 的分界是“未闭合义务是否都落在请求允许的外置集合内”。

实现切片（2026-11-10，`externalizable` 正向路径）：`derive_task_state` 继续把已验证/条件链接的 `condition` 与 `obligations` 作为开放条件；只有全部开放条件都等于固定 `ProblemSpec.externalizable` 中的显式前提时才派生 `COMPLETED_CONDITIONAL`，无开放条件仍为 `COMPLETED`，否则为 `PARTIALLY_SOLVED`。proposal 的 `result_region` 进入 `VerificationLink.condition`，它是工作流条件，不写成 kernel obligation；无条件验证结果不会因为请求允许某些外置前提而变成 `COMPLETED_CONDITIONAL`。当前比较是命题意义相等（同 term、同 meaning 环境），跨 frame 的前提弱化、超过两情形的条件合并与一般条件证明合并仍未建；本切片不声称完整 §18.1。

### 18.2 Candidate 状态

候选分别记录：

1. 验证：Unchecked、Verified、Refuted、Unverified。
2. 适用性：Applicable、Conditional、Blocked、OutOfScope。
3. 覆盖：Unclaimed、Generic、Partial、Complete。
4. 表示是否满足请求的结果语言。

这些维度由证明和请求导出，不由搜索器随意赋值。

候选被否定只淘汰该候选，不表示任务无解。

### 18.3 执行流程

1. 从当前 revision 解析输入对象、选择和 frame。
2. 语义整理并固定 ProblemSpec/OperationRequest。
3. 生成或选择数学提案。
4. 创建中性候选、子任务或构造关系。
5. 对需要承诺的规格执行可信校验。
6. 按策略处理条件与覆盖。
7. 原子发布结果、验证关联、事件和新 revision。
8. 根据实际结果更新任务的派生状态。

用户可以保存未验证候选并继续编辑，但不能将其作为可信前提。后续数学计算可以读取候选的值，产生新的候选并最终验证整个规格。

### 18.4 任务复用

只有数学问题、frame、解释、变量绑定及结果要求相同或存在已验证转换时，才可复用任务结果。

键使用完整语义描述比较；摘要只作索引。alpha 等价的绑定问题可规范化以复用，但不能合并不同自由参数。

不同研究策略可以共享已完成子任务；不能共享仍带有不兼容假设的可信结果。

### 18.5 Undo/redo

undo/redo 只移动 WorkspaceRevision 指针，不删除可信数学历史，不改写对象版本。

新操作在旧 revision 上产生分支。旧分支的焦点、名字映射、上下文和对象集合完整保留。

撤销一条假设会回到没有该假设的 frame；依赖它的旧结果仍存在，但在新查询环境下不可直接使用。

### 18.6 历史合并

历史合并可以把多个研究结果放进同一个工作区视图，但不自动证明它们相容或产生共同结论。

数学分支合并必须另走 §15 的可信协议。

若两个分支对同一显示名建立不同定义，合并界面要求区分名字或选择版本，不偷偷使用最新定义。

### 18.7 错误与恢复

- 用户输入错误保留输入文本并显示位置，不产生数学结果。
- 算法未覆盖保留任务与 blocker，允许更换策略。
- 证书被拒绝保留候选供诊断，但不贴已验证标签。
- 程序内部不变量失败报告 InternalError，不伪装成 FRAGMENT。
- 发布失败不留下部分可信记录；可从原快照重试。

---

## §19 手动交互、选择路径与操作语义

### 19.1 最小用户模型

普通用户只需理解：

1. 我正在处理哪个对象或问题？
2. 当前允许什么假设和变量取值？
3. 我执行了什么动作？
4. 得到了什么结果，附带什么条件？
5. 这是一个候选、一个解，还是完整答案？

不要求用户理解内核 IDs、checker 或清偿账本。

### 19.2 三种输入动作

示意语法，不承诺与当前 REPL 相同：

```text
expr E := x^2 + 1
assume a > 0
solve a*x+b=0 for x
```

第一条创建表达式对象；第二条扩展假设上下文；第三条创建问题。

`expr E := ...` 中 E 是对象标签，不是数学定义。后续公式用 `@E` 嵌入该对象的值快照；普通数学名字 E 仍走 SymbolDeclaration/DefinitionBinding 的名字环境。界面点击对象可以代替输入 `@E`，但内部请求必须保留同样的区别。

单独输入一个公式默认创建公式对象，不自动当作假设。用户选择“假设”“证明”“求解”后才赋予动作意义。

### 19.3 提出方程

用户可以：

- 把方程作为已知条件加入子 frame；
- 把方程作为待求解目标；
- 把方程作为待验证推导；
- 把方程作为候选构造约束。

界面使用不同状态标识。禁止用一个 Claim 命令同时承担四者。

### 19.4 方程变换

每次变换标注关系方向：

- 等价变换；
- 原问题推出新问题；
- 新问题推出原问题；
- 带映射的解集对应。

两边加同一项在适当加法结构与定义性下可等价。

两边乘零可保持某个推论方向，但通常不能保持解集等价。两边除以 a 必须处理 a≠0。

平方、开方、取对数、消分母都不能默认标为双向等价。

### 19.5 代换动作

| 动作 | 行为 |
|---|---|
| 编辑/句法替换 | 新 Artifact，不自动承诺原结论仍成立 |
| 依据等式改写 | 消费真实等式证明并验证整条祖先路径 |
| 实例化全称命题 | 按绑定语义实例化并传播条件 |
| 参数特化 | 变换问题、条件、域映射与上下文 |
| 坐标换元 | 建立源/目标区域及数学映射 |
| 展开定义 | 只沿不可变定义方向展开 |

界面可以把它们放在同一个“代换”菜单下，但请求类型必须不同。

### 19.6 出现位置选择

选择记录 `ObjectVersionId + occurrence_path + expected_subterm`。

执行前重新确认版本和出现位置。如果对象已经编辑，不能把旧路径应用到新表达式上。

绑定体中的选择附带局部绑定视图。选中一个显示字母不等于选中所有同名字母。

### 19.7 条件体验

主结果旁显示最短准确状态，例如：

```text
已验证
在 x≠0 上成立
已验证一个解，尚未证明完整
泛参数答案：要求 a≠0
断点 x=0 尚未验证
当前假设下不可使用
```

展开后显示条件来源、已知证明、阻塞能力与可执行的下一动作。

用户可以选择研究条件成立的子情况；系统不能偷偷把未决条件加入已有 frame。

### 19.8 操作历史的显示

默认展示用户级动作，不展示每次整数乘法或重建节点。

一个动作可展开为：数学关系、所用条件、证书摘要、内部算法轨迹。

手动和自动步骤使用同一个显示模型；自动过程可以折叠为一个动作，但不得伪造未实际执行的推导。

---

## §20 自动算法、SAINT 策略与解释

### 20.1 三个分离组件

- **算法引擎**：在指定片段内计算候选或带证书的结果。
- **策略引擎**：选择下一种算法、改写、换元或子任务。
- **验证系统**：检查承诺，不信任策略排名或搜索成功标志。

SAINT 风格模块属于策略引擎，不取得直接发行 Judgment 的权限。

### 20.2 策略建议

`StrategySuggestion` 包含：

```text
operation_id
parameters
expected_subproblems
applicability_conditions
cost_features
explanation
```

cost_features 可包含次数下降、分母复杂度、扩张塔高度、预计分支数、条件强度与已知算法覆盖。

“看起来更简单”只用于排名，不用于证明正确。

### 20.3 自动与手动共享什么

共享：ProblemSpec、OperationSpec、候选、条件、checker、结果表示与历史事件。

不强制共享：搜索算法、每一步微观过程和策略选择。

用户可以接受、修改或拒绝建议；修改参数后视为新的提案重新检查。

### 20.4 策略失败

找不到建议只说明策略未找到下一步。不得返回“不可积”“无解”或“恒等式为假”。

证明不可积或无解必须来自相应完整算法或已验证的否定证书。

### 20.5 解释的三个层次

1. 用户动作层：为什么选择分部积分、消元或某种换元。
2. 数学关系层：实际成立的公式、区域与条件。
3. 算法证据层：归约、矩阵关系、根计数和证书。

可以另行生成一条更易读且经验证的教学式推导，但必须标明它是结果的另一条验证路径，不是假装原算法当时采用了这些步骤。

### 20.6 自动重写纪律

- 定义默认单向展开。
- 自动规则必须有明确的终止策略、度量或饱和预算。
- 用户指定的反向等式改写是一次显式动作，不加入全局双向循环。
- 相等闭包不是无界重写器；必须有结构性去重和合法同余。
- 预算耗尽时保留已验证结果或未验证候选的真实状态。

---

## §21 完整交互案例

本节规定端到端行为，示意命令不要求复用 v4 语法。

### 21.1 输入表达式后求导

```text
expr E := x^2
对 E 关于 x 求导
```

过程：

1. 按工作簿配置声明 x 为实标量，并固定 D_x。
2. E 是表达式 Artifact，不是假设。
3. 数学引擎得到 2x。
4. 校验 `HasDerivative(R, x², x, 2x)`。
5. 显示新的表达式对象及其已验证导数关系。

任何 store 中都不得出现 `proposition=2x`。

### 21.2 x/x 的化简与延拓

```text
expr E := x/x
化简 E
```

输出值表示为 1，但函数解释仍限制在 x≠0。操作证明 `EqualOn(x≠0, x/x, 1)`。

若用户再令 x=0：原表达式特化失败；不能因为值表示已经是 1 而返回 1。

若用户主动选择“填补可去奇点”，这是另一个延拓操作，必须证明相应极限或代数延拓性质，并产生新的函数对象。

### 21.3 参数方程完整求解

```text
solve a*x+b=0 for x over R
```

建立目标变量绑定的 ProblemSpec，而不是假设 `a*x+b=0` 已对当前自由 x 成立。

泛参数消元产生 `-b/a` 及 a≠0；参数分类任务处理 a=0 的残余问题。

最终返回三支条件解集及覆盖证明。用户只选择非退化分支时，新 frame 含 a≠0，产生对应的受限任务；界面明确显示研究范围收窄，原全参数任务不会因此完成。

对于整数 x，非退化支进一步要求 `a` 整除 `b`（在 a、b 为整数的相应请求下）。不能把实数答案直接贴成整数解。

### 21.4 从 x=1 做代换

```text
assume x=1
把 x 替换为 2
```

系统必须要求选择动作意义：

- 句法编辑：得到公式数据 `2=1`，不产生可信结论。
- 参数特化：原假设同步变为 `2=1`，目标上下文不一致或特化无效。
- 依据等式改写：需要一条可用的 `x=2` 证明，不能凭输入文本得到。

不存在从原假设直接提交无条件 `2=1` 的合法路径。

### 21.5 点方程与函数恒等式的求导

`x=3` 是一个关于取值的条件，不能两边求导推出 `1=0`。

如果已有 `ForAll(x∈U, f(x)=g(x))`，并且 U 与可微性符合导数规格，才可建立相应导数恒等式。

隐式微分需要 y(x) 的依赖声明、沿解曲线成立的关系以及相应正则条件，不借普通“对方程两边求导”绕过这些前提。

### 21.6 两次分部积分的定积分关系

定义确定函数：

```text
I(x) = ∫₀ˣ exp(t)sin(t) dt
J(x) = ∫₀ˣ exp(t)cos(t) dt
```

两次分部积分产生：

```text
I = exp(x)sin(x) - J
J = exp(x)cos(x) - 1 + I
```

这些是两个积分对象之间的已验证函数关系，不是循环证明。任务计划中的未知结果槽可组成联立构造系统。

解出候选：

```text
I(x) = [exp(x)(sin(x)-cos(x)) + 1]/2
```

最终通过导数与 I(0)=0，配合所用积分基本定理及正则性验证结果。

执行依赖图无环；联立关系可以含 I 与 J 的互相引用。

### 21.7 不定积分与候选组合

请求 `FindAntiderivative(exp(x)sin(x), x, R)`。

分部积分策略引入两个结果槽，写出候选组合约束。它们不是“两个任意原函数集合相等”的命题。

线性求解得到一个具体 F 后，验证 `IsAntiderivative(R,F,x,f)`。若还请求全部原函数，再利用连通区域上导数为零的函数为常数这一依据，给出 F+C 及 C 的常数角色。

不能只在打印器后面加 `+C` 就声称证明完整。

### 21.8 正向换元不强求可逆

对：

```text
∫ 2x/(1+x^4) dx
```

使用 u=x²，构造 atan(x²) 作为原函数。正向链式验证不需要排除 x=0，也不要求 x² 在整个 R 上单射。

若另一个操作需要由 u 反解 x，则必须区分正、负分支及零点，不能继续沿用同一个无条件逆映射。

对定积分，采用哪个换元定理、是否使用有向端点关系或需要单调划分，也必须体现在证书中。

### 21.9 分段连接点

```text
f(x)=1
F(x)= x      当 x<0
       x+1   当 x≥0
```

逐支导数为 1 不足以验证 R 上的原函数，因为 F 在 0 跳跃。

允许的结果是：在 R\{0} 的两个连通分支上验证成功；若原请求是 R 上的原函数，则该候选不满足规格。

“边界未检查”不是全域 Verified 加一条警告。

### 21.10 求根与选分支

```text
solve x^2=1 for x over R
```

得到集合 {-1,1}，分别验证成员并验证覆盖全部根。

若只先找到 1，显示“已验证一个根”，不把它变成原方程推出 `x=1`。

用户选择 x=1 分支时建立新的研究上下文或选择解实例，不改写原问题的完整解集。

### 21.11 ODE 基本解族

```text
solve y'(x)=y(x) on R
```

候选 `y=C*exp(x)` 需声明 D_x(C)=0。

残差验证只证明该族内函数是解。完整性还需对应的一阶线性方程理论、区域正则性与参数化覆盖依据。

若加入 y(0)=2，产生新的初值问题，并验证对应唯一解，而不是悄悄修改旧任务。

### 21.12 分支来源不可伪造

即使父 frame 已证明 H∨¬H，提交一段载荷声称“两支答案都是 0=1”也必须被拒绝。

只有真实存在的分支 Judgment、合法的作用域导出和覆盖证明，才能触发分类合并。

### 21.13 编辑定义与撤销

先定义 `u:=x²`，生成对象 E=u+1；之后把显示名 u 改定义为 x³。

E 继续引用原 DefinitionBinding。新的输入引用新绑定。需要让 E 采用新定义时，执行明确的重新解释或替换动作，得到新版本并重新验证。

undo 恢复原 revision 的名字映射和 frame，不修改任何已有 Term 或 Judgment。

---

## §22 多项式、线性代数与 Gröbner 基

### 22.1 公共代数机器

多项式加乘、除法、gcd、无平方分解、因式分解、结式、子结式、判别式、矩阵算法与 Gröbner 基是公共设施。

Risch、CAD 和方程求解不能各自复制一套系数算术与判零逻辑。

所有算法的输入包含明确 parent，输出属于可核对的 parent。算法按已取得的结构能力分派，而不是从 Term 形状猜域。

### 22.2 多项式契约

- 单项式指数为非负整数，生成元顺序固定。
- 零系数按系数域判零消去。
- 单项式序显式进入计算请求或 parent 的表示结构。
- 一元次数、总次数、主变量次数使用不同名称。
- 精确商、带余商、伪余式分别返回有定义的结果。
- 系数环非域时不得调用需要逆元的普通域除法。
- 特征 p 下的无平方分解与特征零算法分派不同，导数为零不等于常数多项式。

### 22.3 分式与有理函数

分式结构要求分母非零且底层结构满足其构造前提。

约分是表示优化或正规化，不删除原函数语义桥中的定义域条件。

域元素判等可用交叉乘法；声称规范约分表示时必须真正实现对应的 gcd/内容处理。

符号参数分式必须附带 §8 的泛参数解释或特化条件。

### 22.4 线性代数

线性求解返回结构化结果：

```text
Inconsistent(witness)
AffineSolution(particular, nullspace_basis, rank_witness)
```

在一个有效域上，这描述完整仿射解空间。无自由方向表示唯一解，不表示“有自由方向就不完整”。

参数问题另加有效参数区域与覆盖证明。不得只返回一个 particular 然后把自由方向丢掉。

证书可包含：

- `A*p=b`；
- `A*N=0`；
- 基的独立性；
- 秩或行变换关系，证明不存在遗漏方向；
- 不相容时导出 `0=c≠0` 的行组合。

同一次消元结果应供秩、特解与零空间共同消费，不重复运行消元只为不同 API 名称。

### 22.5 因式分解

必须区分“给出一些因子”“给出乘积正确的分解”“给出完整不可约分解”。

乘回只证明乘积正确；完整不可约分解还需系数范围、单位、重数与不可约性依据。

有限域、整数/有理数、多元与代数扩张上的算法分别声明片段，不通过通用名称隐藏缺失的能力。

### 22.6 Gröbner 基

Gröbner 服务固定系数域、变量、单项式序和输入理想。

基础输出包括基、输入与输出生成元之间的表示关系、归约证书和必要的参数条件。

验证基至少区分：

1. 新生成元属于原理想。
2. 原生成元属于新理想。
3. 满足相应 Gröbner 判据。

只证明一个多项式能被候选基约成零，不足以证明该基是原理想的 Gröbner 基。

### 22.7 理想与解集

理想属员、根式理想属员、代数闭包中的零点集、实零点集和有理/整数解集是不同问题。

不能把 Gröbner 基算法的成功等同于已经给出全部实解、全部有理解或根式显式解。

正维系统可以返回有明确语义的代数集合或参数化描述；能否满足任务取决于请求的结果语言。

消分母时须处理饱和、排除分母为零的点或等价的条件机制，不能用清分母后的额外根冒充原问题解。

### 22.8 参数化代数

GenericParameters 可在参数分式域中计算，并返回有效区域。

AllParameterValues 需要综合 Gröbner、三角分解、案例分类或其他已验证的覆盖方法；未建立这些能力时返回部分参数分类，不伪造全覆盖。

---

## §23 实代数、CAD 与量词消去

### 23.1 目标范围

完整 CAD 的主契约是：在指定有效实代数系数结构上，对实闭域一阶多项式公式进行分解与量词消去。

必须分别支持和报告：

- 符号不变或真值不变分解；
- 带自由变量的量词消去；
- 解集或无量词公式构造；
- 仅请求投影数据或胞腔数据的模式。

整数或有理数上的量词不自动进入 CAD。它们需要不同问题种类与算法。

### 23.2 实代数数

实代数值至少包含：所属有效结构、定义关系、选根信息与精确比较能力。

隔离区间属于表示见证，可被精化；数的身份不由可变区间端点决定。

根精化缓存与不可变数学值分离。不同多项式或不同扩张上下文中外观相同的区间，不代表相同代数数。

### 23.3 一元根隔离

接口必须明确定义：

- 零多项式与常数多项式；
- 端点是否计入；
- 重根与无平方部分；
- 有理点根与非退化隔离区间；
- 区间是否严格分离；
- 所隔离的是哪个多项式的哪个根。

常数多项式不进入以零导数作除数的 Sturm 步骤。

不强制先穷举整数约数才能做实根隔离。大系数下的位复杂度必须受预算控制。

### 23.4 多层样本点

高维样本点使用三角代数关系或等价的有效实代数扩张表示。

每个坐标的定义依赖低层坐标，必须保留基域、嵌入与根顺序。

多项式在样本点上的符号计算属于实代数机器，不通过浮点近似猜测。

### 23.5 基准投影路线

v5 的完整基准路线选择保守的全投影 CAD：采用完整 Hong 投影所需的系数、reducta、主子结式系数及相关数据，并按其正确性定理建立 lifting 前提。

不能把“若干判别式加两两结式”当作已实现该完整算法。

McCallum 等更小投影可以作为后续优化，但其适用前提必须验证；前提失败时回到已建立的完整基准路线，而不是忽略失败。

投影、lifting、真值传播和解公式是分离模块，共享明确的 ProjectionData 与 CellData。

`ProjectionData` 至少包含：`level`、参与投影的多项式集合、系数集合、reducta、主子结式系数、判别式集合、由投影产生的关系，以及每个多项式的来源与版本。`CellData` 见 §23.7。两者都必须能独立复核，即只用它们就能重建 lifting 前提与符号不变性；只给最终胞腔列表不算完成投影。

### 23.6 零化与降次

必须处理某多项式在低维胞腔上恒等为零、主项系数消失及次数下降。

样本点上为零不能单独推出整个胞腔恒为零。需要投影不变量和系数符号证书支持。

因子归一化、去重与内容分离不得把条件性等价的多项式混为无条件相同。

### 23.7 CellData

胞腔数据包含：

```text
level
parent_cell
section_or_sector
sample_point
boundary_descriptions
sign_information
invariance_witness
```

section 与 sector 使用封闭变体，不以任意字符串决定其字段含义。

多项式在胞腔上判号的接口要求明确的 sign-invariance 依据。仅给一个裸隔离区间，不足以证明任意新多项式在该区间对应根处的符号。

### 23.8 公式处理与量词

输入先经过类型、绑定、定义性与有序域检查。合理的清分母必须保留符号与非零条件。

量词顺序、自由变量和变量重命名由统一绑定层处理。算法可在保持量词依赖的范围内优化变量顺序，不能任意交换不同量词块。

量词消去是算法服务，不要求通用内核进行无界逻辑搜索；其结果仍通过明确规格与可信验证路径进入 Judgment。

### 23.9 解公式

无量词输出必须符合请求的结果语言。

若请求纯实闭域公式，内部 root-index、胞腔编号和任意可调用 CAD 对象不能出现在最终数学公式中。

解公式构造可以增加区分胞腔所需的多项式或使用可消去的 Thom 描述。不能假设原投影多项式的同一个符号向量必然唯一确定一个连通胞腔。

验证目标是：在完整覆盖的每个相关胞腔上，输出公式与输入公式的量化真值一致。

只构造出胞腔而尚未完成公式转换时，可以交付 CAD Artifact，但不能声称已满足纯公式 QE 请求。

### 23.10 证书与成本

候选数据可以包含投影关系、根计数、样本点、符号表、覆盖与量词真值汇总。

独立 checker 不得只重跑同一不可信 CAD 搜索然后比较结果。无法提供轻量证书的完整性部分，可由显式列入 TCB 的完整算法承担，必须如实标明。

内部每个胞腔不必创建一个工作流步骤或独立 Judgment；一次任务可以在边界提交一个组合证书。

CAD 的最坏复杂度不能通过更薄的账本消除。预算耗尽时部分树仍是部分结果，不能标为完整 QE。

---

## §24 积分、Risch 与定积分

### 24.1 积分问题分类

至少区分：

- 寻找一个原函数；
- 描述指定区域上的全部原函数；
- 在指定初等函数类中判定可积性；
- 普通定积分；
- 反常积分；
- 主值等其他明确的积分解释。

不同请求不能共享一个没有语义参数的 `Integrate` 结果槽。

### 24.2 原函数验证

默认规格为 `IsAntiderivative(U,F,x,f)`。

验证内容包括：

1. F、f 的类型与解释一致。
2. F 在请求区域和导数约定下可微。
3. D_x(F)=f 在该区域成立。
4. 定义域、连接点与参数条件没有丢失。

求导得到一个非零形式多项式，并不对任意低维或受约束区域自动构成否证；必须使用与区域相适配的判等或反例依据。

### 24.3 Risch 的完整性契约

完整 Risch 是相对于已准入有效微分域及其常数域的初等可积性判定，不是任意语法表达式的总积分函数。

准入条件包括真实提供的：

- 精确域算术与判等；
- 常数域识别及所需常数运算；
- 生成元关系与扩张结构；
- 多项式与分式算法；
- 算法需要的因式分解、线性相关、RDE/PRDE 等能力。

实现缺少其中一项时，不得把该缺口写成一个神奇 oracle 然后宣称算法完整。

目标覆盖允许的代数与超越初等扩张，但每个已发布 FragmentSpec 必须列明实际支持的扩张种类及否定结论的函数类。

### 24.4 内部分解结果

使用明确的微分分解：

```text
f = D(v) + Σ c_i * D(u_i)/u_i + r
```

结果记录：

- v 的域内表示；
- 对数项的常数 c_i 与非零域元素 u_i；
- 残余 r；
- 分解证书；
- r 的状态：零、已证非初等、尚未判定；
- 对应的分析解释条件。

`尚未判定` 与 `已证非初等` 是不同变体。

c_i 属于常数域需要依据；u_i 作为形式域非零元不免除函数解释中的非零区域条件。

### 24.5 算法模块

Risch 主循环组织：塔分析、分层归约、分母处理、留数、微分方程和结果组装。

可复用工具独立于主循环：

- 有理函数积分；
- normal/special 分裂与无平方分解；
- 微分 Hermite 归约；
- 留数与对数导数识别；
- RDE、参数化 RDE 和次数界；
- 代数函数域算术及相关归约；
- 常数线性相关；
- 表达式与微分塔转换。

级数、特殊函数积分和数值求积可以独立建设，不成为所有 Risch 子片段的无条件前置清单。

### 24.6 非初等性

`NonElementary` 必须说明：基微分域、允许的扩张类、常数域约定、所用完整性定理与算法障碍证据。

例如 RDE 搜索在一个任意试探次数内失败，不足以证明无解；必须有完整次数界和完整子问题判定。

如果否定结论当前依赖可信完整算法而不是可独立短验证的证书，应记录该信任依据。不能把一个带有 detail 字符串的 No 当作已经机械复核的非初等性证明。

### 24.7 参数积分

对 C(a) 上的形式积分完整，不自动意味着对所有实际参数值的分类完整。

AllParameterValues 请求需要处理结构变化、退化分母和生成元关系变化。无法完成分类时，可以返回泛参数原函数及异常条件、已解决分支和残余任务。

完整参数分类只在已经定义并实现的参数片段上承诺，不把任意实参数常数问题包装成可判定。

### 24.8 定积分

定积分验证不能仅检查 `D(F)=f` 和 `F(b)-F(a)`。

必须检查所用积分基本定理的条件、区间、奇点、分支、端点极限和收敛性。

- 普通积分与反常积分有不同规格。
- 主值不作为反常积分发散时的默认替代。
- 反向积分界采用有向积分语义，不把反向界一概判为错误。
- 无穷端点是积分问题数据，不是普通域中的有限元素。
- 等端点积分按指定积分定义处理，不通过不相关的代数规则猜测。

无法判定收敛时返回未决或条件答案，不凭数值稳定性提交有限值。

### 24.9 全部原函数

在已验证的连通区域上，可由零导数为常数的定理给出 F+C。

不连通区域按各连通分支使用独立常数，或以等价的局部常数函数描述。

常数的值域与相对导子明确，不把符号 C 永久设为对一切变量常数。

---

## §25 ODE、PDE 与相邻能力

### 25.1 微分方程 ProblemSpec

必须包含未知函数签名、独立变量、导子、系数结构、区域、方程、初始/边界条件、结果语言与覆盖要求。

未知函数不是普通标量常数；导数节点保留其绑定和依赖。

### 25.2 线性 ODE

公共基础包括微分算子/Ore 结构、线性代数、微分域与因子分解。

求解器可以按已知片段采用因式分解、降阶、微分 Galois 方法、特殊函数识别或其他有明确契约的算法。

n 阶线性方程的基本解系需要：

- n 个经验证的解；
- 线性独立性，例如合法点上的非零 Wronskian；
- 系数与区域的正则性；
- 完整性所用的线性 ODE 理论。

残差为零本身不证明完整。

### 25.3 非线性 ODE

采用问题分类、对称性、积分因子、降阶和候选搜索等策略。

策略失败返回未决。只有适用的完整子算法或严格障碍证明才能声称指定函数类内无解。

隐式解需要验证隐式关系及其适用条件；不能把隐式函数定理要求的非退化条件省略。

### 25.4 结果语言

分别标识：初等、Liouvillian、特殊函数、D-finite/算子表示、隐式关系、级数、数值对象。

给一个新函数命名并把原方程作为定义，不等于满足“求出初等闭式”的任务。

如果请求允许算子加初值定义的精确函数对象，该表示必须有相应存在唯一性和语义契约，并如实显示结果类别。

### 25.5 PDE

PDE 是单独能力族，不因支持多个导子就声称具备一般求解器。

需要显式声明导子交换条件、函数空间、区域和边界条件。微分代数、对称性或分离变量只承诺各自覆盖的片段。

ODE 的存在唯一性和解空间维数结论不能直接套用到 PDE。

### 25.6 离散与数论问题

求和、差分、递推、整数解和有理点问题使用同样的任务与验证框架，但拥有各自的数学算法。

- 一般整数多项式求解存在不可判定性边界。
- 一般有理点问题不因系数域是 Q 就自动可解。
- 发散级数的正则化值不是普通级数和，必须是不同请求。

不为这些能力再建立一套独立上下文、候选状态和证明账本。

---

## §26 Python 类型、不可变性与扩展边界

### 26.1 类型目标

类型系统负责排除结构误用，不声称证明数学定理。

优先防止：

- 把 Artifact 当作前提；
- 把表达式当作命题；
- 把一个 parent 的元素交给另一个 parent；
- 把错误 payload 交给 checker；
- 读取某个结果变体不存在的字段；
- 将 TaskId、JudgmentId 等混用。

### 26.2 值对象

语法、规格、上下文描述、parent 描述和证书数据使用不可变值对象。

`frozen=True, slots=True` 只是手段之一，必须同时防止内部可变容器别名泄漏。接收外部 dict/list 时复制并转为不可变结构，不能只给原可变对象套一个只读类型注解。

构造期预计算 hash 与结构键允许使用封装的内部初始化手段；创建后不得改变其数学意义。

### 26.3 封闭结果

Verdict、CheckOutcome、CommitOutcome、Task 的受控状态等使用显式联合类型、final 变体和穷尽检查。

不通过一个可自由继承的空基类假装已经封闭。

错误使用 `bool(Verdict)` 应立即抛出明确的编程错误。

### 26.4 开放扩展

操作种类、数学谓词和插件能力通过注册扩展。

注册表在装配结束后冻结。重复身份、证书 schema 冲突和不匹配签名在启动时失败，不留到用户操作时才出现缺字段错误。

允许在一个明确的注册边界做类型擦除；边界外恢复具体类型，不让 object/Any 在代数热循环和整个工作流中传播。

### 26.5 泛型代数

采用 `Ring[E]`、`Field[E]`、`Polynomial[E]` 等关联接口，使系数类型由 parent 保持一致。

运行时仍需检查 parent 身份、生成元维数和外部输入合法性。Python 泛型不能替代这些动态不变量。

能力协议必须提供真实实现。不存在“声明满足 Protocol，所以数学性质自动成立”。

### 26.6 ID 与句柄

静态类型使用不同 ID 类型。运行时对外引用还必须校验所属 store/session、存在性和可见性。

仅用 NewType 包装整数不能防止持久化输入伪造跨 store 引用。

显示名称与内部 ID 分离，ID 不提供自动数学信任。

### 26.7 错误边界

输入解码、插件协议、持久化载入和公共 API 是验证边界。

已验证的内部结构不在每个小函数重复防御式检查，也不捕获所有 Exception 后返回 Unknown。

InternalError 保留堆栈与相关不可变快照，禁止伪装成“数学上不可判定”。

### 26.8 静态检查

目标代码启用严格的类型检查、未处理联合检查和禁止隐式 Any 的纪律。

检查工具帮助发现结构缺陷；不能以“类型检查全绿”替代绑定、域公理、条件传播和数学性质验收。

---

## §27 性能、预算、缓存与并发

### 27.1 性能原则

优化顺序：

1. 选择合适数学算法与表示。
2. 控制系数增长和中间表达式体量。
3. 避免重复投影、消元、求根和定义展开。
4. 共享不可变结构与计算结果。
5. 减少边界记账成本。

不预设“LCF 太慢”是主要瓶颈，也不为了节省记录跳过条件和验证。

### 27.2 代数工作区与规范化成本

热循环只处理已确定 parent 的元素和轻量状态。表达式、作用域与历史在管线边界解析，域内运算直接调用相应代数接口。

规范表示在公开元素构造边界建立，私有算法工作区可批量积累。例如 m 个稀疏多项式求和时，将全部项汇入一个系数字典，再消零和按单项式序排序一次；成本取决于输入总项数和最终支持，而不是每加一项就重建所有前缀多项式。乘法、矩阵归约和模重构也按各自代数不变量选择批处理边界。

以已绑定 parent 的 E 值完成中间运算，只有需要保存或复用的用户级结果才形成 Artifact/Task。数学操作完成后，核验其规格并一次提交，或按少数有独立数学意义的阶段提交。

性能报告同时记录转换、算法、核验和发布；小例只用于检查机制，具有代表性的稀疏/稠密、参数和高位系数案例用于选择算法。

### 27.3 预算对象

`BudgetTicket` 在一次顶层请求、子任务和 checker 之间按明确策略共享或分配。当前实现的 `BudgetTicket` 记录 `ExecutionBudget` 与已消耗节点/深度，`spend` 超限返回 `None`；它不改变已给出答案的真假。

至少限制：

- 时间与取消点；
- 节点/单项式/矩阵规模；
- 整数与分母位数；
- 扩张次数；
- 分支与胞腔数；
- 内存与持久化写入量。

大幂、巨大展开和递归分支应在分配前做保守预算检查，而不是内存耗尽后再报告 BUDGET。

子调用不得通过重新创建满额预算绕过顶层限制。

### 27.4 预算与正确性

预算可以影响是否得到答案，不可改变已经给出答案的真假含义。具体边界：预算耗尽或取消只允许产出 `Unknown(BUDGET)`、未验证候选，或明确标注为部分的结果；不允许把被截断搜索得到的“完整解集”“无解”“不可积”当作答案。§11.6 的“禁止任意深度截断改变已声称答案”在此收口。

耗尽时可保留已验证片段和候选，但必须保留未覆盖范围。NoSolutions、NonElementary、Complete 等结论不能来自资源截断。

取消不破坏已提交结果，也不发布半成品证明。

### 27.5 缓存

所有派生缓存有容量与淘汰策略，公开诊断统计。

语义缓存键包含必要的：world、frame、parent、解释模式、变量角色、区域、导子和算法/证书版本。

不能只按打印字符串缓存数学判断。

- 精确 Yes/No 仅在相同语义条件下复用。
- BUDGET 结果不作为永久数学否定缓存。
- FRAGMENT 随能力注册版本变化失效。
- 结构共享缓存失效不改变相等和 hash。

### 27.6 上下文与依赖记录

最低正确性记录固定整个 world/frame 快照与必要的证明支持。

精细读依赖可用于增量失效与解释，但若关闭它，缓存必须使用较粗且安全的完整快照键，不能继续假设只依赖少量未记录字段。

### 27.7 存储分层

- 已发行判断在会话内不可覆写或改变身份。
- 持久化可信数据可以分页载入，内存缓存有界。
- 工作流对象和事件可按用户配置归档或截断可撤销历史。
- 活跃结果需要的证明支持必须保持可解析，不能因裁剪界面历史而消失。
- 空间不足时拒绝新的原子发布，不删除仍被引用的证明来腾空间。

不把“逻辑追加式”误写成“所有历史必须永远强引用在内存中”。

### 27.8 并发

数学求解在不可变输入快照上并行运行。默认使用单写入协调器发布内核与工作区事务。

并行任务共享只读 parent、声明和安全缓存，不共享会被修改的 frame。

同一问题的多个候选可以同时产生；先完成的候选不自动取消用户仍需的完整搜索，除非任务策略与覆盖要求允许。

### 27.9 性能证据

性能报告应分别记录语义整理、代数计算、校验、提交与显示耗时，以及节点、位数和缓存指标。

不以单个小例或全量测试通过声称架构高效。优先优化实际 profile 的热点，保留优化前后的相同数学规格。

---

## §28 持久化、重放与外部接口

### 28.1 持久化格式

默认数据交换采用版本化 JSON 结构，内部持久化可采用 SQLite 事务。人类可读脚本是另一层，不作为唯一无损存储格式。

禁止使用 pickle 或任意 Python 求值载入不受信任工作簿。

序列化保存：

- schema 版本；
- world 与声明/规则版本；
- SymbolId、绑定与 parent 描述；
- frame 和定义依赖；
- 问题、对象、候选与区域；
- 证书与证明支持；
- 事件、revision 和用户显示信息。

### 28.2 载入不等于信任

文件中标为 Verified 的对象不能直接成为可信判断。

载入需要检查结构、绑定、引用、世界版本、checker/codec 兼容性，并验证证书或符合明确的可信存档策略。

无法重验证的结果可以作为中性 Artifact 打开，但显示“验证状态尚未恢复”。

### 28.3 哈希与身份

持久化摘要使用稳定的规范编码与密码学摘要，用于完整性和内容索引；不使用 Python hash。当前 `World.digest`/`FrameStore.digest(frame)` 已使用 `hashlib.sha256` 和确定性结构 key；持久化索引与重放仍待实现。

数学相等仍不能只靠摘要相等。自由符号、parent 和语义环境必须保留完整身份，避免不同参数被序列化归并。

同一快照的输出应确定；不同会话中独立声明的同名字母不要求自动共享身份。

### 28.4 重放

重放分为：

- 数据重放：恢复对象与历史；
- 验证重放：重新检查数学规格和证书；
- 搜索重放：重新执行策略，可能因版本或预算得到不同轨迹。

恢复一个已验证结果不必重跑整个昂贵搜索，只要已有证书和所依赖的可信设施足以复核。

### 28.5 Python API 分层

| API | 输出 | 承诺 |
|---|---|---|
| `algebra` 低层 | parent 成员、算法数据 | 输入满足协议时的精确代数运算 |
| `propose(request)` | 候选提案 | 无可信结论承诺 |
| `calculate(request)` / `verify(...)` | 带规格与条件的验证结果 | 明确的已验证数学关系 |
| `decide(frame,P)` | Verdict | Γ 下的命题判断 |
| `Workbook.apply(...)` | 用户动作结果和新 revision | 编排、验证与历史原子发布 |

不要使用同一个函数配 `verify=False` 后仍返回外观相同的“可信结果”类型。提出候选与得到已验证结果使用不同接口与类型。

### 28.6 外部求解器

外部求解器输出数学数据、条件与证书，默认视为候选。

不能解析其控制台中一个 `true` 就生成 Judgment。没有可验证证书且未被明确列入 TCB 的外部答案保持未验证。

外部服务的失败、超时和不支持不等于数学否定。传输边界限制数据大小，不允许载荷执行宿主代码。

### 28.7 导出与显示

显示层可使用人类名称、传统积分记号和简化排版，但不能改变结果对象语义。

显示 `+C`、省略条件、压缩解分支或使用近似小数时，必须有相应真实数据与清楚标识。

证明详情可折叠，条件状态不可伪装成无条件状态。

---

## §29 命名、职责与工程纪律

### 29.1 名称约束

- `normalize` 必须说明规范化的结构与不变量。
- `simplify` 是启发式表达式优化，不假装是所有数学对象的唯一正规形。
- `verify_*` 不执行对应问题的候选搜索。
- `is_zero` 只在可完全判零的有效成员接口返回 bool。
- 一般语义判零使用返回 Verdict 的 `decide_zero` 或明确的查询接口。
- 不驻留的构造器不叫 `intern_*`。
- 对象序号不叫 hash。
- `complete` 不代表唯一解、没有自由参数或没有报错。
- Context 名称必须指出是 MeaningWorld、SemanticFrame、AlgebraRequest 还是 VerificationContext。

### 29.2 单一职责

一个模块可以包含紧密相关的算法，不要求机械地“一函数一文件”。

但下列职责必须隔离：

- 搜索与验证；
- 语法替换与数学改写；
- 类型与值域声明、计算 parent 选择；
- 候选构造关系与可信假设；
- 数学分支合并与历史合并；
- 代数热循环与工作簿记录。

### 29.3 无隐式全局状态

域工厂、规则、checker、操作和声明经显式 builder 装配并冻结。

允许固定语言签名和纯不可变常量。用户变量、当前假设、活动分支、导子和参数模式不放在模块级可变全局状态中。

### 29.4 数据化数学语义

函数与常数定律来自声明和可信依据，消费模块不得凭具体名称加分支。

语言结构分派和代数算法的表示分派可以存在，但必须与数学定理的适用域分开。

在边界检查某个表示是不是 Fraction，不等于按 Python 类型猜测用户整个表达式的数学域；两者不得混为一条禁令。

### 29.5 参考实现纪律

借鉴数学算法、输入输出和边界处理，不照搬历史数据结构和未声明的隐式假设。

参考库的能力判断需要实际定位算法及其限制，不能从 `.rlg`、文件大小或关键词未命中推断整个系统的能力。

参考程序的数值输出与本系统相同，不自动构成证明。

### 29.6 文档与实现

- 设计裁定只在架构文档中维护。
- 实现状态只在进度文档中维护。
- 参考取证独立记录。
- 被替换的设计必须标记历史或删除，不让两套相冲突定义同时充当当前规范。
- 不添加只断言某个旧文件名永不出现的门禁；检查真实的结构、依赖与语义性质。

### 29.7 数学操作命名与职责表

名字描述实际数学运算，不描述当前测试、某个调用方或“处理一切”。以下是命名语义，不要求把每一行做成独立文件：

| 建议名称 | 必须具有的含义 | 不得混称 |
|---|---|---|
| normalize_polynomial | 固定 parent/单项式序下收集项和系数 | 全局 simplify |
| reduce_mod_polynomial | 对指定模多项式取余 | 任意理想正规形 |
| normal_form_mod_ideal | 对已建立 Gröbner 基的理想正规形 | 未经判据的规则余式 |
| exact_quotient | 要求整除并给精确商 | 带余除法或偷偷进入分式域 |
| divmod / pseudo_divmod | 商余恒等式 / 带显式乘子的伪除法 | 同一个含糊 divide |
| extended_gcd | gcd 与 Bezout 系数及单位约定 | 只返回某个公因子 |
| squarefree_decomposition | 单位、平方自由因子及重数 | 完整不可约分解 |
| factor_polynomial | 指定系数结构中的单位/不可约因子/重数 | 只乘回正确的任意拆分 |
| specialize_parameters | 检查参数关系与局部化的求值映射 | 普通语法替换 |
| change_generators | 显式生成元映射与表示转换 | 修改全局符号角色 |
| differentiate_polynomial | 指定生成元的形式偏导 | 含系数导子的总微分 |
| apply_derivation | 显式 DifferentialStructure 上的 D | 默认所有非 x 符号导数为零 |
| hermite_reduce | f=D(v)+r 的指定归约 | 声称 r 已经积分或不可积 |
| solve_risch_equation | 指定微分域中带完整界的 RDE 解问题 | 任意一阶 ODE 求解 |
| isolate_real_roots | 指定多项式的全根计数与隔离 | 数值近似根列表 |
| sign_at_algebraic_point | 精确代数点处的多项式符号 | 整个胞腔的符号不变性 |
| project_cad / lift_cad | 固定投影算子 / 在其前提下提升胞腔 | 无前提的通用 project |
| verify_* | 核验给定输入、候选与证书 | 重新搜索答案 |
| propose_* | 构造候选，不发行信任 | calculate 后附一个未消费 success |

核心循环应直接呈现代数关系：加、乘、除、余式、gcd、矩阵行变换、导子、映射、子结式和取号。避免以 apply_rule、process、handle、engine 等泛名隐藏实际数学；协调器可以通用，但数学函数必须具体。

### 29.8 Python 代码组织

- 数据记录、结构运算、算法控制、语义桥、核验、用户编排分工明确，尽量沿现有 owner 增长。
- 单个算法可以使用局部可变数组/字典，公开结果冻结；不能为不可变性把每个中间系数包进账本对象。
- 公共边界做载荷、parent、维数和作用域检查；内部直接消费已成立的不变量，不重复广泛防御。
- 使用显式联合及穷尽分派，不靠动态属性探测弥补类型设计；类型擦除只在注册/解码边界出现一次。
- 参数名区分 coefficient、parameter、generator、derivation、region、premise 与 certificate，不以同一个 context/value 隐藏不同对象。
- 能用名称和类型表达的语义不写重复注释；注释只说明不明显的定理前提、表示约束或良基递归原因。
- 修复先有回归，算法有不变量/性质和边界用例，优化必须保持同一规格并有 profile；不以字符串门禁代替这些验收。

---

## §30 完整能力路线、依赖图与迁移边界

### 30.1 迁移原则

这不是再包装一次现有工作流，也不是把最终 CAS 缩减为求导或积分演示。30.2–30.7 保留迁移边界，30.8 起规定完整能力图。边界是每个数学里程碑的验收要求，不是要求先建完全部工作流再开始数学算法。

能够保留的是经过独立核对的精确代数算法、数学声明数据与表示工具；不能因为某模块通过旧测试就默认其操作语义符合 v5。

迁移期间未满足 v5 规格的旧结果只能作为候选数据，不能绕过新边界进入可信 store。

### 30.2 第一边界：结构与可信性

先闭合：

- Term 不可变与结构 hash；
- 碰撞安全的集合、闭包与查询键；
- 自由符号身份和完整绑定操作；
- Proposition 类型边界；
- 假设正确作用域；
- 分支证明的真实引用；
- 计算结果、解成员与完整解集的区分。

这部分未闭合前，不以增加 Risch/CAD 功能掩盖可信性缺陷。

### 30.3 第二边界：语义与有效域

建立 MeaningWorld、SemanticFrame、AlgebraRequest 和 AlgebraView。

将纯代数算法从 Term 和隐式上下文中剥离，去掉任意 TermField 兜底。

用参数线性方程、代数系数、多项式/分式、函数定义依赖验证域接口的闭合性，而不是只验证常数算术。

### 30.4 第三边界：对象化工作流

随对应数学里程碑实现 §21 的完整纵向案例：输入、对象、任务、候选、验证、条件、历史与撤销全部贯通。不能把“全部案例已经贯通”当作开始实现积分、方程或分段算法的前提，因为这些案例本身就消费这些算法。

终态需要的任务图、构造关系、分支历史与持久化全部保留在设计中；实现则随真实消费者接线，不预建空壳，也不从架构中删掉尚未施工的终态职责。

研究分支和情形分支必须从一开始区分，避免后续再以合并代码补逻辑漏洞。

### 30.5 第四边界：数学能力生长

以有明确规格的完整片段逐步增加多项式、实代数、微分塔与求解算法。

“片段完整”允许诚实拒绝片段外输入，但不允许在片段内只为手头案例加分支冒充通用算法。

Risch、CAD、Gröbner 和 ODE 共用域、变量、条件、任务与证书设施，不再私造平行协议。

### 30.6 旧 API 的退出

不保留旧语义兼容层或两套名同义异的 Claim、Subst、Solve、Context、Step。保留经过独立核对的底层算法不等于保留旧 API；新旧实现切换时同步迁移消费者并删除旧入口。

尤其不能把旧 `Solve` 的 `x=s` 结果直接包装成 v5 CompleteSolutionSet。

退出清单还包括过渡期的封闭命令接口：`Command`/`CommandName`、`checker_id` 字符串分派以及各 `*Payload` 数据类（由 §16.1 的开放操作与 §13.3 的 `CheckerSpec` 取代），以及 v4 的 `GuardPolicy`（由 §14.4 的 `ConditionPolicy` 取代）。退出条件是：对应操作在新协议下首次贯通 §21 的一个端到端案例之后。

迁移完成的模块删除旧语义入口和误导文案，不以兼容名称掩盖行为变化。

### 30.7 进度职责

本节定义完整设计的能力依赖、施工次序和验收门槛，不提供虚构工期或假完成记录。

已完成记录追加到 `progress.log`；施工路线写入 `roadmap.md`；当前未实现项、已知缺陷、失败案例与下一批工作写入 `AGENTS.md` 第五节。未施工的终态能力继续保留在本节，不因暂缓实现而删除；存在目录、协议或算法名字不算完成。

### 30.8 终态能力总表

编号表示能力节点，不表示一次性提交或必须完全串行的阶段。每个节点均须具有低层数学 API、所需的语义桥、对应规格及验证路径；仅作为公共工具的节点可以由上层算法消费，不要求单独增加 REPL 命令。

| 节点 | 最终交付 | 直接数学/工程依赖 | 主要消费者 |
|---|---|---|---|
| S0 语言与意义 | 纯 Term、绑定、sort、统一声明、World/Frame、词法定义 | 基础身份与不可变值 | 全系统 |
| S1 请求与解释桥 | 请求局部变量角色、有效域视图、源定义域、嵌入/转换、区域与结果语言 | S0、相应代数结构 | 全部数学操作 |
| K0 信任与核验 | CheckerSpec、实际规格匹配、假设/条件/支持、单批原子发行 | S0、语义数据 | 全部已验证结果 |
| K1 复合证明 | 局部回执、有限作用域导出、覆盖/情形合并、跨存储发布协调 | K0、实际复合操作 | 参数分类、手动推导、长任务 |
| A0 系数结构 | Z、Q、素域及有限扩张、特征和显式映射 | 精确算术、结构证明 | 多项式、模算法、线性代数 |
| A1 多项式与分式 | 多元/递归多项式、单项式序、精确/带余/伪除法、gcd/xgcd、平方自由、分式域 | A0、结构所需能力 | G、R、D、I 全分支 |
| A2 模计算与分解 | CRT、有理重构、有限域分解、Hensel、Z/Q 一元及多元 gcd/因式分解 | A1、有限域、必要线性代数 | 数域、积分、投影及性能优化 |
| A3 代数常数扩张 | 商代数、不可约商域、基与坐标、迹/范数、嵌入、扩张域因式分解 | A1、A2 的基域不可约性算法 | 实/复代数数、I、G、O |
| A4 线性与模 | 域上秩/仿射解/零空间、分式自由消元、Z 上 Hermite/Smith | A0/A1 的相应能力 | PRDE、解集、数域、离散线性问题 |
| P0 参数结构 | 任意已准入基结构的参数环/泛点域、局部化、特化和异常集 | A1、S1 | 所有带参数算法 |
| P1 参数关系与分类 | 关系理想、商/局部化、综合 Gröbner/正规链、实参数条件分类 | P0、G0/G1；实分类另用 C1 | 全参数求解与特化覆盖 |
| G0 Gröbner | Buchberger、约化基、多元正规形、属员和消元 | A1、有效系数域 | G1/G2、P1、代数预处理 |
| G1 理想与商代数 | 消元理想、饱和、交、商空间及零维乘法矩阵、所选分解表示 | G0、A4；部分分解用 A2/A3 | 系统求解、参数关系、代数分析 |
| G2 多项式方程组 | 零维三角/RUR 类表示、代数根选择、重数与覆盖；正维精确代数集合/正规链表示 | G1、A3；实解另用 R/C | solve、参数分类、代数预处理 |
| R0 一元根 | 根界、平方自由、Sturm/子结式计数、重数、端点与隔离 | A1、有序有效系数能力 | R1、分段、CAD |
| R1 实代数数 | 精确算术、跨表示判等/排序、多项式取号、根编码与选根 | R0、A3 所需部分 | C0、分段、实解及定积分 |
| C0 CAD 几何 | 三角实代数样本点、完整投影/lifting、section/sector、零化/降次、全空间覆盖 | R1、A1/A2 中投影所需部分 | C1、区域与参数服务 |
| C1 CAD/QE | 量词真值传播、无量词解公式、投影/包含/空性等半代数服务 | C0、S0 的逻辑与绑定 | 实方程/不等式、P1、区域分析 |
| D0 微分代数 | 显式导子、关系稳定性、常数结构、形式微分多项式 | A1/A3、S1 | 求导、I、O |
| D1 微分塔准入 | primitive/exponential/代数扩张、生成元关系、有效常数能力、表达式往返 | D0、相应代数算法、低层结构判定 | Risch、微分方程 |
| I0 基例积分 | 多项式积分、有理 Hermite、留数与对数部分、精确结果表示 | A1；对数/代数留数部分用 A2/A3 | I1、手动积分、定积分 |
| I1 Risch 超越主线 | 分裂/微分 Hermite、留数、有限次数界、RDE/PRDE、受限积分与非初等障碍 | I0、D1、A4、有效常数子算法 | 完整已准入超越塔上的初等判定 |
| I2 代数函数分支 | 函数域、整基、局部展开/赋值、除子、Riemann–Roch 及所需类群/挠性判定、代数 Hermite/对数部分 | A1–A4、D0、G/R 中所需设施 | 代数及混合 Risch 扩展 |
| F0 区域与分段 | 精确支集、首中互斥化、公共细分、边界/连通分支、逐点与区域运算 | S1；半代数判定用 R0/R1/C1 | 分段求导/积分、解集 |
| F1 微积分解释 | 经典/单侧/几乎处处区分、连接点验证、全部原函数、定积分/反常积分/主值及收敛证据 | F0、D/I、相应局部代数 | 用户微积分操作 |
| O0 线性 ODE | 有理/多项式解、常系数基本解系、一阶线性、二阶 Kovacic、正规点级数/算子表示 | A3/A4、D0；各子类按需用 I/D1 | 微分方程求解 |
| O1 可判定扩展 | 所选更高阶线性/Liouvillian 子类、精确微分算子与受限 PDE 的代数兼容性分析 | O0、Ore/模算法及各子类的定理前提 | 后续微分方程能力 |
| U0 手动工作簿 | 对象/问题/候选、声明/定义、表达式引用、编辑/check、焦点/路径、undo/redo | S0/S1/K0 | 所有手动动作 |
| U1 完整交互与策略 | 依据等式改写、换元/分部积分、任务 DAG、构造超图、情形/研究分支、建议与解释 | U0/K1、实际数学操作 | 完整手动/自动协作 |
| E0 工程终态 | 版本化持久化、数据/验证/搜索重放、有界缓存、预算/取消、并发快照与原子发布 | 各层稳定契约、U/K | 长计算与可恢复工作簿 |

主干关系如下；同一行的分支不构成彼此前置，表中的额外依赖仍须满足：

```text
S0 ── S1 ── 数学请求/域桥 ──────────────────────────────┐
 │     │                                               │
 └── K0 ── K1 ── 可信规格/条件/覆盖 ────────────────────┤
                                                       │
A0 → A1 ┬→ A2 → A3 ───────────→ 数域/实复代数常数       │
        ├→ A4 ───────────────→ 线性代数/模              │
        ├→ G0 → G1 → G2 ─────→ 方程组                   │
        ├→ R0 → R1 → C0 → C1 → 完整 CAD/QE             │
        └→ D0 → D1 + I0 → I1 → 完整已准入超越 Risch    │
                     └──── I2 → 代数/混合扩展           │
P0 + G/C → P1 ────────────────→ 全参数分类               │
R/C + D/I → F0/F1 ────────────→ 分段/定积分              │
A/D/I + Ore → O0/O1 ──────────→ 微分方程                 │
                                                       │
U0 → U1 + E0 ←────── 所有数学分支的操作、证书与解释 ─────┘
```

### 30.9 公共代数的施工与出口

**A1 先解决表示，不先做表达式化简器。** 明确系数 parent、生成元顺序、单项式序、主变量视图；递归表示与平坦表示经指定同构转换。多元判等逐系数完成，归约由明确的除法或 Gröbner 契约承担。

1. 有效域上一元 `divmod` 满足 f=qg+r 且 r=0 或 deg(r)<deg(g)。
2. `extended_gcd` 输出 d,s,t，验证 sf+tg=d，并检查 d 的规范单位及公因子性质。
3. 非域系数上的 `pseudo_divmod` 同时输出乘子的幂或显式系数，验证 c*f=q*g+r；不能把 q 叫作域上的商。
4. 平方自由分解验证单位、重数、乘回和互素性。正特征的 Frobenius/不可分情形是算法的一部分，不通过默认零导子混过去。
5. 分式可先交叉乘法精确判等，再实现带 gcd 的约分与内容归一。原函数的孔洞只在桥上保留，不能塞进每次分式乘法。
6. 结式、子结式链、判别式分别暴露数学含义，记录所选主变量。非域系数不得偷偷求逆。

**A2 区分算法前提与优化。** 有限域分解、CRT、重构、Hensel 与 Z/Q 分解形成可独立使用的工具。固定次数/高度界和精确乘回是终止/正确性的一部分；随机挑素数不充当不可约性证明。基准算法与优化共用表示及结果契约，不能仅实现概率性启发式却声明完整。

**A3 不制造循环依赖。** 先在已有效的基域上证明 p 不可约，再构造 K[t]/(p)。在新数域上的因式分解是随后建立的能力，不把它作为构造该数域所需的同一个未实现 oracle。一般商代数保留零因子语义；简单域扩张、复嵌入、实嵌入、原始元转换和数值选根是不同构造条件。

**A4 一次分解供多项消费者。** 特解、核、秩、行列式等复用消元结果；输出行变换/秩或模结构见证。Z 上 Smith/Hermite 不经过把非单位随意变成可逆元的假域。

### 30.10 参数与系数正交的完整路线

P0 必须对结构参数 K 工作，而非建立 Q 专用的参数实现。依次实现 K[A]、在条件允许时的 Frac(K[A])、局部化及映射；每条操作固定目标 X、参数 A、所选导子与目标取值空间。

验收矩阵至少覆盖 Q[A][X]、有限代数扩张 K[A][X]、K(A)[X]、K(A)(x)，并测试同一符号在不同请求中交换参数/目标角色。正特征参数扩张可以进入相应代数算法，但不能自动取得特征零积分能力。

P1 的次序为：

1. 关系理想 I 与商/局部化表示，核验转换是否保持关系；
2. 泛参数运算的非零、次数、秩、判别式等特化见证；
3. 有限参数分支算法，先线性系统，再综合 Gröbner/正规链所声明的类；
4. 实参数分类把等式/不等式交给 C1，合并时证明覆盖和结果性质；
5. 特化到有理点、代数点及已有有效嵌入，分别验证映射有效性；
6. 支持部分特化和剩余参数时，结果重新成为较小参数空间上的问题，而不是丢掉未赋值参数。

全参数覆盖、每支结果完备、每支非空是不同承诺。一般有理参数代数集合的非空性不能用实 CAD 代替；允许用精确条件描述分类时，也不能把它显示为已经决定每支存在有理点。泛点结论对未知超越常数关系不自动有效。

参数化算术与任意参数分类也不能混淆。例如 x^a 在正实解释下可写为 exp(a*log(x))，而 a=n/m 的特化会给生成元引入 t^m=x^n 的关系；这不是仅检查有限个最终分母就能覆盖的结构变化。涉及无限离散条件的结果须有相应结果语言和可判定子类，不能一律化成有限半代数分类。完整设计保留这种条件表达与分类接口，但每个“全参数”算法须给出其准确终止/覆盖契约。

### 30.11 Gröbner 与方程组的完整路线

G0 从有效域上的通用多元除法和 Buchberger 开始，给出基、双向生成表示及 S-多项式归约见证。约化基与单项式序固定后提供确定的理想正规形。随后增加判据、sugar、模算法、F4/F5 等优化，但不换数学契约。

G1 建立消元、理想交、饱和与商代数。零维时建立标准单项式基和乘法矩阵，提供维数/有限性依据，再做变序、三角化或 RUR。基不是 Gröbner 时的余式不能冒充理想正规形。

G2 分开四条解语义：

- 代数闭包中的零维几何点与代数重数；
- 实点筛选和完整实解描述；
- 正维代数集合/正规链分解，包含各分量、排除条件和覆盖；
- 对已知零维有理系数系统筛选有理/整数点，而不扩张为一般正维有理点决定过程。

消分母先保留非零条件或使用饱和；平方、消元与投影后回代复核原系统，不能仅检查中间系统。结果是否满足“显式解”取决于请求接受有限点、RootOf、三角系统、参数化族还是代数集合。无根式表达不等于未求解，重述输入也不等于已完成分解。

### 30.12 实代数与完整 CAD/QE 路线

R0 首先提供根界、平方自由、Sturm/子结式计数和可复核隔离。不必为隔离先完整因式分解；根的选取与随后需要不可约商域的条件分开。
R1 提供实代数数的精确表示、算术、跨多项式选根判等和排序；区间是根计数支持的表示见证，不是浮点近似答案。

C0/C1 必须贯通下列全部环节，不能在“已能分解一些胞腔”处收工：

1. 公式定型、偏运算消除条件、量词/自由变量与投影序；
2. 内容和本原部分、平方自由/互素投影基；
3. 完整基准投影及其系数、reducta、子结式等前提；
4. 低维胞腔上的恒零、降次与 nullification 处理；
5. 三角代数样本点上的取号、根计数、section/sector 提升；
6. 全空间覆盖、柱状性以及足以支撑公式真值的区域不变性；
7. 按原量词顺序进行真值传播；
8. 构造满足请求语言的无量词公式，不泄漏内部胞腔编号；
9. 投影、空性、包含、等价、连通信息中已具备定理与实现的区域服务；
10. 增加局部/部分 CAD、约束优化、小投影及变量顺序优化，条件失败时保持基准正确性。

双指数最坏复杂度是真实数学成本，不能通过放弃覆盖伪装优化。Buchberger 不是保守基准 CAD 的必需前置；若某个投影/公式优化消费 Gröbner，则只为那条优化增加依赖。

### 30.13 微分塔与完整 Risch 路线

D0 先把 D:K→K 与基域相等分开。D1 逐层准入 K(t)，记录生成元关系、导数、常数结构和原表达式映射；不能按所有自由符号创建一个“显然独立”的塔。

完整超越主线分为：

1. I0 多项式原函数、Q(x) 与有效常数域上的有理 Hermite；
2. 留数多项式、代数常数、对数项与精确 RootSum 类结果；
3. normal/special 分裂及分裂平方自由，微分 Hermite；
4. 对数导数/导数识别、常数线性相关与受限积分；
5. RDE 的一般分母、特殊分母、次数界、系数递降；
6. PRDE 的常数未知量、解空间与残余常数线性系统；
7. primitive/exponential 各层归约与向低层递降；
8. 总分解与正/负结论证据，限定有效常数域和允许的初等扩张；
9. 声明函数到塔的结构转换与实/复分支回译；
10. P0/P1 下的特化有效性、退化塔与可完成参数子类的全覆盖。

这里存在数学上的相互调用，但不能存在未定义的循环 oracle。塔高降低的子问题可以调用已完成低层算法；同层 RDE/PRDE 使用已证明的次数/极点界终止。实现前列明递归所依赖的良基量和每个基例；不能在准入一层时先假设该层完整积分器已正确。

I2 的代数函数分支完整保留：曲线/函数域表示 → 可分扩张与导子 → 整基及局部化 → 赋值、Laurent/Puiseux 局部数据 → 除子/Riemann–Roch 所需运算 → 留数与对数部分的类群/挠性等判定 → 代数 Hermite/积分 → 混合塔。每种基域和曲线类分别核对其算术判定前提；没有有效算法的具体环节记为研究阻塞，不伪造通用 oracle。

该分支不是近期必须一次完成的条件，但它的依赖和目标不可从总体图里删除。反之，整基、亏格或除子算法不是 Q(x) 有理积分与全部纯超越塔的无条件前置。

### 30.14 分段、端点与积分解释路线

F0 从一维有理/代数端点和半代数支集扩展到 C1 支持的区域。保留有序首中，构造公共细分、实际支集、边界、孤立点与连通分支。

F1 的出口不止逐支公式：必须分别处理定义域保持、连接点极限/连续性/差商、经典与单侧导数、积分常数拼接、普通与反常积分的端点/极点，以及主值的独立规格。

精确局部代数（消失阶、局部展开、代数根取号）可以决定所支持分支的边界性质。有限截断只证明截断精度，不单独证明任意函数的全局相等或收敛。

超越端点不从表达语言中删除。存在唯一性证明可以产生指定根描述，有限端点之间的已验证顺序可以支持该有限划分；这不赋予一个任意超越数域以总排序能力。后续每项算术/边界操作分别消费其实际所需证据，未覆盖的请求诚实停下，不能偷偷改成代数端点。

### 30.15 ODE、PDE 与相邻精确能力路线

ODE 不以“支持求导”冒充“能求解”，也不把整个方向缩成一句未来研究。按已知算法分别实施：

1. 微分算子/Ore 表示、组合、作用与所需左右除法；
2. 常系数线性方程的特征多项式、重根、基本解系与初值；
3. Q(x) 等已声明系数域上、给定阶数的线性方程有理/多项式解算法及其次数/分母界；
4. 一阶线性方程，区分初等闭式、积分表示、隐式关系与算子/初值表示；
5. 二阶有理系数 Kovacic/Liouvillian 判定及其常数/代数扩张前提；
6. 正规点的精确递推系数/截断级数、残差与初值核验；
7. 更高阶线性微分算子分解和选定 Liouvillian 子类，逐项写明有效微分 Galois/常数域前提；
8. 每条路线补全正则区域、独立性、解空间覆盖和奇点/初值分支。

一般非线性 ODE 没有一个可任意套用的完整算法；可分离、Riccati 可归约情形等分别以明确子类和变换定理立项。找不到变换不是不可解。
PDE 保留多导子与交换条件、微分算子模以及常系数线性兼容性/消元等可判定代数任务；不把这些任务的成功冒充任意函数空间、区域和边界条件下的全部 PDE 解。

相邻能力仍进入全景：精确截断级数、代数级数、有限表示的生成函数、选定 D-finite/递推表示、整数线性系统与 Presburger 类约束、单变量整数根。它们分别复用 A/G/D/O，不开第二套上下文和证明账本。任意惰性无限级数没有一般零等价，不自动注册为有效域；一般丢番图与一般有理点问题仍遵守理论边界。

### 30.16 手动、自动与工程终态路线

U0 先贯通对象、问题、候选、假设/定义与核验。U1 随数学能力接入但最终必须覆盖：

- 版本固定的表达式引用、子项选择、绑定体编辑与可见性；
- 句法编辑、依据等式改写、全称实例化、特化、坐标换元这五种不同动作；
- 方程变换的推论方向、积分分部/换元、局部变量和函数对象；
- 子任务执行 DAG 与允许联立的构造关系超图；
- 研究分支的 revision DAG 与数学情形覆盖/合并；
- 自动策略建议、预算、复用、取消以及真实来源的折叠解释；
- 条件解析/清偿和未覆盖范围的用户可见状态。

E0 最终覆盖版本化序列化、语义/信任快照、数据与验证重放、搜索重放、有界派生缓存、历史归档、并发只读计算和单写原子发布。内部算法轨迹可裁剪，活跃结果的证明支持不可丢失。

日志多少不改变数学结果。一次自动积分可以只有一个用户事件，内部构造证书；用户主动标为可信的每个手动变换是独立承诺。允许连续编辑中性候选再最终核验，不要求每次编辑成为证明。

### 30.17 实施波次与并行关系

默认波次只表达拓扑顺序，不替代各节点契约：

| 波次 | 必须形成的可验收产物 | 同时为哪些终态目标铺路 |
|---|---|---|
| W0 解释与类型闭合 | 修复现有请求/区域/幂/作用域边界，封闭结果；S0/S1/K0 的真实纵线 | 所有分支，而非仅求导 |
| W1 代数公共核心 | A1 所需除法/gcd/xgcd/分式，A4 基础，P0 初版 | 积分、Gröbner、参数线性；同步 U0 |
| W2 三条数学基线 | I0 有理积分链、G0 Buchberger、R0/R1 实代数链，各自按依赖交付 | Risch、方程组、CAD；按需补 A2/A3 |
| W3 结构与区域 | G1/G2、C0/C1、D0/D1、F0/F1 的对应子阶段 | 完整实求解、分段、微分塔；同步 K1/U1 |
| W4 里程碑闭合 | I1 的完整已准入塔判定、完整 CAD/QE 输出、P1 全参数子类、O0 各确定片段 | 不止示例，覆盖完整契约及负面结论 |
| W5 扩展与规模 | I2、O1、更多系数/参数类、高级策略、持久化/重放/并发性能 | 在明确理论前提下继续扩完整系统 |

W2 不是“先做完三个分支才允许任意分支前进”，各支可沿已有依赖进入 W3。S1/K0 的正确性约束不能跳过，U1/E0 的全部终态功能却不是 A1/I0/G0/R0 的共同前置。

禁止三种伪依赖：为有理积分先建全套代数几何；为 Buchberger 先建 CAD；为一个用户级核验先建完整异步工作流。也禁止反向缩目标：交付第一个有理积分后，仍必须沿图走向塔、PRDE、非初等性、参数及全交互，而不是宣布小系统足够。

### 30.18 每个节点的完成定义

节点完成至少交付：

1. 明确输入表示、基结构能力、变量/参数角色与结果语言；
2. 数学算法、终止依据、正面结论及所承诺的负面/完备性边界；
3. 精确结果与独立核验所需证书或列明的可信验证算法；
4. 参数/定义域/分支条件，以及原请求未覆盖部分；
5. 注册操作和真实消费路径，若是公共工具则有上层消费者或公开低层 API；
6. 正向、反向/边界、篡改证书、预算及固定种子性质测试；
7. 实际状态与后继节点解锁记录。

“有类名”“有协议”“找到一个例子”“只有正确性没有覆盖”都不满足更强节点的出口。未解决理论前提单独列出，不从目标图隐藏，也不包装成已完成接口。

---

## §31 不变量与验收矩阵

### 31.1 结构与绑定不变量

| 编号 | 必须成立 |
|---|---|
| S1 | Term 不含上下文、guard、证明或工作流引用 |
| S2 | 参与结构相等与 hash 的字段创建后不可修改 |
| S3 | 结构相等推出 hash 相同；hash 相同不直接推出相等 |
| S4 | 缓存清空、重新构造与不同分配顺序不改变结构语义 |
| S5 | 自由符号按 SymbolId，不按显示名识别 |
| S6 | 所有 binder 操作捕获规避且无越界索引 |
| S7 | operator 位置的自由函数符号参与作用域检查 |
| S8 | 未经类型确认不执行依赖交换性、零吸收或定义性的化简 |

### 31.2 域与数学不变量

| 编号 | 必须成立 |
|---|---|
| A1 | 有效域成员的判等与判零完整且不返回 Unknown |
| A2 | 不支持转换不被压成“非零”或“不相等” |
| A3 | parent、系数结构、变量顺序和嵌入匹配 |
| A4 | 形式非零不被解释成所有特化下非零 |
| A5 | 所有特化保存定义域和算法有效条件 |
| A6 | 未知导子不默认为零导子 |
| A7 | 商结构取得 field 能力有真实依据 |
| A8 | 定义域、函数值相等与域元素相等分别验证 |
| A9 | 分段边界覆盖不能由逐支计算代替 |
| A10 | NoSolutions 与 NonElementary 不来自搜索失败或预算耗尽 |

### 31.3 可信内核不变量

| 编号 | 必须成立 |
|---|---|
| K1 | Judgment 只由可信 commit 发行 |
| K2 | 裸表达式、Artifact 和 Candidate 不成为可信命题或前提 |
| K3 | checker 实际验证的规格与提交规格完全对应 |
| K4 | 假设证明只存在于已经包含该假设的合法 frame |
| K5 | 前提可见，兄弟分支不自动互通 |
| K6 | 直接、继承、定义性及特化条件统一处理 |
| K7 | 未决条件不自动加入假设 |
| K8 | 清偿证明闭合且不存在自我支持循环 |
| K9 | 分支合并引用真实分支证明并正确导出条件 |
| K10 | 局部符号不逃逸，任意变量与存在见证不混淆 |
| K11 | 日志模式不改变判定、条件或适用性语义 |
| K12 | 发布原子，失败不留下半个可信状态 |
| K13 | 已发行判断不可覆写，历史裁剪不破坏活跃证明 |
| K14 | InvalidEvidence、Refuted、Blocked 和 Unknown 含义不同 |

### 31.4 工作流不变量

| 编号 | 必须成立 |
|---|---|
| W1 | 表达式可直接计算，不需先被 Claim 为真 |
| W2 | 公式、假设、问题和构造约束分别表示 |
| W3 | 候选正确性、适用性和完备性独立记录 |
| W4 | 用户操作绑定输入对象版本与语义快照 |
| W5 | 执行依赖无环，联立构造关系允许环 |
| W6 | undo/redo 恢复确切 revision，不重新解释旧对象 |
| W7 | 研究分支合并不自动产生数学结论 |
| W8 | 任务完成按原 frame、覆盖和结果语言判断，不因进入更强分支而完成 |
| W9 | 程序异常不伪装成数学未决或否定 |
| W10 | 显示器不创造条件、积分常数或完整性承诺 |

### 31.5 行为验收案例

至少覆盖：

- 故意制造 hash 碰撞，两个不同整数仍不相等。
- 修改不可变符号字段被拒绝，或不可能经公共 API 改变语义。
- 向 binder 内插入同显示名自由符号不被捕获。
- x:Complex 不进入无依据的有序域平方非负判定。
- 不可投影的 u 不被伪域判为 `u≠u`。
- Claim/assume 不在空 frame 创造任意定理。
- `x=1` 的句法替换不能提交 `2=1`。
- `x²=1` 的一个根不变成原方程推出 x=1。
- 无分支证明的合并载荷被拒绝。
- 导出分支时完整保留定义性假设包，守卫之外不提前求值偏函数。
- 参数 a=0 使泛参数公式失效时，回到原问题而不是直接代入。
- 进入 a≠0 子 frame 不使原全参数任务变为 Completed 或 CompletedConditional。
- 分段跳跃候选不通过全域原函数验证。
- 非零常数的胞腔判号不进入除零 Sturm 步骤。
- 所有模式下条件状态一致。
- 中断发布、取消搜索和持久化失败不留下半提交状态。
- 编辑定义、切换分支与 undo 不改变旧对象的意义。

### 31.6 验收方法

正确性验收分三类，与 AGENTS.md 一致：

1. 严格类型检查：封闭结果、域元素关联、载荷、ID 和前提类型；不声称证明数学。
2. 行为测试：确定性边界、绑定、条件、分支、定义域，以及 §21 从输入到结果与撤销的端到端案例。
3. 固定种子性质测试：域公理、表示往返、算法证书、特化有效区域和不变量。

依赖和写权限由构造边界、明确 owner、代码审查及真实行为测试检查，不以名字/字符串/import 面或 AST 扫描冒充设计正确性。lint/compileall 是辅助工程检查，性能按 §27 独立 profile。

随机数值抽样可以发现错误，不能独立证明一般恒等式。参考实现可以辅助差分发现，但其输出不直接成为可信真值。

本文规定未来实现应接受的验收；编写本文本身不代表这些验收已经运行或通过。

---

## §32 最终接口闭合表、类型载荷与全程数据流

### 32.1 从输入到可信结果

| 阶段 | 输入 | 输出 | 不得越过的边界 |
|---|---|---|---|
| 解析 | 文本与表面语法 | Surface AST | 不猜数学真值 |
| 名字与绑定整理 | AST、frame | resolved Term | 不按同名字符串合并身份 |
| 语义整理 | Term、声明与解释 | TypedExpr/Proposition | 不把可解析当成可计算 |
| 问题构造 | 数学对象与用户意图 | ProblemSpec | 不把待解方程变成假设 |
| 域桥接 | TypedExpr、AlgebraRequest | AlgebraView 或拒绝 | 不伪造有效域成员 |
| 搜索 | 问题、域表示、预算 | 候选、子问题、证书 | 不发行 Judgment |
| 校验 | 规格、候选、证书、frame | CheckOutcome | 不偷换规格与覆盖 |
| 提交 | 已验证提案与条件 | Judgment/InferenceRecord | 不丢条件、不跨作用域 |
| 工作流发布 | 结果与可信 batch | 对象、事件、revision | 不半提交、不重解释旧对象 |
| 显示 | 真实对象和验证状态 | 用户可读结果 | 不把局部或条件结果说成完整 |

### 32.2 各层唯一写职责

- 语义上下文扩展入口创建经过检查的声明、定义和假设 frame。
- 内核 commit 发行可信数学记录。
- 工作流 application 创建对象关联、任务状态事件和 revision。
- 事务协调器只原子发布各自拥有权限的批次，不拥有修改数学结论的权力。
- 数学算法、checker、格式化器和缓存均无直接账本写权限。

### 32.3 最终设计判断

pyCAS v5 不是“表达式等式链外面加证明壳”，也不是“每次数学运算都展开成 HOL 证明”。

它是：

```text
明确的数学对象与问题
    + 有效的代数结构
    + 正确的变量、绑定与上下文
    + 不可信但灵活的候选和策略
    + 针对确切规格的可信校验
    + 可理解的对象化交互与历史
```

正确性由语义与验证边界保证；效率由表示、算法、共享和粗粒度提交保证；灵活性由开放操作、任务组合、条件分支和局部上下文保证。

任何未来功能都必须能放进这条链，而不是再引入一个绕过它的专用全局状态、伪域或特殊工作流。

### 32.4 终态类型载荷及唯一 owner

本表细化已有对象，不引入另一套平行 API。字段是目标契约，只有随消费者实现时才创建代码；当前源码名字不等于已满足此契约。

| 数据 | 必须固定的载荷 | owner / 真实消费者 |
|---|---|---|
| TypedExpr | resolved Term、sort、MeaningKey、绑定视图 | 数据归 language/typing，semantics/elaborate 发行；问题、桥和工作簿消费 |
| VariableRoles | 目标/参数 SymbolId、绑定位置和语言层角色约定 | language/problems；问题与代数请求共享同一不可变值 |
| ProblemSpec | 操作类别、固定输入、VariableRoles、语言层域/解释要求、请求区域、结果语言、覆盖要求 | language/problems；操作和 checker 消费，不导入具体 Parent |
| AlgebraRequest | 同一 VariableRoles、已解析基系数 parent、参数结构及关系、导子/嵌入、解释视图 | semantics/request；桥和算法准入消费 |
| ExecutionRequest | ProblemSpec、与之匹配的 AlgebraRequest、frame、执行预算和条件策略 | operations/protocols；一次构造后供提案与核验共同消费 |
| AlgebraView[E] | source TypedExpr、Parent[E]、value:E、生成元映射、`ConversionWitness`、源定义域、表示有效区域 | semantics 的桥；数学操作与 checker 消费 |
| RegionSpec | 坐标/绑定、条件 Proposition、意义环境 | semantics；区域算法/函数视图消费 |
| Definedness | 源对象及其定义域描述、已证精确性或仅充分区域的证据 | semantics 定义性服务；转换/微积分 checker 消费 |
| MathematicalProposal | 原 ProblemSpec 引用、结果数据、所求核验规格、证书、达到区域/残余区域、必要条件、局部计划/解释 | operations 契约、math 构造；workflow/验证器消费 |
| CheckRequest | 固定问题、候选数学数据、所请求规格、内核解析的可见前提、可信上下文、结构化组件与证书 | kernel 构造；绑定的数学 checker 消费 |
| CheckOutcome | Verified / Refuted / Unverified / InvalidEvidence 的具体联合载荷 | kernel/evidence；提交与状态投影消费 |
| ValidatedCommitBatch | 已核验规格、实际支持、义务/清偿、局部回执解析结果和版本快照 | kernel 私有构造；发布协调器只读消费；seal 不是 init 字段，`dataclasses.replace` 不能伪造 |
| ObjectVersion | 中性表达式值或 FunctionValue、版本、来源事件；显式函数保留其固有域 | workflow；后续操作和显示消费 |
| Candidate/VerificationLink | 原问题、候选版本、提出时的 `AlgebraRequest` 快照、确切规格、核验结果/判断引用、作用域 | workflow；完成性、适用性与手动复核消费 |
| Event/Revision | 固定输入输出/作用域/参数、实际执行结果与父 revision，对象/任务/核验关联可见集 | workflow；历史、恢复与显示消费 |

角色只允许一处权威设定：请求构造器先固定 language 拥有的 VariableRoles，ProblemSpec 与 AlgebraRequest 共享它；禁止操作、运行时和 checker 各自设置可能不同的 target/parameter_mode。语言层只保存域/解释要求，不反向导入 semantics 的 AlgebraRequest 或 algebra 的 Parent；operations 中的 ExecutionRequest 验证并绑定已解析结构与原要求。
完整数学查询键包含 ProblemSpec、AlgebraRequest 和必要意义快照，不能只按表达式或 operation id 缓存。预算属于执行尝试，不改变数学问题身份。请求全域答案时不能把收到的局部结果写回 ProblemSpec.region；候选记录保留原 ProblemSpec，实际达到区域属于验证关联。

参数族结果、对象和验证关联都属于 revision 快照：undo 之后不能继续使用只在未来 revision 中可见的家族，redo 恢复同一快照。工作区输入句柄必须校验所属 workspace、存在性和当前可见性；版本号相同不足以证明是同一对象。

Definedness 中“精确原定义域”和“已证明可工作的子区域”必须分清。SamePartialFunction 需要两边完整定义域等价；只有充分区域证据时最多证明 EqualOn，不得把保守区域误当精确域。源全定义时表示仍可能只在充分子区域有效；该情形是 `SUFFICIENT`，不是 `EXACT`，其证据是桥的转换 witness 而不是伪造的完整域。

实现切片（2026-11-09）：`RegionSpec` 已固定有序坐标与条件 `Proposition`；`RegionCertificate` 已以 `NonemptyCertificate`/`SubregionCertificate`/`CoversCertificate` 三种封闭变体落地，并由 `certify_*`/`verify_region_certificate` 在受限条件片段上发行/重检。`Definedness` 已改为 `DefinednessExactness`（`TOTAL`/`EXACT`/`SUFFICIENT`）+ `RegionSpec` + 可选 `RegionCertificate`，由 `AlgebraView.definedness` 单一派生；`EXACT` 的证据仍是桥的 `ConversionWitness`；`SUFFICIENT` 覆盖两种情形：非平凡固有域上的严格子区域必须携带匹配的 `SubregionCertificate`，源全定义（`domain` 为 None）而表示只在充分子区域有效时由桥的 `ConversionWitness` 作证据、不携带区域证书。`Definedness` 的区域坐标必须包含源的全部自由符号，允许额外坐标并保留区域自身顺序；`AlgebraView` 发行时要求每个区域与源同 world，两个区域同时存在时共享同一 `MeaningKey`，`valid_on` 不再要求 `source_domain` 存在。声明函数定义域、`Guarded`/`Piecewise` 分支局部语义、binder-aware premises、一般偏函数定义域、`ProblemSpec`/`FunctionValue` 的 `RegionSpec` 迁移与结果语言覆盖仍未建；`GenericResult.valid_on`/`excluded_cases` 的 `RegionSpec` 迁移已在本批闭合，`region_from_proposition` 提供确定坐标桥并由 workspace/`specialize` 消费；`Proposition` 的结构定义性前提由后续切片记录，其消费边界见下两段。

实现切片（2026-11-09，Proposition 结构定义性前提）：`Proposition` 已增加 `definedness` 字段并由 `propositions.check` 收集结构前提；`RegionSpec` 的证书消费 `conditions.premises_proved`/`regions.premises_proved_from`/`proved_subregion`，`AlgebraView` 发行/`definedness` 与 `DefinednessService.covers` 同样拒绝未证明前提。该切片只覆盖非正指数整数幂的 `Ne(base,0)` 与和/积/比较/布尔连接词的结构递归；声明函数定义域、`Guarded`/`Piecewise` 分支局部语义、binder-aware premises、一般偏函数定义域、`ProblemSpec`/`FunctionValue` 的区域迁移与结果语言覆盖仍未建，不能把本切片写成完整 Proposition definedness 或 Guarded 支持。

实现切片（2026-11-09，定义性前提的消费者修正）：`specialize` 对 `RegionSpec.condition` 递归求值定义性前提（假前提 → 点在外/排除情形不适用，未决前提 → `NeedsRecomputation`）；`FunctionEqualityChecker`/`FunctionExtensionOperation`/workspace 函数区域检查改用 `proved_subregion`，`proved_subregion` 增加仅供已校验可见性的调用方使用的 `same_meaning=False`；`ProblemSpec.region`、`OperationRequest.region`、`FunctionValue`/`FunctionRepresentation` 区域与 `MathematicalProposal` 区域等仍按 term 消费的裸 Proposition 载荷在构造器拒绝非空 `definedness`。`ProblemSpec`/`FunctionValue` 的 `RegionSpec` 迁移、声明函数定义域、`Guarded`/`Piecewise`、binder-aware premises、一般偏函数定义域与结果语言覆盖仍未建。

实现切片（2026-11-09，请求局部导子载荷）：`AlgebraRequest` 已增加可选 `differential`，缺省 `None` 表示无导子假设，存在时必须为 `DifferentialStructure`；请求是唯一导子权威，`DifferentiationView`/`SpecializationView` 要求视图导子与请求导子为同一对象。`bootstrap`/`bootstrap_parameterized`/`bootstrap_elementary` 已把既有 Q[x]、`K[parameters][target]`、特化 Q[x] 与初等导子写入对应请求。嵌入、参数关系、实嵌入、`VariableRoles` 绑定位置与 binder-aware 角色（目标/参数排序已闭合）与 `DifferentialStructure` 的持久化/重放载荷仍未建。

实现切片（2026-11-09，定义性保留 witness）：`AlgebraView` 的区域载荷与 `ConversionWitness.preserves_definedness` 在发行与准入边界一致。携带 `source_domain`/`valid_on` 的视图必须由保留定义性的 witness 支撑；`AlgebraView.__post_init__` 与 `_issue_view` 在发行时拒绝不保留定义性的区域视图，`_admit_view_relation`/`typed_view` 在准入边界再次检查并以 `ViewRefused(missing={"conversion_witness"})` 拒绝。全定义视图不作出定义性声明，非保定义同态仍按单射/保等号规则传递等式。多项式桥、参数多项式桥与有理桥继续发行 `preserves_definedness=True` 的表示同构。嵌入/同态的具体实现、混域消解与 `AlgebraRequest` 嵌入字段仍未建。

实现切片（2026-11-09，解释与 witness 一致性）：`AlgebraView` 的 `interpretation` 与 `ConversionWitness.kind` 不能互相矛盾，由 `semantics.bridge._interpretation_witness_refusal` 单一判定并在 `AlgebraView.__post_init__`/`_issue_view` 消费：`EMBEDDED` 只接受 `EMBEDDING`/`REPRESENTATION_ISOMORPHISM`，`PARAMETER_FAMILY` 只接受 `REPRESENTATION_ISOMORPHISM`，`FORMAL` 接受三种 kind 并由 witness 标志约束可传递事实。`_issue_view` 在建造前以 `ViewRefused(Reason.FRAGMENT, missing={"interpretation_witness"})` 拒绝，直接构造边界抛 `ValueError`。该规则不替代区域/定义性保留检查，也不构成嵌入/同态桥、混域消解或请求嵌入字段的实现。

实现切片（2026-11-09，区域载荷绑定与 sealed Definedness）：`RegionSpec` 的载荷现为有序坐标、条件 `Proposition` 与 binding `sorts`；`sorts` 非空时必须恰好覆盖坐标，`is_dense` 只在全部坐标为 `RATIONAL`/`REAL` 时为真。区域证书只在所有参与区域稠密时发行/重检，整数、复数、未知或缺失排序区域不继承 `condition_satisfiable`/`is_empty_condition` 的稠密序推理。`AlgebraView` 的 sealed `region_bindings` 是 `definedness` 构造 `RegionSpec` 的唯一坐标/排序来源，默认 source binding view，并可显式加入后代 frame 的额外坐标；未覆盖源或任一区域自由变量时 `_issue_view` 以 `missing={"region_bindings"}` 拒绝。`Definedness` 已 sealed，只由 `_issue_definedness`/`AlgebraView.definedness` 发行，`dataclasses.replace` 不能伪造；`EXACT` 与源全定义的 `SUFFICIENT` 仍以桥的 `ConversionWitness` 为证据。`function_region` 只为参数坐标记录排序，含非参数自由变量时省略整个 `sorts` 并因此拒绝覆盖证书。`ProblemSpec` 的精确域/解释、`VariableRoles` 目标/参数排序与 `externalizable` 正向路径已由后续切片闭合；完整绑定位置与 binder-aware 角色、跨 frame 前提弱化、注册 `Covers` 规格/checker、结果语言、嵌入字段与一般完备性仍未建，本切片不声称完整 S1。

实现切片（2026-11-09，函数问题绑定与世界作用域角色）：`ProblemSpec` 增加 `function_inputs`，函数问题固定 `FunctionValue` 的参数绑定、固有域与全部表示区域，并要求 `roles.target is None`、函数域/表示区域与类型化输入同 world。`VariableRoles` 增加 `world`，`ProblemSpec`/`AlgebraRequest` 拒绝未绑定 world 的角色集，并要求 `roles.world`、`region`、`externalizable` 与输入同 world。`SimplePolynomialBridge`/`ParameterPolynomialBridge`/`RationalFunctionBridge` 在 `to_view` 中以 `ViewRefused(missing={"request_world"})` 拒绝跨 world 请求。`FunctionEqualityChecker` 在 `problem_mismatch` 后绑定 `problem.function_inputs`（compare 两项、extension 旧函数一项），`EqualOn` 消费 problem-region ⊆ claim-region，`SamePartialFunction` 要求 problem region 位于两侧完整域内，并逐个检查表示区域是固有域的可证子区域；非稠密参数与非参数自由变量分别返回 `GUARDED`/`FRAGMENT`。该切片不声称完整 S1、一般函数定义域语义或 `ProblemSpec` 全部字段闭合。

实现切片（2026-11-10，请求契约全绑定）：`ProblemSpec` 的 `exactness`（仅 `EXACT`）与 `interpretation_requirement`、`VariableRoles.target_sort`/`parameter_sorts`、问题区域与 `externalizable` 前提的稠密排序校验已落地。`AlgebraRequest.interpretation_requirement` 是语言层解释要求的唯一映射；`ProblemBuilt`/`ExecutionRequest` 在 problem 与 algebra 之间强制该绑定，无 algebra 时必须为 `None`。`problem_mismatch` 增加 `roles`/`interpretation_requirement`/`exactness` 检查，数学 checker 传入固定 request 的 roles 与 interpretation；函数 checker 不传 roles/interpretation，保留 `function_inputs` 绑定。系数范围/值域字段与 `externalizable` 正向路径后由同日后续切片闭合；嵌入/实嵌入、参数关系、结果语言、完整绑定位置与 binder-aware 角色、注册 `Covers` 规格/checker 与一般完备性仍未建；本切片不声称完整 S1 或一般区域代数。

实现切片（2026-11-10，候选代数快照与上下文代数）：`Candidate` 增加 `algebra: AlgebraRequest | None`，非空时要求与 `ProblemSpec` 共享 `roles` 与 `target`，函数问题必须为 `None`；workspace 在 `_apply` 保存 `execution.algebra`，`edit_candidate` 清除证书时保留，`_candidate_proposal` 原样提交，因此手动复核不会切换到另一个预装配视图。`cas.kernel.evidence.context_algebra_mismatch` 是 Derivative/Elementary/Hermite/Linear/Gcd/Resultant checker 消费 `VerificationContext.algebra` 的唯一规则，按对象同一性比较；函数 checker 拒绝 algebra 快照，核心逻辑规则不要求 algebra。`validate_commit` 仍只从 `proposal.algebra` 构造上下文，缺失/不同由 checker 报 `InvalidEvidence`，不是 `Refuted`。跨 frame 前提弱化、注册 `Covers` 规格/checker、嵌入/实嵌入、结果语言、完整绑定位置与 binder-aware 角色仍未建；系数范围/值域字段与 `externalizable` 正向路径已由同日后续切片闭合，本切片不声称完整 S1。

实现切片（2026-11-10，ProblemSpec/AlgebraRequest 域绑定）：`ProblemSpec.domain_requirement`（`DomainRequirement`：语言层 coefficient range + allowed value domain）与 `AlgebraRequest.coefficient_domain`/`value_domain` 已绑定并由 `ProblemBuilt`/`ExecutionRequest` 强制一致；`AlgebraRequest.coefficient_domain` 是装配声明的数据（Q 为 `RATIONAL`，Z 测试为 `INTEGER`），`value_domain` 由 `roles.target_sort` 经 `value_domain_of_sort` 唯一派生。`problem_mismatch` 增加 coefficient/value domain 检查，固定请求 checker 传入自身请求值，函数 checker 传 `None`/`REAL`。`CoversCertificate` 仍是函数延拓内部证书，由 `FunctionEqualityChecker` 独立重检，没有独立 `Covers` judgment；注册 `Covers` 仍是未来 K1/S1 工作。嵌入/实嵌入、参数关系、结果语言覆盖、完整绑定位置与 binder-aware 角色、一般完备性仍未建；本切片不声称完整 S1。

实现切片（2026-11-10，固定问题比较与区域绑定排序）：`workspace._same_problem` 精确比较 `ProblemSpec.exactness`/`interpretation_requirement`/`domain_requirement`，`run_task` 以该唯一比较器拒绝重建出不同请求契约的执行；`AlgebraView.region_bindings` 对与源自由符号同 `SymbolId` 的条目要求排序等于源 `BindingView`，`semantics.bridge._region_binding_refusal` 在 `_issue_view` 与 sealed `__post_init__` 两处拒绝不一致绑定，避免非稠密源坐标被显式绑定伪装成稠密坐标。后代 frame 额外坐标仍由桥声明排序；本切片不替代一般区域代数、嵌入/同态实现或完整 S1。

### 32.5 静态类型怎样贯穿注册边界

低层算法使用 Ring[E]、Field[E]、Polynomial[E]、Matrix[E] 等精确类型；parent 与 E 成对传递，内部不沿用 Any。动态 parent 身份、维数和生成元数在构造/转换边界核验，静态类型不能代替它们。

开放 OperationSpec 对每个注册项绑定输入/参数/结果/证书的类型化适配器。序列化或注册查找处允许一次受控擦除；适配器验证载荷后立即进入具体类型方法。新增操作不能要求中央封闭参数联合列举所有数学操作的私有载荷。

相反，失败与状态本身是有限语义，必须使用显式联合、final 变体和穷尽处理。不存在一个空 CheckOutcome/CommitResult 基类就自动实现了封闭 ADT 的结论。禁止依赖 `getattr`、捕获 AttributeError 或到处 cast 来补一个未建立的能力。

同一结果不得用若干可随意组合的 optional 字段表达互斥状态，例如“verified=True 但 judgment=None”。字段的合法组合由具体变体保证；对象、命题、前提、局部回执和持久判断各有不同类型。

### 32.6 输入到域元素的数据流

```text
文本 + 当前 revision
  → parser：保留位置的 Surface AST
  → 名称/对象引用解析：SymbolId、ObjectVersionId 固定为快照
  → 词法定义展开与捕获规避整理
  → TypedExpr / Proposition / 合法问题草稿
  → 固定 ProblemSpec + 请求角色/解释
  → 查询已冻结的结构工厂与映射能力
  → AlgebraView[E] 或明确的输入/片段/条件失败
  → 持有确定 parent 的纯代数算法
```

名字在此阶段解析一次，不在系数循环反复查符号表。运行时冻结的是能力工厂和语义世界，不是把 x 永远固定为整个会话的唯一变量。

桥必须说明其数学关系：表示同构可双向传递相等；嵌入可传递相等和不等；一般同态只能保证源相等推出目标相等，不能把源非零推出目标非零。把形式生成元代入 sin/exp 等函数可用于证明多项式恒等式，但不能因此宣称函数代数独立或成立一个任意表达式域。

实现切片（2026-11-09，定义性保留 witness）：桥的 `ConversionWitness` 现在区分是否保留定义性；只有保留定义性的 witness 才能把 `source_domain`/`valid_on` 区域声明读回源表达式，`typed_view` 在准入边界拒绝不保留定义性的区域视图。多项式桥、参数多项式桥与有理桥仍发行保留定义性的表示同构；一般嵌入/同态实现、混域消解与请求嵌入字段仍未建。

参数特化是映射而非文本替换；需要在求值前核验关系和局部化条件。转换回 Term 使用原映射或显式新绑定，不能发明同名全局变量。

### 32.7 候选到可信结果的数据流

```text
固定 ProblemSpec + 候选数据
  → 由绑定的规格构造器生成对该候选的数学承诺
  → kernel 解析 world/frame、前提、checker/schema 和预算
  → checker 核验问题/输入/候选/目标/区域/证书匹配
  → 独立代数验证、定义性/区域/覆盖验证
  → CheckOutcome（只上报实际使用的支持及义务）
  → 条件统一处理、局部支持闭合、自循环检查
  → ValidatedCommitBatch
  → 与工作区输出记录一起原子发布
  → 当前适用性、原请求完成性、解释显示
```

checker 的结果应绑定原问题，而不是只证明证书自行声明的另一个命题。命题本身已验证不等于问题已完成：一个受限区域导数、一组正确但不全的根、一个泛参数公式均可有有效 Judgment，而原请求仍为部分完成。

实现切片（2026-11-09，函数问题的候选绑定）：`FunctionEqualityChecker` 的证书 `left`/`right` 必须与 `ProblemSpec.function_inputs` 精确一致；只比较表示项会接受“同项不同固有域”的伪造函数值。`EqualOn` 在 problem 有区域时要求 problem region 被 claim region 覆盖；`SamePartialFunction` 要求 problem region 位于两侧完整域内。每个 `FunctionValue` 的每个表示区域必须是其固有域的可证子区域；不可证为 `Unverified(GUARDED)`，可证在外为 `InvalidEvidence`，都不伪造 `Refuted`/`Verified`。该切片不替代完整 §32.7 数据流或一般函数定义域核验。

实现切片（2026-11-10，候选代数快照）：`Candidate.algebra` 固定候选被提出时的预装配 `AlgebraRequest`，workspace `_apply` 保存 `execution.algebra`，`edit_candidate` 清除证书时保留，`_candidate_proposal` 原样提交；`check_candidate`/`decide_candidate` 因此把同一 target/parameter/interpretation/differential 快照交给 kernel，而不是重新选择一个视图。固定请求 checker 通过 `context_algebra_mismatch` 统一消费 `VerificationContext.algebra`，按对象同一性比较；函数问题没有代数视图，`FunctionEqualityChecker` 拒绝 algebra 快照，核心逻辑规则不要求 algebra。缺失/不同由 checker 报 `InvalidEvidence`，不是 `Refuted`。该切片不替代完整 §32.7 数据流、跨 frame `externalizable` 前提弱化、注册 `Covers` 规格/checker、嵌入/实嵌入或结果语言覆盖。

实现切片（2026-11-10，`externalizable` 正向路径）：workspace 在 operation 返回固定问题后，用请求的显式 `externalizable` 集替换该问题的集合，并让同一问题对象贯穿 `ExecutionRequest`、候选、提交与任务；operation 自己构造的集合不成为第二权威。`run_task` 传入任务的集合，`_same_problem` 精确比较；不匹配的执行被记录为 blocked，而不是悄悄运行另一个问题。checker 仍只核验规格与候选；proposal 的 `result_region` 作为 `VerificationLink.condition` 参与任务完成性派生，不伪造 kernel obligation。`COMPLETED_CONDITIONAL` 只在全部开放条件都属于该显式集时成立；跨 frame 前提弱化、注册 `Covers` 规格/checker、嵌入/实嵌入、参数关系与结果语言覆盖仍未建。

证书结构校验不等于数学核验；Refuted 必须确实否定所请求规格。区域未证明等价、载荷形状不同、格式不合法，只能产生对应失败，不能伪造否证。

### 32.8 条件与发布的数据流

新支持在校验会话内用不可伪造的局部回执，不递归立即发布。内核按实际使用关系建立证明 DAG、统一继承义务并检查清偿闭合。未被使用的前提不进入支持集；循环目标不能证明自身条件。

workflow 先构造对象/候选/事件/revision 的暂存记录，关联暂存判断句柄，再与内核批次在同一发布边界转换为真实引用。它可以决定放弃批次，不能修改其中数学结论。发布失败无半个用户动作；取消已提交动作不回滚数学历史。

数学核验不持有长时间的发布锁。并发结果仍属于启动时的输入和语义快照，不强行挂到用户后来切换的焦点。缓存与工作区旁路关联也必须服从 revision 可见性，不能在 undo 后悄悄复用未来事件。

实现切片（2026-11-10，`externalizable` 正向路径）：条件结果的 `result_region` 走工作流条件通道而非 kernel obligation；`derive_task_state` 把链接条件与 kernel obligations 一起列为开放条件，并只在固定 `ProblemSpec.externalizable` 显式允许全部开放条件时给出 `COMPLETED_CONDITIONAL`。无条件验证结果保持 `COMPLETED`；不属于显式集的开放条件保持 `PARTIALLY_SOLVED`。该切片不改变 kernel 的条件处理策略，也不声称一般条件证明合并、跨 frame 前提弱化或完整 §32.8 数据流。

### 32.9 手动积分的完整数据流

以 §21.6–§21.7 为例：

1. 用户建立积分 ProblemSpec；被积式是数据，不是假设。
2. 分部积分操作固定所选 u/dv、出现位置、变量及区域；创建两个局部结果槽和有类型的构造关系。
3. 若只是在试算，这些是候选约束，不作为可信前提；若显示为已验证积分关系，必须通过相应定理、边界与正则性 checker。
4. 联立关系进入构造超图，求解它是一个线性代数任务；不能让 I 和 J 在执行 DAG 中相互等待。
5. 线性求解得到具体候选 F；将 F 对原积分问题核验，而非只核验它满足构造方程。
6. 定积分关系还核验初值/端点和基本定理；全部原函数再引入按连通分支组织的常数族。
7. 发布一次或少数明确用户级事件；内部乘加不创建工作簿对象。

修改了 u、换元映射或任一候选公式，就是新快照，不沿用旧核验标签。依据点值等式的替换不能越过积分或导数绑定体，只有满足区域/函数级提升条件的关系才能这么做。

### 32.10 自动 Risch 的完整数据流

```text
表达式 + 变量/参数/区域 + 结果类
 → 固定问题与系数/常数结构
 → 塔分析及每层准入见证
 → 塔内有理表示 + 显式 D
 → 分裂/微分 Hermite/留数/RDE/PRDE 的局部代数状态
 → 分解 (v, 对数项, residual, residual 的已知状态)
 → 表达式回译及实/复区域条件
 → 正向原函数 checker 或有明确完备性依据的 NonElementary checker；当前有理 Hermite checker 已在 `den != 0` 上验证区域化恒等式（源域覆盖、`v`/`r` 分母整除、K(x) 形式等式）
 → 条件/覆盖处理与边界提交
```

塔元素、中间余式、矩阵和 RDE 系数没有 TaskId/JudgmentId。只有真正独立复用或展示的子问题才成为任务。改变搜索策略可以改变候选和成本，不能改变原输入解释或以“剩下未积部分”自动生成 NonElementary。

### 32.11 自动 CAD 与方程组的数据流

CAD：原量化公式 → 多项式原子/变量序 → 投影数据 → 三角样本点与胞腔树 → 符号不变性/覆盖 → 量词真值 → 解公式 → 规格与组合证书。内部 root index 可以构造 CellData，不得混入要求纯实闭域公式的最终结果。

方程组：原多项式/有理约束 → 明确系数域、目标和非零条件 → 理想/饱和 → Gröbner/消元 → 三角/RUR/代数集合表示 → 根选择或参数族 → 回代与完整性核验。不同目标域的最后一步不同：复/代数闭包、实、有理、整数不是只换一个打印标签。

两者通过相同操作/验证/发布边界，但不强制共享搜索算法。CAD 几何覆盖和 Gröbner 理想相等是不同证书，不互相冒充。

### 32.12 全参数线性方程的数据流

对 a*x+b=0，固定参数空间与目标 x 后：

```text
泛点计算 → a≠0 上的 {-b/a} 与有效性见证
残余 a=0 → b=0 / b≠0 两支
各支结果 → soundness + completeness
支条件 → 父参数空间覆盖（必要时互斥）
真实分支支持 → 合并为条件解集
```

“进入 a≠0 假设继续算”是一个受限问题，不是原任务完成。特化 a=0 时先检查失效并回原问题，不能将 0 代入 -b/a 后试图修补答案。完整参数图既保留算法的分支，也保留其证明来源。

### 32.13 各阶段的写权限与成本位置

| 阶段 | 可变状态 | 不允许的副作用 | 成本优化位置 |
|---|---|---|---|
| 解析/整理 | 局部语法缓冲、受控上下文扩展 | 偷改旧定义或旧对象 | 定义 DAG、固定意义缓存 |
| 代数算法 | 私有稀疏表、矩阵工作区、模计算缓冲 | 查工作簿焦点、逐次发行证明 | 表示、位增长、分式自由/模算法 |
| 候选策略 | 局部计划、预算与尝试状态 | 自行标记数学完成 | 可复用子任务和选择策略 |
| checker | 局部代数工作区、支持收集 | 调用对应搜索并信其成功、直接写账本 | 独立短证书、共享基础算术 |
| 条件/批次 | 私有回执、依赖拓扑、待发布记录 | 条件未闭合就 discharge、循环支持 | 语义去重、有界索引 |
| 发布 | 单写协调器或数据库事务 | 修改核验后的结论 | 短事务、批量关联 |
| 显示/历史 | 视图缓存、焦点/revision 指针 | 创造 +C、隐藏条件、赋予候选真假 | 分页/折叠，不改变语义 |

全部数学值与外部可见记录仍是不可变的；算法内部可变工作区不对外泄漏。性能报告按这些阶段分解，不把“核验开启”当作不分析瓶颈的借口，也不承诺 checker 必然比搜索便宜。
