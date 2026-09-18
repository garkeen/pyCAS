# pyCAS v4 架构设计报告

> 设计目标：构建一个通用、纯符号、支持自动计算与手动交互的 CAS。  
> 系统严格记录上下文、守卫、定义、分支与推导依赖，但不实现通用定理搜索，也不为积分、ODE、换元等功能向内核增加特化原语。

以下设计以 **2026 年 9 月 8 日当前 `master`** 为迁移基线。v3 已经确立了三值判定、手动/自动双通道、独立验证、守卫传播和步骤 DAG 等正确方向；当前主要结构问题是：工作流使用封闭的 `Derivation` ADT 并通过 `isinstance` 分派功能验证，模式变量仍然属于 `Term`，上下文则主要以可变列表和 clone 组织。

---

# 一、最终架构结论

pyCAS v4 分为四个真正的语义层，加一个装配层：

```text
syntax/
    只表示和操作语法

kernel/
    管理上下文中的条件性数学结论

workflow/
    管理用户正在做什么、先做什么、在哪里做

math/
    定义数学对象、规则、守卫语义、算法和验证器

runtime/
    显式装配上述部分
```

最重要的职责边界是：

> **数学模块负责产生和判断守卫；内核负责记录、传播、清偿和约束守卫的作用域；工作流负责组织用户操作。**

因此：

- 不能让工作流自己猜守卫；
- 不能让算法直接向步骤图写入“真结论”；
- 不能把未知守卫自动加入假设；
- 不能把每一个工作流箭头解释成等式；
- 不能把守卫附着到每个 `Term`；
- 也不能让内核完全不知道守卫和上下文。

---

# 二、设计原则

## 2.1 项是纯语法

`Term` 不包含：

```text
guards
context
domain
proof
history
integration_constant
substitution_variable
ode_solution
```

项只回答：

> “这个表达式长什么样？”

而不回答：

> “它在什么条件下有定义？”  
> “它是否等于另一个表达式？”  
> “这个结果是怎么得到的？”

---

## 2.2 内核的基本对象不是“变换后的表达式”，而是条件性结论

统一采用：

\[
\Gamma\vdash P\;[\Delta]
\]

其中：

- \(\Gamma\)：作用域中的声明、定义和假设；
- \(P\)：经过验证的数学命题；
- \(\Delta\)：仍未清偿的条件。

其语义是：

\[
\Gamma\models
\left(\bigwedge \Delta\right)\Rightarrow P.
\]

例如：

\[
x\in\mathbb R
\vdash
\frac{x}{x}=1
\quad[x\ne0].
\]

这里：

- `x ∈ ℝ` 是上下文声明；
- `x ≠ 0` 是该结论的开放条件；
- `x ≠ 0` 并没有自动成为假设。

---

## 2.3 算法产物不是数学结论

例如求导：

```text
输入：x²
产物：2x
结论：Derivative(x², x) = 2x
```

表达式 `2x` 是一个产物。

真正可参与后续可信推导的是：

```text
Derivative(x², x) = 2x
```

因此工作流必须区分：

```text
Artifact    数据、候选、表达式
Judgment    已验证的数学结论
```

---

## 2.4 手动与自动共享提交协议，不必共享算法过程

手动分部积分可以产生十个细步骤。

Risch 算法可以只产生一个最终候选和一个证书。

两者最终都通过：

```text
候选结论
+ 显式前提
+ 证据
+ 可能的守卫
→ kernel.commit(...)
```

---

## 2.5 不建立功能特化内核原语

内核中不应存在：

```text
IntegrateStep
ODESolveStep
ChangeVariableStep
IntegrationConstant
AntiderivativeEquality
RowEquivalentPrimitive
```

允许存在的是通用结构：

```text
Scope
Assumption
Definition
Requirement
Judgment
Evidence
Step
```

积分、ODE、矩阵、求解，只是产生不同数学命题和不同证书的模块。

---

# 三、目标文件架构

这是一棵目标结构，不要求立即创建所有空目录。一个模块只有在出现实际代码时才拆分。

```text
pyCAS/
├── pyproject.toml
├── docs/
│   ├── v4-architecture.md
│   ├── kernel-semantics.md
│   ├── module-contract.md
│   ├── workflow-model.md
│   └── trust-boundary.md
│
├── src/
│   └── pycas/
│       ├── __init__.py
│       ├── api.py
│       │
│       ├── syntax/
│       │   ├── __init__.py
│       │   ├── term.py
│       │   ├── factory.py
│       │   ├── signature.py
│       │   ├── binder.py
│       │   ├── substitute.py
│       │   ├── path.py
│       │   ├── traverse.py
│       │   ├── pattern.py
│       │   ├── match.py
│       │   └── abstract.py
│       │
│       ├── kernel/
│       │   ├── __init__.py
│       │   ├── ids.py
│       │   ├── verdict.py
│       │   ├── scope.py
│       │   ├── context.py
│       │   ├── model.py
│       │   ├── evidence.py
│       │   ├── rule.py
│       │   ├── services.py
│       │   ├── commit.py
│       │   ├── store.py
│       │   ├── resolve.py
│       │   └── export.py
│       │
│       ├── workflow/
│       │   ├── __init__.py
│       │   ├── artifact.py
│       │   ├── task.py
│       │   ├── constraint.py
│       │   ├── branch.py
│       │   ├── focus.py
│       │   ├── command.py
│       │   ├── event.py
│       │   ├── history.py
│       │   └── session.py
│       │
│       ├── runtime/
│       │   ├── __init__.py
│       │   ├── registry.py
│       │   ├── runtime.py
│       │   ├── dispatch.py
│       │   └── bootstrap.py
│       │
│       ├── math/
│       │   ├── __init__.py
│       │   ├── module.py
│       │   │
│       │   ├── base/
│       │   │   ├── module.py
│       │   │   ├── operators.py
│       │   │   ├── logic.py
│       │   │   ├── equality.py
│       │   │   ├── definedness.py
│       │   │   └── rewrite.py
│       │   │
│       │   ├── domains/
│       │   │   ├── protocol.py
│       │   │   ├── registry.py
│       │   │   ├── integers.py
│       │   │   ├── rationals.py
│       │   │   ├── polynomial.py
│       │   │   ├── fraction.py
│       │   │   ├── algebraic.py
│       │   │   ├── real_algebraic.py
│       │   │   ├── matrix.py
│       │   │   └── projection.py
│       │   │
│       │   ├── arithmetic/
│       │   │   ├── module.py
│       │   │   ├── normalize.py
│       │   │   ├── rules.py
│       │   │   └── checkers.py
│       │   │
│       │   ├── elementary/
│       │   │   ├── module.py
│       │   │   ├── rules.py
│       │   │   ├── definedness.py
│       │   │   ├── derivatives.py
│       │   │   └── deciders.py
│       │   │
│       │   ├── piecewise/
│       │   │   ├── module.py
│       │   │   ├── rules.py
│       │   │   ├── definedness.py
│       │   │   └── checkers.py
│       │   │
│       │   ├── calculus/
│       │   │   ├── differentiation/
│       │   │   │   ├── module.py
│       │   │   │   ├── rules.py
│       │   │   │   ├── algorithm.py
│       │   │   │   ├── checkers.py
│       │   │   │   └── commands.py
│       │   │   │
│       │   │   └── integration/
│       │   │       ├── module.py
│       │   │       ├── rules.py
│       │   │       ├── manual.py
│       │   │       ├── dispatch.py
│       │   │       ├── rational.py
│       │   │       ├── risch.py
│       │   │       ├── checkers.py
│       │   │       └── commands.py
│       │   │
│       │   ├── solving/
│       │   │   ├── equations/
│       │   │   │   ├── module.py
│       │   │   │   ├── algorithms.py
│       │   │   │   ├── checkers.py
│       │   │   │   └── commands.py
│       │   │   │
│       │   │   ├── inequalities/
│       │   │   │   ├── module.py
│       │   │   │   ├── algorithms.py
│       │   │   │   ├── cad.py
│       │   │   │   ├── checkers.py
│       │   │   │   └── commands.py
│       │   │   │
│       │   │   └── ode/
│       │   │       ├── module.py
│       │   │       ├── classify.py
│       │   │       ├── algorithms.py
│       │   │       ├── checkers.py
│       │   │       └── commands.py
│       │   │
│       │   └── linalg/
│       │       ├── module.py
│       │       ├── algorithms.py
│       │       ├── checkers.py
│       │       └── commands.py
│       │
│       └── frontend/
│           ├── parser.py
│           ├── pretty.py
│           ├── latex.py
│           ├── serialization.py
│           └── repl.py
│
└── tests/
    ├── syntax/
    ├── kernel/
    ├── workflow/
    ├── math/
    ├── integration/
    └── regression/
```

---

# 四、依赖方向

```text
syntax
   ↑
kernel
   ↑
workflow

math/domains ─────→ syntax
math/base    ─────→ syntax + kernel
math/features ────→ syntax + kernel + workflow + math/domains

runtime/bootstrap → 所有数学模块
frontend          → api + workflow + runtime
```

具体约束：

| 包 | 允许依赖 |
|---|---|
| `syntax` | Python 标准库 |
| `kernel` | `syntax` |
| `workflow` | `syntax`, `kernel` |
| `math/domains` | `syntax` |
| 其他 `math` 模块 | `syntax`, `kernel`, `workflow`, `math/domains` |
| `runtime` | 接口层；`bootstrap` 可导入所有模块 |
| `frontend` | `api`, `workflow`, `runtime` |

严格禁止：

```text
syntax   → kernel
kernel   → concrete math module
kernel   → workflow
workflow → concrete integration/ODE solver
checker  → 对应的搜索算法实现
```

内核通过接口调用注册的 checker/decider，但源码不导入具体数学模块。

**同一个规则也决定对象之间的引用方向：指针只许指向下方层（或同层）。** 指针
就是源码级的名字可见性，指错了就等于引入反向 import。各对象的引用面：

```text
kernel 内：  Judgment.producer            → StepId
             Step.premises/conclusions    → JudgmentId
             Requirement.introduced_by    → StepId
             Discharge.by_judgment        → JudgmentId
             （以上都不跨层）
workflow 内：Artifact.produced_by          → EventId
             Task.scope / Constraint.scope → ScopeId     （workflow → kernel，合规）
             TaskCandidate.validation      → JudgmentId   （workflow → kernel，合规）
             BranchGroup.coverage          → JudgmentId   （workflow → kernel，合规）
跨层出口：   Event.outputs                 → ArtifactId | TaskId | ConstraintId
                                            | StepId | JudgmentId
```

**`Event.outputs` 是唯一连接「操作」与「内核结论」的地方**（workflow → kernel，
合规）。内核侧（Scope / Judgment / Step / Requirement / Discharge / Applicability）
**没有任何指向 Artifact / Task / Event 的字段**——所以「这张结论是哪个操作造出来的」
只能由 Event 侧回答。溯源链是：

```text
Judgment → Step → Event
```

（`Judgment.producer → Step` 是回溯指针，不构成数学依赖；证明图的无环性由
premises → conclusions 决定，见 §8.5 / 不变量 11。）

反向索引（EventId → 本次产出的内核 id 列表）建在 **workflow 侧**，内核不参与。
undo/redo 移 revision 指针时，靠它知道该重新指向哪些内核对象。

**为什么 Event 与 Step 不能合并**（三条，任一即可否决）：两者是不同关系
（Step 带推理依赖，Event 带发生顺序，§8.1 明确禁止混同）；基数不同（一条
`interactive` 化简可产几百个 Artifact 而**零个** Step）；可撤销性不同
（undo/redo 只移 revision 指针，内核账本追加式、结论不可删，§四.5 / §8.9）。

---

# 五、`syntax/`：纯语法层

## 5.1 项结构

建议保留少量驻留项类型：

```python
class Term: ...

class Symbol(Term):
    name: str

class Integer(Term):
    value: int

class Rational(Term):
    numerator: int
    denominator: int

class Bound(Term):
    index: int

class Call(Term):
    head: Term
    args: tuple[Term, ...]
```

数学对象全部是普通 `Call`：

```text
Plus(a,b)
Equal(a,b)
Integral(body, binder)
Derivative(body,x)
Matrix(...)
Solve(problem,x)
```

内核不认识这些 head。

## 5.2 模式不是项

当前代码中 `PatVar`、`PatSeq` 是 `Term` 子类；v4 应将它们移入模式元语言。

```python
class Pattern: ...

class PatternVar(Pattern):
    name: str

class PatternSeq(Pattern):
    name: str

class PatternCall(Pattern):
    head: Pattern
    args: tuple[Pattern, ...]
```

这能阻止模式变量意外进入用户表达式、域投影和数学判等。

## 5.3 绑定变量

`binder.py` 统一处理：

```text
Lambda
Integral
Sum
Product
Limit
SetBuilder
ForAll（如果仅作为库公式）
```

只提供：

```python
abstract(term, symbol)
instantiate(body, value)
shift(term, amount, cutoff)
alpha_equal(a, b)
```

不存在“积分换元专用 substitution”。

## 5.4 子项抽象

`abstract.py` 提供：

```python
abstract_subterms(term, predicate)
thaw(term, environment)
```

输出：

```python
@dataclass(frozen=True)
class Abstraction:
    term: Term
    replacements: tuple[tuple[Symbol, Term], ...]
```

用途包括：

- 循环积分方程；
- 把 `sin(x)` 当代数未知量；
- 把 `y'(x)` 当方程未知量；
- 矩阵表达式方程；
- 特殊函数表达式的多项式化。

这只是语法抽象。将被冻结项视为代数独立元是否安全，由使用它的数学算法和 checker 决定。

---

# 六、通用内核模型

## 6.1 内核管理什么？

内核负责：

1. 作用域和上下文；
2. 条件性结论；
3. 条件的传播与清偿；
4. 前提是否可访问；
5. 证据检查器调用；
6. 结论依赖图；
7. 局部定义和辅助符号的逃逸检查。

内核不负责：

1. 如何积分；
2. 如何求解 ODE；
3. `log` 的定义域是什么；
4. 矩阵何时可逆；
5. 某个积分结果是否覆盖所有原函数；
6. 自动搜索证明。

---

## 6.2 Scope：持久化作用域树

```python
@dataclass(frozen=True)
class Scope:
    id: ScopeId
    parent: ScopeId | None

    declarations: tuple[Declaration, ...]
    definitions: tuple[Definition, ...]
    assumptions: tuple[Assumption, ...]
```

三类上下文条目：

### 声明

```text
x : Real
n : Integer
c : Parameter independent of x
y : Function(Real, Real)
```

### 定义

```text
u := x²
I := Integral(exp(t) sin(t), (t,0,x))
```

定义是局部别名，不是用户需要证明的数学等式。

内核只检查：

- 左侧符号新鲜；
- 不形成非法递归；
- 右侧在父作用域中良好绑定；
- 局部符号不能泄漏到父作用域结论。

### 假设

```text
x > 0
a ≠ 0
continuous(f, I)
```

假设是用户或分支明确接受的条件。

开放守卫不能自动写入 `assumptions`。

---

## 6.3 Requirement：开放条件

```python
@dataclass(frozen=True)
class Requirement:
    id: RequirementId
    scope: ScopeId
    proposition: Term
    introduced_by: StepId
    reason: RequirementReason
```

例如：

```text
x ≠ 0
a > 0
det(A) ≠ 0
continuous(f, [a,b])
```

`RequirementReason` 可以保留 v3 的分类思想：

```python
class RequirementReason(Enum):
    DEFINEDNESS
    RULE_GUARD
    ALGORITHM_PRECONDITION
    BRANCH_COVERAGE
    DOMAIN_MEMBERSHIP
```

而判定失败原因继续使用：

```text
FRAGMENT
GUARDED
UNDECIDABLE
BUDGET
```

四种理由的后果完全不同，**禁止折叠成同一个「不知道」**：

| 理由 | 含义 | 消解方式 |
|---|---|---|
| `FRAGMENT` | 片段没覆盖，表达式含未建结构 | 扩声明或扩算法即可判定 |
| `GUARDED` | 被未确认条件挡住 | 条件清偿后答案自动翻转 |
| `UNDECIDABLE` | 可证不可判定 | 不可消解。每一格都必须引用数学定理（希尔伯特第十问题、Richardson 定理等），不是能力占位符 |
| `BUDGET` | 可判定但资源超限 | 放宽预算可能翻转——「没找到」不等于「不存在」 |

判定结果是代数数据类型而非字符串：`Yes(证据)`、`No`、`Unknown(理由)`，匹配必须穷尽，漏分支是错误。失败是返回值的一部分，禁止用异常吞掉错误；空缺用 `None`/`Option` 表达。

---

## 6.4 Judgment：可依赖的数学结论

```python
@dataclass(frozen=True)
class Judgment:
    id: JudgmentId
    scope: ScopeId

    proposition: Term
    requirements: tuple[RequirementId, ...]

    producer: StepId
```

例子：

```text
Equal(x/x, 1)
Equal(Derivative(x²,x), 2x)
SatisfiesEquation(x²=1, x=1)
CompleteSolution(problem, result)
```

注意最后两个命题由方程模块定义，内核只把它们当普通 `Term`。

---

## 6.5 证书必须对应确切命题

不使用模糊的：

```python
sound = True
complete = False
```

而应产生不同的判断：

```text
IsSolution(problem, candidate)
CompleteSolution(problem, answer)
```

例如 ODE 回代只能证明：

```text
SatisfiesODE(problem, y=c*exp(x))
```

它不能自动证明：

```text
CompleteSolutionFamily(problem, {c*exp(x)})
```

后者需要另一份证书和另一个 checker。

---

## 6.6 Step：数学依赖边

```python
@dataclass(frozen=True)
class Step:
    id: StepId
    scope: ScopeId

    premises: tuple[JudgmentId, ...]
    conclusions: tuple[JudgmentId, ...]

    evidence: Evidence
    reads: ContextReadSet
```

`Step` 没有子类：

```text
没有 DiffStep
没有 IntegrateStep
没有 SolveStep
没有 MergeStep
```

步骤究竟做了什么，由结论命题和证据说明。

---

## 6.7 Evidence 和 checker

```python
@dataclass(frozen=True)
class Evidence:
    checker_id: str
    payload: object
```

示例：

```python
Evidence(
    checker_id="rule.instance",
    payload={
        "rule_id": "field.cancel",
        "substitution": {...},
    },
)
```

```python
Evidence(
    checker_id="calculus.antiderivative",
    payload={
        "integrand": f,
        "variable": x,
        "candidate": F,
    },
)
```

checker 接口：

```python
class Checker(Protocol):
    def check(
        self,
        proposal: StepProposal,
        context: TrackedContext,
        services: KernelServices,
    ) -> CheckResult:
        ...
```

结果：

```python
Accepted(
    direct_requirements=(...),
    reads=ContextReadSet(...),
)

Rejected(reason)

Unknown(reason)
```

关键点：

> 守卫不能只由算法自己声明。checker 必须复核并返回使结论成立所需的直接条件。

---

## 6.8 RuleSchema：通用条件规则

```python
@dataclass(frozen=True)
class RuleSchema:
    id: str

    premises: tuple[Pattern, ...]
    conclusions: tuple[Pattern, ...]
    conditions: tuple[Pattern, ...]

    tags: frozenset[str]
```

约分规则：

```text
条件：b ≠ 0
结论：(a*b)/b = a
```

传递性规则：

```text
前提：a = b
前提：b = c
结论：a = c
```

二者使用同一个规则实例化 checker。

但规则本身属于数学模块：

```text
field.cancel      → arithmetic/field 模块
equality.trans    → math/base/equality.py
```

内核不建立“关系属性注册表”。

---

## 6.9 `commit` 是唯一可信提交入口

```python
@dataclass(frozen=True)
class StepProposal:
    scope: ScopeId
    premises: tuple[JudgmentId, ...]
    conclusions: tuple[Term, ...]
    evidence: Evidence
    guard_policy: GuardPolicy
```

提交过程：

```text
1. 检查 scope 与项的绑定合法性
2. 检查 premise 是否在当前 scope 可访问
3. 调用 checker
4. checker 验证结论并返回直接条件
5. 收集 premise 继承的未清偿条件
6. 使用当前 context 尝试清偿条件
7. Proved   → 记录清偿依据
8. Refuted  → 本次应用不适用，拒绝提交
9. Unknown  → 根据 guard policy 处理
10. 原子地写入 Step、Judgment、Requirement
```

守卫策略：

```python
class GuardPolicy(Enum):
    REQUIRE_PROVED       # 自动化简默认
    ALLOW_CONDITIONAL    # 手动显式应用规则
    REQUEST_SPLIT        # 自动要求分类讨论
```

当前 v3 的规则应用只有守卫返回 `YES` 时才落地，未知守卫不静默通过；v4 应保留这种自动模式，同时增加显式的“条件性提交”能力。

---

## 6.10 条件清偿不会修改原 Judgment

```python
@dataclass(frozen=True)
class Discharge:
    requirement: RequirementId
    by_judgment: JudgmentId
    scope: ScopeId
```

如果之后证明了 `x ≠ 0`：

- 原来的条件结论不变；
- 新增一条 `Discharge`；
- 在该作用域中查询时，结果变为可直接应用。

如果证明了 `x = 0`：

- 条件结论本身仍是正确的条件命题；
- 但在当前作用域中状态为 `Inapplicable`；
- 不应删除或级联销毁原结论。

```python
Applicability =
    Applicable()
  | Conditional(requirements)
  | Inapplicable(refutations)
```

---

## 6.11 TrackedContext：任何隐式使用都必须留下读依赖

checker 不直接读取裸 `Context`，而读取：

```python
class TrackedContext:
    def lookup_definition(...): ...
    def assumptions(...): ...
    def query_fact(...): ...
    def decide(...): ...

    def read_set(self) -> ContextReadSet: ...
```

如果 checker 使用了：

```text
x ∈ ℝ
x > 0
u := x²
某个已证明等式
```

这些都进入 `Step.reads`。

这样不会出现：

> 一个步骤实际上依赖某条假设，但步骤记录中没有体现。

---

# 七、数学模块模型

## 7.1 统一模块契约

```python
class MathModule(Protocol):
    id: str
    version: str
    dependencies: tuple[str, ...]

    def install(self, builder: RuntimeBuilder) -> None:
        ...
```

典型安装：

```python
def install(builder):
    builder.heads.register(...)
    builder.rules.register(...)
    builder.checkers.register(...)
    builder.deciders.register(...)
    builder.definedness.register(...)
    builder.algorithms.register(...)
    builder.commands.register(...)
```

禁止通过 import 自动修改全局状态。

---

## 7.2 每个数学模块包含什么？

一个完整模块可以包含：

```text
module.py
    模块清单、head 注册、安装函数

rules.py
    数学规则和定理模式

definedness.py
    定义条件、参数合法性

deciders.py
    可判定片段

algorithms.py
    搜索候选的算法

checkers.py
    验证候选结论

commands.py
    用户可见的手动操作
```

不是每个模块必须创建全部文件。

---

## 7.3 算法与 checker 的依赖纪律

例如：

```text
integration/risch.py
```

可以依赖：

```text
多项式
有理函数
微分域塔
线性代数
因式分解
```

但：

```text
integration/checkers.py
```

不能导入 `risch.py`。

它可以依赖独立的：

```text
微分器
域标准形
恒等判定
定义域分析
```

因此：

```text
Risch 找到 F
→ checker 证明 D(F)=f
```

不是：

```text
Risch 找到 F
→ Risch 自己说自己正确
```

验证独立性还有三条要求：

- 验证器与求解器必须是两套独立实现，自己验证自己等于没有验证。
- 手动步骤与自动结果过同一套验证器。验证器按推导类型分派：Solve 只做回代判官（代入 + 域标准形判零，不重跑求解公式）；微分结果由域层导数（另一实现）交叉复核；规则重写复核声明的规则产物；分支切割验证排中律覆盖。
- 启发式搜索可以探索任何问题：找到候选就送验证，通过即成立。「未找到」与「不存在」是两个结论，后者只能出自可判定片段的判定器并携带证据。

---

## 7.4 定义域知识的位置

定义域知识属于数学模块，不属于内核。

例如：

```text
Div(a,b):      b ≠ 0
Log(x):        x > 0          （实数语义）
MatrixInv(A):  det(A) ≠ 0
```

Piecewise 必须路径敏感：

\[
\operatorname{WD}
\begin{cases}
1/x,&x\ne0\\
0,&x=0
\end{cases}
\]

不能简单变成全局条件 \(x\ne0\)。

它应近似产生：

\[
(x\ne0\Rightarrow \operatorname{WD}(1/x))
\land
(x=0\Rightarrow \operatorname{WD}(0)).
\]

因此：

> `commit` 管守卫生命周期，但守卫必须由规则 checker、定义域分析器或算法 checker 在语义仍完整时产生。

不能等结果算完后再从结果 AST 猜。

---

## 7.5 相等替换不是任意路径替换

语法层可以执行：

```python
replace_at(term, path, replacement)
```

但它只能说明 AST 被修改了。

数学上从：

\[
A=A'
\]

推出：

\[
F(A)=F(A')
\]

需要 equality 模块的替换规则。

对于 `Plus`：

\[
A=A'\Rightarrow A+B=A'+B
\]

通常成立。

但不能无条件对所有 head 使用相同规则：

- 进入 `Piecewise` 分支时要加入路径条件；
- 进入绑定体时要处理绑定和自由变量；
- 点值相等不一定足以在 `Derivative` 下替换；
- 积分区间、被积函数恒等和点值等式并非同一条件；
- held/quoted 表达式可能根本不允许数学替换。

因此数学 head 可以注册：

```text
congruence/lifting checker
```

而不是让内核硬编码所有 head 的同余规则。

---

## 7.6 域系统

`math/domains` 是可复用的精确数学机器：

```text
ℤ
ℚ
ℚ(i)
代数扩张
多项式环
有理函数域
实代数数
矩阵 over domain
```

域对象不认识：

```text
当前工作流
当前任务
用户焦点
步骤编号
积分命令
```

它们只提供：

```python
contains
normalize
equal
add
mul
gcd
factor
differentiate
solve_linear
```

表达式与域元素之间通过显式投影：

```python
project(term, domain_request, context)
embed(domain_element)
```

算法在哪个域内计算，与最终向用户声称的命题要区分：

```text
域内有理函数判等
≠
实数点值部分函数判等
```

这种桥接由数学 checker 负责，并可能生成定义域条件。

---

## 7.7 判定层：命题复合与语义来源

判定层是**命题复合 + 域特定可判定原子**，不是一阶逻辑，不是定理证明器；系统不做运行时量词推理。全称事实是声明引理，按模式匹配实例化。复合层只需三值命题运算 `and3`/`or3`/`not3`，并传播首个未决理由。

CAS 依赖的三种语义各有来源：

- **代数语义**（等式、规则）：域判等（片段内完全判定）+ 声明规则（无条件恒等式才入册）
- **序语义**：判定管线——假设帧 + 区间通道 + 声明的常数界引理。序只在有序域上有意义，是域的能力字段，不是全局预设
- **逻辑语义**：命题复合 + 守卫清偿 + 排中律分支。分支帧内的结论作为条件命题成立；矛盾假设不做一致性检查

判定管线：规则触发前检查守卫；判零统一走所在域的标准形比较；无法确定时返回 `Unknown` 并携带 6.3 定义的四种理由之一。序判定按「假设帧 → 区间通道（链式不等式的图搜索）→ 结构符号引理 → 声明的常数界与函数值域界」逐层尝试，全部输出判定契约类型。

---

## 7.8 拒答协议表

| 触发情形 | 边界名称 | 理由等级 |
|---|---|---|
| ℤ/ℕ 上一般多项式方程解的存在性 | 希尔伯特第十问题（Matiyasevich 1970） | UNDECIDABLE |
| 指数多项式求整数零点 | Skolem 问题，尚未解决 | FRAGMENT（开放） |
| ℚ 上多项式方程解的存在性 | 希尔伯特第十问题之 ℚ 版本，公开未决 | FRAGMENT（开放） |
| 超越常数组合判零且声明里无引理 | Richardson 定理 | UNDECIDABLE |
| 超越方程的根之间比大小且无声明事实 | 无完备算法 | UNDECIDABLE |

发现新的已知边界就增补一行。这张表是数据，防止边界共识随换人蒸发。注意区分两类拒答：定理保证不可判定的用 `UNDECIDABLE`；连「是否可判定」都未解决的用 `FRAGMENT` 并标注开放——前者是数学结论，后者是诚实留白。

---

## 7.9 根与序：可判定性地图与分层实现

分段函数的一切操作——求导的分段点、定积分的区间切分、解方程的支域、条件合并——最终都归结为四个原子问题：根**存在吗**、**有几个**、**谁大谁小**、**两个对象相等吗**（零等价）。这四个问题的可判定性随数域扩张断崖式下跌，这张地图决定哪些层能建、哪些层只能拒绝：

| 原子问题 | 代数世界（ℚ/代数数系数与端点） | 超越世界 |
|---|---|---|
| 根存在性 / 计数 | **可判定**：单变量 Sturm 计数；多变量 CAD（代价对变量数双指数） | 含全轴 sin：**不可判定**；仅 exp：开放（Schanuel 猜想下可判定）；知识覆盖的局部情形（已知单调性/零点集）可判 |
| 根隔离与排序 | **可判定**：隔离区间 + 加细；Thom 编码做精确算术与比较 | 可分离根：**可靠半判定**（区间加细到分离即证不等）；判等**无完备算法** |
| 端点 / 常数判等 | **可判定**：极小多项式相同 + Thom 符号一致 | **不可判定**（Richardson 定理，见 7.8 第四行） |
| 实闭域量词消去 | **可判定**（Tarski；Collins CAD 1975） | ℝ_exp：Macintyre–Wilkie 1996 在 Schanuel 猜想下可判定，无条件未解决；ℝ+sin 不可判定 |

理论锚点（每条都是公开数学结论，不是能力占位符）：

- π 一阶可定义为「sin 的最小正零点」，而 sin(πx)=0 ⟺ x∈ℤ——(ℝ,+,·,sin) 解释出整数算术，理论不可判定。这是「超越根不止一个怎么排序」类问题无完备算法的根源：不存在的东西不能靠工程补出来
- Richardson 定理（1968）：由 ℚ、π、log 2、exp、sin、|·| 复合而成的常数判零不可判定。区间算术对「≠」是半判定程序——加细到区间分离即证明不等；分不开时不存在更强算法，只能 `Unknown`
- CAD 双指数于变量数：多变量代数情形可判定但昂贵，单变量 Sturm 是代价锚点——分层先建一维是成本依据，不是权宜

分层实现（顺序即依赖序；每层的合法性条件：输出过验证器或携带 `Verdict`，层内「分不开」如实升级为 `Unknown`）：

- **L0 代数核（已建）**：一维 CAD + Sturm 根隔离 + 胞腔符号判定，精确完备
- **L1 ℚ(α) 精确化**：代数端点的精确算术与比较（mod-m + Thom 编码），把「无理分界点拒答」清成可判定——这一格是 `FRAGMENT`，不是 `UNDECIDABLE`，纯增量
- **L2 区间算术比较层**：可计算函数（exp/log/sin/atan…）的任意精度区间求值——分离即 Yes/No，重叠即 `Unknown`。这不是启发式：它是「≠/<」在 Richardson 墙下最强的可靠程序，输出天然是 6.3 的 `Verdict`。数值只以带误差界、可无限加细的隔离形式出现，裸浮点禁止进入符号通道
- **L3 声明序引理**：单调性、零点集（sin 零点恰为 kπ）、周期、凸性作为 `FunctionDecl` 数据入册——知识覆盖的局部超越比较由 `FRAGMENT` 降为可判。序引理与导数模板同一准入纪律：无条件可证者才入册
- **L4 超越根对象**：(方程, 隔离区间) 对象 + 加细协议。排序靠区间分离；等号仅在可证时成立（同定义方程且隔离区间重叠，或声明引理）。根簇、疑似重根、周期外的无穷多根一律拒绝
- **L5 包络归约（后置可选）**：Taylor/Remez 有理包络把超越不等式严格归约为代数不等式，再交实闭域判定（MetiTarski 路线）——可靠不完备，作 L2/L3 的增强而非替代

---

## 7.10 Unknown 的出口纪律

「任何环节出现 `Unknown` 就整体拒绝」是过粗的规则：它一并禁掉了条件化答案（端点序未决时，答案本身可以按参数条件分支给出——未决性被**提升为答案结构**，不是被消灭）与开放步骤（验证未决 ≠ 内容被否证）。正确的不变量是：

**`Unknown` 只能沿三条显式出口离开系统，绝不静默消解。**

1. **条件化传播**：未决比较提升为答案中的显式条件（条件分支容器承载），答案同时携带完备性声明——`complete`，或 `partial`（附逐条未决清单）。枚举型通道（契约是「全部解」）任一支未决时，要么整体拒答，要么显式降级为 `partial` 并列出未决项；已知解与未决项不允许无标注地混在一起
2. **开放步骤**：验证未决 → 步骤 `open`，永不 `dead`。`No` 必须携带证据（7.3），无证据不得声称否证
3. **带理由拒答**：按 6.3 四理由分派；定理级边界逐行对照 7.8 表

禁止的消解方式（一律视为作弊）：静默选支（把 `Unknown` 当真/假使用）、静默丢支（部分解冒充全解）、generic 答案（稠密开集上正确冒充全域正确）、无误差界的数值定序混入符号通道。

用户消解通道：假设/split 是唯一合法的第三方消解——用户为具体实例注入比较事实或假设，帧内重判，`GUARDED` 守卫清偿后答案自动翻转。其边界：注入的事实只对该实例生效，系统不得据此把 7.8 表的 `UNDECIDABLE` 行改判为可判——定理针对一般情形，实例事实不推翻定理。

---

# 八、工作流模型

## 8.1 工作流不是真理内核

工作流负责：

- 当前用户在解决什么问题；
- 产生了哪些候选；
- 当前焦点在哪里；
- 分支如何组织；
- 用户操作历史；
- undo/redo；
- 哪个结果被选为当前答案。

工作流不能：

- 绕过 kernel 添加 Judgment；
- 把算法候选直接标为 VERIFIED；
- 把步骤时间顺序当作数学依赖；
- 把工作流图路径当作等式链。

---

## 8.2 Artifact：中性计算产物

```python
@dataclass(frozen=True)
class Artifact:
    id: ArtifactId
    scope: ScopeId
    value: Term
    produced_by: EventId
```

Artifact 没有真假。

例如：

```text
2x
{-1,1}
c*exp(x)
Piecewise(...)
```

都只是 artifact。

---

## 8.3 Task：计算问题

```python
@dataclass(frozen=True)
class Task:
    id: TaskId
    scope: ScopeId
    request: Term
    parent: TaskId | None
```

请求仍然是普通项：

```text
Simplify(expr)
Differentiate(expr,x)
Integrate(expr,x)
Solve(equation,x)
SolveODE(equation,y,x)
```

没有封闭的 `TaskKind` 枚举。

数学模块为请求提供“候选规格”：

```text
Simplify(f) 的候选 g：
    Equal(f,g)

Differentiate(f,x) 的候选 g：
    Equal(Derivative(f,x),g)

Integrate(f,x) 的候选 F：
    Equal(Derivative(F,x),f)

Solve(P,x) 的候选 r：
    Substitute(P,x,r)

SolveODE(P,y,x) 的候选 Y：
    Substitute(P,y,Y)
```

完整解、解族完备性是额外命题，不与候选正确性混为一谈。

---

## 8.4 TaskCandidate

```python
@dataclass(frozen=True)
class TaskCandidate:
    task: TaskId
    artifact: ArtifactId
    validation: JudgmentId | None
```

状态由数据推导：

```text
validation is None
    → 未验证候选

validation 存在但有开放 requirement
    → 已验证的条件候选

validation 可直接应用
    → 已验证候选
```

不需要可变的 `verified=True`。

---

## 8.5 三种图不能混在一起

### 1. 数学结论依赖 DAG

位于 kernel：

```text
Judgment → Step → Judgment
```

只表示数学依赖，必须无环。

### 2. 任务/子计算图

位于 workflow：

```text
Task → Subtask
Task → Candidate
Candidate → Constraint
Constraint → Candidate
```

**环只可能出现在「候选 ↔ 约束」子图上**，例如循环积分：两条分部积分各产出一条
构造约束，把两个候选互相定义为对方的表达式（§9.6）。

`Task.parent` 是单父指针的树，**永远无环**；环由 §5.4 的子项抽象把候选冻成符号
后，在约束系统上用代数求解消化掉——环存在于被求解的方程里，不在证明图上
（§9.5 的证明依赖图仍然无环）。`Constraint.sources` 因此必须能引用**候选**，
而不只是 Task（§8.6）。

### 3. 操作历史图

位于 workflow：

```text
Revision → Revision
```

用于：

- undo；
- redo；
- 从旧状态创建新分支；
- 隐藏或重新选择结果。

时间上的先后不自动成为数学依赖。

---

## 8.6 Constraint：计算构造方程

```python
@dataclass(frozen=True)
class Constraint:
    id: ConstraintId
    scope: ScopeId
    relation: Term
    sources: tuple[object, ...]           # TaskId | CandidateRef = (TaskId, ArtifactId)
    proposed_evidence: Evidence | None
```

`sources` 允许引用**候选**（`(task, artifact)`）：循环积分的构造约束是候选之间的
关系（§9.6「candidate(T0) = e^x sin x − candidate(T1)」），只指 Task 表达不了这个环。

`proposed_evidence` 是**候选凭据**，不是已验证的证据——它只是提交时准备交给
checker 的材料。Constraint 要成为 Judgment，仍须经 `kernel.commit` 并由 checker
接受（§6.9）；**带一个 Evidence 对象本身不构成任何验证**。

它用于表示：

```text
辅助未知量之间的代数关系
任务输出之间的构造关系
循环积分形成的方程组
```

Constraint 可能只是算法构造，不一定是可参与数学证明的 Judgment。

如果它经过 checker 并形成确切数学命题，才可以转成 Judgment。

---

## 8.7 Focus

```python
@dataclass(frozen=True)
class TargetRef:
    artifact: ArtifactId
    path: TermPath
    expected: Term
```

`expected` 防止路径过期。

Focus：

- 是会话状态；
- 不是上下文事实；
- 不产生数学结论；
- 不应进入 kernel。

---

## 8.8 Branch

```python
@dataclass(frozen=True)
class BranchCase:
    condition: Term
    scope: ScopeId
    task: TaskId

@dataclass(frozen=True)
class BranchGroup:
    parent_scope: ScopeId
    cases: tuple[BranchCase, ...]
    coverage: JudgmentId | None
```

每个 case 使用独立子作用域：

```text
Γ
├── Γ + [a ≠ 0]
└── Γ + [a = 0]
```

不能把分支上下文直接合并。

合并必须验证：

1. 分支覆盖父问题；
2. 每个分支回答同一个任务；
3. 分支结果各自在其 scope 中成立；
4. 辅助符号没有逃逸；
5. 分支开放条件被正确提升。

分支 \(C_i\) 中开放的守卫 \(G_i\)，提升到父层时是：

\[
C_i\Rightarrow G_i,
\]

而不是全局无条件要求 \(G_i\)。

---

## 8.9 Event 与历史

```python
@dataclass(frozen=True)
class Event:
    id: EventId
    command: str
    inputs: tuple[object, ...]
    outputs: tuple[object, ...]
    parent_revision: RevisionId
```

典型事件：

```text
CreateTask
CreateArtifact
CommitJudgment
OpenBranch
MoveFocus
SelectCandidate
AddConstraint
CloseTask
```

`outputs` 是本次操作产出的对象 id，**可以含内核 id**（`StepId` / `JudgmentId`）——
这是 workflow → kernel 的引用，方向合规（§四）。`CommitJudgment` 事件的 outputs
就是它提交出来的 Step 与 Judgment；`CreateArtifact` 的 outputs 是 Artifact。
于是「结论 ← 推理边 ← 操作」这条链在两边都走得通：内核侧 `Judgment.producer`
给出 Step，workflow 侧 Event.outputs 给出 Event。

**内核不反向引用**：`Step` / `Judgment` 里没有 `event_id`。想「从结论找回操作」，
查 workflow 侧的倒排索引，不要把这个字段塞进内核（那样 kernel 就认识 workflow 类型了）。

undo/redo 只是移动当前 revision 指针。

kernel store 和历史记录保持追加式，不物理删除旧结论。

---

# 九、未来工作流示例

## 9.1 `x/x → 1`

初始上下文：

\[
\Gamma=\{x\in\mathbb R\}.
\]

工作流：

```text
Artifact A0: x/x
        │
        │ apply rule field.cancel
        ▼
checker 验证规则实例
产生条件 x ≠ 0
        │
        ▼
decideΓ(x ≠ 0) = Unknown
        │
        ▼
Judgment J1:
Γ ⊢ x/x = 1 [x ≠ 0]

Artifact A1: 1
Candidate(A1, validation=J1)
```

如果进入分支：

```text
Γ₁ = Γ + [x ≠ 0]
```

则 `J1` 在 `Γ₁` 中直接可用。

如果进入：

```text
Γ₂ = Γ + [x = 0]
```

则 `J1` 在 `Γ₂` 中不适用，但不会从系统中删除。

---

## 9.2 分别计算 `A+B` 中的 `A` 和 `B`

> **本节为 `derivation` 模式示例，非默认路径。** 默认 `interactive` 模式下同一次计算不产生任何 Step/Judgment，只留下结果与未清偿条件。本节演示的是「要求留痕时留成什么样」，不是「化简平时怎么跑」。

初始 artifact：

```text
A0 = A + B
```

先聚焦左边：

```text
focus = TargetRef(A0, path=[0], expected=A)
```

某数学模块产生：

\[
\Gamma\vdash A=A'\;[G_A].
\]

语法替换得到候选：

```text
A1 = A' + B
```

但还不能仅凭 AST 替换声称它等于原式。

`Plus` 的同余 checker 产生：

\[
\Gamma\vdash A+B=A'+B\;[G_A].
\]

再处理右边：

\[
\Gamma\vdash A'+B=A'+B'\;[G_B].
\]

最后 equality 模块的传递规则产生：

\[
\Gamma\vdash A+B=A'+B'
\;[G_A,G_B].
\]

这说明：

- `replace_at` 负责语法；
- Plus 同余负责数学提升；
- 传递性负责等式链；
- 工作流负责焦点和顺序；
- 内核负责条件和依赖。

---

## 9.3 `A=B, B=C` 推出 `A=C`

> **本节为 `derivation` 模式示例，非默认路径。** 默认模式下传递由 equality 模块的闭包算法一次算完，不产生逐条 StepProposal。

已有：

\[
J_1:\Gamma\vdash A=B\;[G_1]
\]

\[
J_2:\Gamma\vdash B=C\;[G_2].
\]

调用普通规则：

```text
equality.trans
```

产生：

\[
J_3:\Gamma\vdash A=C\;[G_1,G_2].
\]

实现上：

```python
StepProposal(
    scope=gamma,
    premises=(J1, J2),
    conclusions=(Equal(A, C),),
    evidence=Evidence(
        checker_id="rule.instance",
        payload={
            "rule": "equality.trans",
            "subst": {"a": A, "b": B, "c": C},
        },
    ),
)
```

传递性属于 `math/base/equality.py`，不是内核关系注册表。

---

## 9.4 参数方程 `ax+b=0`

父任务：

```text
Task T0 = Solve(ax+b=0, x)
```

第一次分支：

```text
Γ
├── Γ₁ = Γ + [a ≠ 0]
└── Γ₂ = Γ + [a = 0]
```

在 `Γ₂` 再分：

```text
Γ₂
├── Γ₂₁ = Γ + [a=0, b=0]
└── Γ₂₂ = Γ + [a=0, b≠0]
```

各分支产生：

```text
Γ₁   ⊢ CompleteSolution(T0, x=-b/a)
Γ₂₁  ⊢ CompleteSolution(T0, all real x)
Γ₂₂  ⊢ CompleteSolution(T0, no solution)
```

coverage judgment：

```text
a≠0 ∨ a=0
b=0 ∨ b≠0
```

经过 branch merge checker 后，可以输出：

```text
a ≠ 0           → x = -b/a
a = 0 ∧ b = 0   → x 任意
a = 0 ∧ b ≠ 0   → 无解
```

工作流本身不强制把它编码成 `Piecewise`。方程模块可以选择：

- 条件列表；
- `Piecewise`；
- 逻辑公式；
- replacement rules。

---

## 9.5 循环定积分方程

定义：

\[
I(x):=\int_0^x e^t\sin t\,dt,
\qquad
J(x):=\int_0^x e^t\cos t\,dt.
\]

`I`、`J` 是作用域内的普通定义。

第一次分部积分：

\[
p_1:
I(x)=e^x\sin x-J(x).
\]

第二次分部积分：

\[
p_2:
J(x)=e^x\cos x-1+I(x).
\]

两条都由定积分分部积分规则实例 checker 验证。

然后语法抽象：

```text
I(x) → u
J(x) → v
```

方程组：

```text
u = e^x sin(x) - v
v = e^x cos(x) - 1 + u
```

代数求解器得到：

\[
u=\frac{e^x(\sin x-\cos x)+1}{2}.
\]

代数 checker 可以通过多项式标准形验证该结论由 `p1,p2` 推出。

证明依赖图是：

```text
              p1 ─────┐
定义 I,J ────          ├── algebraic elimination ── p3
              p2 ─────┘
```

没有证明环。

循环只存在于被求解的代数方程中。

---

## 9.6 不定积分循环计算

对于：

\[
\int e^x\sin x\,dx
\]

不要引入 `EqC` 或 `IntegrationConstant`。

创建任务：

```text
T0 = FindAntiderivative(e^x sin x, x)
```

该任务的候选规格是：

\[
\operatorname{CandidateSpec}(F)
\equiv
D_xF=e^x\sin x.
\]

手动分部积分可以把它分解为另一个子任务：

```text
T1 = FindAntiderivative(e^x cos x, x)
```

以及候选构造：

```text
candidate(T0) = e^x sin x - candidate(T1)
```

第二次分部积分形成：

```text
candidate(T1) = e^x cos x + candidate(T0)
```

这两个是任务构造约束，不是“任意两个不定积分对象之间的普通等式”。

冻结两个候选占位符并代数求解，得到：

\[
F=\frac12e^x(\sin x-\cos x).
\]

最终可信结论是：

\[
D_xF=e^x\sin x.
\]

如果用户希望显示传统答案，前端可以打印：

\[
\int e^x\sin x\,dx
=
\frac12e^x(\sin x-\cos x)+C.
\]

但 `C` 是普通参数，传统显示不参与内核语义。内核真正持有的是原函数候选及其导数验证。

---

## 9.7 ODE `y'=y`

任务：

```text
T0 = SolveODE(y'(x)=y(x), y, x)
```

算法产生 artifact：

```text
A1 = y(x) = c*exp(x)
```

其中作用域声明：

```text
c ∈ ℝ
c independent of x
```

没有 `ODESolutionConstant` 类型。

回代 checker 产生：

```text
J1:
SatisfiesODE(y'=y, y=c*exp(x))
```

这只验证了解族中的每个成员是解。

如果 ODE 模块另有完备性定理和证书，再产生：

```text
J2:
CompleteSolutionFamily(y'=y, {c*exp(x) | c∈ℝ})
```

如果只有 `J1`，UI 应明确显示：

```text
已验证解族；未验证其完备性
```

而不是把 `complete=False` 隐藏起来。

这也自然避免：

\[
y=e^{x+C}
\]

漏掉零解、负系数解的问题。

---

# 十、可信边界

## 10.1 可信部分

```text
syntax 的绑定与代换
kernel 的 scope/commit/requirement 规则
RuleSchema 库
checker 实现
精确域算术
证书验证所依赖的判等器
checker 所依赖的独立设施（§7.3）：
    微分器
    域标准形
    恒等判定
    定义域分析
```

这些出现 bug 会影响系统正确性。

最后一项必须显式列出，不能省：`Risch 找到 F → checker 证明 D(F)=f`（§7.3）里，
`D(F)=f` 是候选正确性的**唯一**保证，微分器出错则整条链失守。同理，恒等判定与
定义域分析出错会让「已验证」变成假象。它们与搜索算法**独立**（这是 §7.3 的要求），
但独立不等于不需要正确——独立解决「不自证」，可信解决「值得信」，两件事都要。

## 10.2 不可信部分

```text
启发式化简器
积分搜索器
Risch 主算法
ODE 分类器
方程求解策略
自动 tactic/planner
UI
任务调度
```

这些可以给错候选，但不能直接创建可信 Judgment。

---

# 十一、从 v3 到 v4 的迁移方案

## 第一阶段：拆语法，不改变行为

当前 `term.py` 同时包含驻留项、模式变量和显示逻辑；先迁移为：

```text
syntax/term.py
syntax/binder.py
syntax/path.py
syntax/pattern.py
syntax/match.py
frontend/pretty.py
```

重点先把：

```text
PatVar
PatSeq
```

移出 `Term`。

---

## 第二阶段：引入新内核模型，包裹旧验证器

新建：

```text
kernel/scope.py
kernel/model.py
kernel/evidence.py
kernel/store.py
kernel/commit.py
```

暂时将旧 `_verify_diff`、`_verify_integrate` 等包装为 checker adapter。

这一步不必先重写积分和求解算法。

---

## 第三阶段：拆除封闭 Derivation ADT

当前工作流中的 `Claim/BothSides/Rewrite/Solve/Split/Subst/Diff/Integrate` 是功能封闭点，且 `_verify` 通过 `isinstance` 集中分派。

替换为：

```text
StepProposal
Evidence(checker_id, payload)
CheckerRegistry
```

先保留旧命令名称，但命令只负责生成 proposal。

---

## 第四阶段：区分 Artifact、Task 和 Judgment

将旧 Step 的“内容”拆成：

```text
Artifact    计算产物（无真假，免费）
Judgment    已验证结论（**可选**，只在边界产生）
Step        推理边（只有提交才产生）
```

求导产生 **Artifact**：

```text
Artifact: 2x
```

**Artifact 即可直接参与后续计算**——后续计算也是重写，重写吃项，不吃结论。
Judgment 是**可选的**（§8.4 `validation: JudgmentId | None`），只在三种情况下产生：

```text
要对外断言这个结果
结果出自不可信算法，需要边界复核
该步产生了条件（Requirement）
```

不要为每个计算结果都配一张 Judgment。**热循环跑在 Artifact 上，可信结论只在
边界 commit 一次**（AGENTS.md §四.1）；把每一份算出来的表达式都送进账本，等于
把内核放回内循环——那正是把它变回定理证明器的做法。

---

## 第五阶段：建立持久化 Scope

用父指针和 delta 替代 mutable clone：

```text
root
├── scope + assumption a≠0
└── scope + assumption a=0
```

旧 Context 可以暂时作为 `TrackedContext` 的后端，随后替换。

---

## 第六阶段：迁移数学模块

推荐顺序：

```text
math/base
→ arithmetic
→ domains
→ differentiation
→ equations
→ piecewise
→ integration
→ inequalities
→ ODE
```

Risch 最后进入，因为它依赖域塔、因式分解和线性代数。

---

# 十二、v4 必须强制的架构不变量

建议直接写成测试和 CI 规则。

1. `Term` 不包含 context、guard、proof 字段。
2. Pattern 不是 Term。
3. 只有 `kernel.commit` 能创建 Judgment。
4. Artifact 不能作为数学 premise。
5. 开放 Requirement 不能自动进入 Scope.assumptions。
6. checker 返回的条件必须由 kernel 记录。
7. checker 对 Context 的读取必须进入 `read_set`。
8. 子作用域结论不能直接在父作用域使用。
9. 兄弟分支不能互相读取事实。
10. branch merge 必须有覆盖依据。
11. 数学依赖图必须无环。
12. 工作流任务图可以包含循环构造，但不能冒充证明图。
13. 算法不能导入 kernel store 并直接写结论。
14. 对应 checker 不能导入自身求解算法。
15. 局部辅助符号不得逃逸。
16. 未验证候选不能参与可信推导。
17. graph reachability 不能被解释为 equality。
18. 自动化简默认不应用未证明的条件规则。
19. 手动显式规则允许产生条件性 Judgment。
20. 每个求解结果必须明确它证明的是“候选正确”还是“结果完备”。

---

# 十三、验收方法论

以下七件构成完整的裁判标准：

- **随机性质测试**：生成器构造已知答案的表达式，用域判定器验证性质，全部自证、无外部真值。当前四十一条（P1–P41），以 pytest 收集层（`tests/random/test_random.py`）统一驱动、CI 守门
- **差分生成器**（积分阶段启用）：随机生成初等函数 F，要求 integrate(dF/dx)，且结果求导回到 F。覆盖率的唯一来源
- **回代判官**：验证系统的原子，已建
- **验证独立性**：每条推导类型的验证器必须与被验证算法实现不共享代码路径
- **钉子库**：退化形态与修过的 bug 逐个固化成测试，持续积累
- **符号反证**：系统给出否定结论时，用符号方法生成候选反例逐一排除，保证否定可靠
- **文档现实锁定**：文档声称存在的模块，磁盘上必须有

---

# 十四、最终概括

pyCAS v4 的中心不应该是一个“万能重写器”，也不应该是一个按功能增长的 `Derivation` 类型系统。

它的中心应当是：

```text
纯语法 Term
+
持久化 Scope
+
条件性 Judgment
+
证据检查与 Requirement 生命周期
+
独立的任务/历史工作流
+
插件化数学模块
```

最关键的四条边界是：

1. **项不带守卫，结论带条件。**
2. **数学模块产生守卫，内核管理守卫。**
3. **工作流组织计算，内核登记真结论。**
4. **算法产生候选，checker 决定能声称什么。**

这样增加积分、ODE、不等式、线性代数、级数或求和时，变化主要发生在 `math/`；而 `syntax/`、`kernel/` 和 `workflow/` 保持稳定。