# pyCAS

一个**纯符号**的计算机代数系统（Python 实现，运行时零第三方依赖）。

方法论：**只做可判定的内容，片段外诚实拒答。** 求解器只产生候选，独立验证器复核，
可信结论只在一次边界提交中发行；未决永远不会被静默当成 Yes 或 No。

项目正在按 v5 架构彻底重构。设计裁定见 `cas_v5_arch.md`，工程纪律见 `AGENTS.md`，
当前进度见 `progress.md`。

---

## 当前状态

第一条纵线已贯通：

```text
文本 → Term → 求导候选 → HasDerivative 规格 → 独立系数级验证
     → kernel 原子发行 → 工作流记录 → 会话显示 / undo / redo
```

当前可用的数学能力：

- **Q 上的单变量多项式求导**；
- 它的参数化版本 **Q[a…][x]**：形式参数作为系数环的生成元，`x` 仍然是求导目标，
  两个角色由请求显式固定。参数族结果携带有效区域、异常集与覆盖声明；多项式求导
  不引入分母或分支，因此默认的 `AllParameterValues` 请求可以得到无条件覆盖。精确
  有理参数点可以特化，结果在 Q[x] 中由独立 checker 重新验证；
- 由数据声明的**初等函数片段**：`sin`、`cos`、`exp` 及其导数定律来自
  `cas/math/elementary/declarations.dsl`，支持和、积、非负整数幂与链式法则。
  `sqrt`、`log` 的条件定律与函数定义域会生成显式的可微区域；结果在
  `HasDerivative(region, …)` 中发行，并显示为 `verified on …`，不会伪装成全域结论。

片段外（例如 `1/a`、`1/x`、未声明符号或区域为空的条件）一律诚实拒答，不会伪造
答案，也不会写入账本。

v4 的 CAD、积分、方程求解、实根隔离、规则引擎等实现已删除；它们会在 v5 地基上
重新落地，而不是以兼容层迁回。旧代码仍可从 git 历史中查阅。

---

## 快速开始

```console
$ python repl.py
pyCAS v5 — polynomial and elementary differentiation. Type help for commands.
cas> x^3 - 3*x
@E0: x^3 - 3*x
cas> diff
verified @E1: -3 + 3*x^2
cas> sin(x)
@E2: sin(x)
cas> diff
verified @E3: cos(x)
cas> sqrt(x)
@E4: sqrt(x)
cas> diff
verified on x > 0 @E5: 1/2*sqrt(x)^-1
cas> 1/x
@E6: x^-1
cas> diff
unsupported: only nonnegative integer powers are differentiated
```

命令：

| 命令 | 作用 |
|---|---|
| `<expr>` | 存入一个表达式对象（不产生判断） |
| `expr LABEL := <expr>` | 带标签存入 |
| `assume FORMULA` | 在子 frame 中引入一条假设，并发行 `H ⊢ H` |
| `diff [@LABEL]` | 对焦点或指定对象求导，候选须通过独立验证 |
| `specialize [@LABEL] a=VALUE …` | 用精确有理值特化已验证的参数族，并在 Q[x] 中重新验证 |
| `show [@LABEL]` | 显示对象 |
| `list` | 列出当前 revision 中的对象 |
| `undo` / `redo` | 移动视图指针；账本不回滚 |
| `help` / `quit` | 帮助 / 退出 |

默认 REPL 装配的是 `bootstrap_elementary()`（多项式是它的子片段）。参数化运行时通过
`bootstrap_parameterized` 在 Python API 中使用；REPL 的参数化入口尚未实现。

程序化使用：

```python
from cas.frontend import Session
from cas.runtime import bootstrap

runtime = bootstrap()
session = Session(runtime)
session.execute("expr F := x^3 - 3*x")
result = session.differentiate(session.object("F"))
assert result.verification is not None
assert result.verification.judgment is not None
```

`Workspace` 也可以直接使用：`workspace.intake(term)` 只记录对象，
`workspace.differentiate(expression, runtime.variable)` 负责候选、规格、提交与关联。

### 参数化的系数

```python
from cas.frontend import Session
from cas.runtime import bootstrap_parameterized

runtime = bootstrap_parameterized(("a",))  # Q[a][x]
session = Session(runtime)
session.execute("expr F := a*x^2")
assert session.execute("diff @F") == "verified @E0: 2*a*x"
```

这里 `a` 是系数环 Q[a] 的生成元，`x` 是目标；`AlgebraRequest` 固定两者的角色，
同一个符号可以在另一个请求里成为目标。参数族结果记录 `valid_on`、异常集、正确性
规格与覆盖声明；默认请求 `AllParameterValues`，多项式求导因无分母与分支而得到
`ALL_VALUES` 覆盖。也可以用 `bootstrap_parameterized(..., parameter_mode=
ParameterMode.GENERIC_PARAMETERS)` 只声明形式族结果。

```python
session.execute("expr F := a*x^2")
session.execute("diff @F")           # verified @E0: 2*a*x
session.execute("specialize @F a=3") # verified @E1: 6*x
```

特化只接受**全部参数**的精确有理值。它先检查有效区域与异常集；没有例外且条件可判时
代入泛参数公式，否则回到原问题在 Q[x] 中重算，绝不把未决条件当成成立。特化后的
源与候选都经 Q[x] 的独立 checker 验证后才提交。非有理参数点、缺失参数或片段外
输入一律诚实拒答。

### 初等函数声明

`cas/math/elementary/declarations.dsl` 是 data-only 的数学声明：

```text
constant pi : Real
function sin : Real -> Real
function sqrt : Real -> Real on u >= 0
derivative sin(u) = cos(u)
derivative sqrt(u) = (1/2)*sqrt(u)^(-1) on u > 0
```

装配器把文件作为受信任的 basis 读入；用户公理来源的定律不会自动用于求导。
`bootstrap_elementary()` 是默认 REPL 运行时：

```python
from cas.frontend import Session
from cas.runtime import bootstrap_elementary

session = Session(bootstrap_elementary())
assert session.execute("sin(x^2)") == "@E0: sin(x^2)"
assert session.execute("diff") == "verified @E1: 2*cos(x^2)*x"
```

候选生成器与 checker 是两个独立实现：checker 不调用候选生成器，只按同一声明数据
重建期望导数与区域；结构不同但可能等价的候选或区域返回 `unverified`，不会被伪装成
否证。条件计算区分**定义域**与**可微区域**：

- `sqrt(0)` 的导数 0 在定义域 `x >= 0` 上已成立，因此是无条件结果；
- `sqrt(x)` 的导数只在 `x > 0` 上成立，结果以 `HasDerivative(x > 0, …)` 发行；
- `sqrt(-1)`、`log(0)` 的可微区域为空，诚实拒答；
- 条件合取会做精确的真假折叠、线性边界规范化、矛盾检测与结构去重；未知条件保持
  显式，不自动当成成立。

工作流的 `OperationStatus.CONDITIONAL`、`DerivativeResult.condition` 与
`VerificationLink.condition` 记录受限区域；kernel 的 judgment 本身是在该区域上
无条件成立的规格，而不是把全域结论挂上一条说明。条件区域仍写进规格；kernel 的
假设、条件检查与 `resolve_applicability`/原子 discharge 机制单独用于显式前提和
将来会产生 obligation 的算法，不用于伪造全域导数结论。

条件服务还提供受限的规范化与蕴含/等价判定：一原子线性比较会化成边界
（`x >= 0 and x > 0` 化为 `x > 0`），矛盾边界化为 `false`，重叠边界取最强；
checker 接受结构不同但被证明等价的区域。未知原子、跨原子关系与非线性关系不做
猜测，保持未决。当前限制：初等片段仍只支持一元函数与非负整数幂；条件服务只支持
线性单原子比较、受限的命题连接词与保守的 Or/Not 处理；没有一般的一阶判定或
kernel 义务自动清偿。

语言层另有 data-only 声明 DSL（`operator` / `binder` 签名）与 binder 定型：
`BindingSignature` 声明参数 sort 与结果，函数值 binder 定型为 `FunctionSort`，
值 binder 要求 body 嵌入结果。前端 binder 输入语法尚未接入。

### 假设、条件与适用性

`assume FORMULA` 在当前 frame 下解析并发行命题，然后创建一个包含该假设的子 frame，
并用 core hypothesis checker 发行 `H ⊢ H`。之后的对象与判断使用当前 revision 的
frame；`undo`/`redo` 会连同 frame 一起移动，账本不回滚。

```python
session.execute("assume x > 0")
session.execute("sin(x)")
session.execute("diff")
```

kernel 还提供 `ConditionChecker`（`logic.condition`）与
`resolve_applicability`：前者用受限蕴含服务从前提判断证明条件，并只报告实际使用的
前提；后者尝试为未决 obligation 生成证明，并在**同一个 commit 批次**中发行证明
Judgment 与 discharge（循环与前提闭合检查在发布前完成）。证明失败、前提不足或
超过预算时保持 `Conditional`，不会返回虚假的 `Applicable`。

### 一致性、信任与失效

frame 一致性是显式状态，而不是“没发现矛盾就等于一致”：

- `Unassessed` 是默认状态；`ConsistentForFragment` 必须给出片段说明以及证据判断
  或 `BasisRef`；`Inconsistent` 必须引用一条已发行的闭合 `false` 判断。
- 核心矛盾规则只在 frame 链上可见的假设出现 `H` 与 `not H`（或直接假设 `false`）
  时发行 `false`。祖先假设按 §6.3 的弱化进入后代；兄弟 frame 之间不互相可见。
- 在已判定不一致的 frame（或其后代）中，`commit` 拒绝发行，`assume`、`diff`、
  `specialize` 都会停止并报告。撤销/重做只移动 revision，矛盾证明仍留在账本中。

checker 注册现在是 `CheckerSpec`，显式绑定证书 schema、接受的 problem /
specification 种类、验证函数与可信依赖。可信依赖用 `BasisRef` 记录种类、版本、
世界作用域和内容摘要；每次 `InferenceRecord` 记录该次推理实际使用的 basis。
初等声明文件在装配期以 `declarations.dsl` 的 SHA-256 摘要登记为
`DECLARATION_FILE` basis。结构性的证书校验仍由 checker 的 `InvalidEvidence`
负责；证书大小/深度预算尚未接入本文档所称的 schema 门限。

适用性增加 `Blocked`：当某个未决义务的否定已由可见闭合判断证明时，该判断不能
应用，但这**不**表示结论为假。`commit` 对已否定条件返回 `Rejected`，并区分
`refuted_conditions`（应用所需条件被否定）与 `refutation`（结论本身被否定）。

## 目录

| 路径 | 内容 |
|---|---|
| `cas/foundation/` | 互不混用的身份类型与 issuer |
| `cas/syntax/` | 不可变 Term、结构相等/hash/序、de Bruijn 绑定原语 |
| `cas/language/` | Sort、结构签名、定型（含 binder）、Proposition、ProblemSpec、三值 Verdict、声明 DSL |
| `cas/algebra/` | 结构协议、parent 描述、ℤ、ℚ、多项式环、有理函数域 |
| `cas/semantics/` | World/Frame、符号表、定义展开、AlgebraRequest 角色、参数特化/覆盖、条件求值、注入的求导服务、Term↔元素桥（含参数系数）、微分结构 |
| `cas/kernel/` | Judgment/Obligation/InferenceRecord、BasisRef/CheckerSpec、假设与矛盾规则、条件 checker、一致性状态、原子账本、commit、Blocked/适用性解析 |
| `cas/math/` | 数学声明与独立 checker：多项式求导、data-only 初等函数声明与符号求导 |
| `cas/workflow/` | 表达式对象、候选、验证关联、事件、revision、frame 作用域假设 |
| `cas/runtime/` | 显式装配的 Runtime（Q[x]、参数化 Q[a…][x]、Q[x] 特化视图与初等函数片段）与 workspace 入口 |
| `cas/frontend/` | parser、printer、Session、REPL |

依赖方向：`syntax → language → algebra → semantics → kernel → workflow → frontend`；
装配只在 `runtime/bootstrap.py` 发生，import 期不修改全局状态。

---

## 验收

```console
python -m pytest -q                 # 行为测试 + 固定种子性质测试
python -m mypy --strict cas         # 类型检查
python -m ruff check cas tests      # 静态风格与未使用导入
python -m compileall -q cas         # 字节码编译
```

测试按 `tests/unit`、`tests/integration`、`tests/property` 分类，只做行为与性质验收；
没有按标识符、字符串、import 面或 AST 名字判断设计的门禁。

---

## 文档

| 文件 | 作用 |
|---|---|
| `cas_v5_arch.md` | 架构裁定：对象模型、依赖方向、数学与工作流语义 |
| `AGENTS.md` | 工程纪律：六条硬约束与验收边界 |
| `progress.md` | 当前进度、已知缺口、下一步 |
| `reference.md` | 参考实现索引（Maxima、FriCAS 等） |
| `risch.md` / `cad.md` / `maple.md` / `mathematica.md` | 目标与参考系统笔记 |

---

## 目标

三项地基目标：

1. **完整 Risch 积分**（参数与超越数积分，参照 FriCAS）；
2. **完整 Gröbner 基**（多元多项式理想论：属员、方程组、消元）；
3. **完整 CAD**（多变量实代数投影 + 胞腔分解 + 量化消去）。

方法尚未裁定的占位方向：ODE/PDE 符号求解、丢番图整数解。裁定前不立项。

节奏：先让一条纵线完整贯通，再横向长能力；能力缺失时拒答，不用猜测填充。
