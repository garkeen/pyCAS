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

当前可用的数学能力是 **Q 上的单变量多项式求导**，以及它的参数化版本
**Q[a…][x]**：形式参数作为系数环的生成元，`x` 仍然是求导目标，两个角色由请求
显式固定。参数族结果携带有效区域、异常集与覆盖声明；多项式求导不引入分母或分支，
因此默认的 `AllParameterValues` 请求可以得到无条件覆盖。精确有理参数点可以特化，
特化结果在 Q[x] 中由独立 checker 重新验证。片段外（例如 `1/a` 或非多项式输入）
一律诚实拒答，不会伪造答案，也不会写入账本。

v4 的 CAD、积分、方程求解、实根隔离、规则引擎等实现已删除；它们会在 v5 地基上
重新落地，而不是以兼容层迁回。旧代码仍可从 git 历史中查阅。

---

## 快速开始

```console
$ python repl.py
pyCAS v5 — polynomial differentiation. Type help for commands.
cas> x^3 - 3*x
@E0: x^3 - 3*x
cas> diff
verified @E1: -3 + 3*x^2
cas> undo
undo: @E0
cas> list
> @E0: x^3 - 3*x
cas> 1/x
@E2: x^-1
cas> diff
unsupported: the source is outside the polynomial fragment
```

命令：

| 命令 | 作用 |
|---|---|
| `<expr>` | 存入一个表达式对象（不产生判断） |
| `expr LABEL := <expr>` | 带标签存入 |
| `diff [@LABEL]` | 对焦点或指定对象求导，候选须通过独立验证 |
| `specialize [@LABEL] a=VALUE …` | 用精确有理值特化已验证的参数族，并在 Q[x] 中重新验证 |
| `show [@LABEL]` | 显示对象 |
| `list` | 列出当前 revision 中的对象 |
| `undo` / `redo` | 移动视图指针；账本不回滚 |
| `help` / `quit` | 帮助 / 退出 |

默认 REPL 装配的是 Q[x]。参数化运行时通过 `bootstrap_parameterized` 在 Python API
中使用；REPL 的参数化入口尚未实现。

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

语言层另有 data-only 声明 DSL（`operator` / `binder` 签名）与 binder 定型：
`BindingSignature` 声明参数 sort 与结果，函数值 binder 定型为 `FunctionSort`，
值 binder 要求 body 嵌入结果。前端 binder 输入语法尚未接入。

---

## 目录

| 路径 | 内容 |
|---|---|
| `cas/foundation/` | 互不混用的身份类型与 issuer |
| `cas/syntax/` | 不可变 Term、结构相等/hash/序、de Bruijn 绑定原语 |
| `cas/language/` | Sort、结构签名、定型（含 binder）、Proposition、ProblemSpec、三值 Verdict、声明 DSL |
| `cas/algebra/` | 结构协议、parent 描述、ℤ、ℚ、多项式环、有理函数域 |
| `cas/semantics/` | World/Frame、符号表、定义展开、AlgebraRequest 角色、参数特化/覆盖、Term↔元素桥（含参数系数）、微分结构 |
| `cas/kernel/` | Judgment/Obligation/InferenceRecord、checker 协议、原子账本、commit |
| `cas/math/` | 数学规格与独立 checker（当前仅多项式求导） |
| `cas/workflow/` | 表达式对象、候选、验证关联、事件与 revision |
| `cas/runtime/` | 显式装配的 Runtime（Q[x]、参数化 Q[a…][x] 与特化 Q[x] 视图）与 workspace 入口 |
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
