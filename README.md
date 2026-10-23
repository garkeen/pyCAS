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

当前可用的数学能力只有 **Q 上的单变量多项式求导**（变量为 `x`）。代数层另提供
ℤ、ℚ、K[x₁…xₙ]、K(x) 的精确结构供程序化使用。片段外（例如 `1/x`）一律诚实拒答，
不会伪造答案，也不会写入账本。

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
| `show [@LABEL]` | 显示对象 |
| `list` | 列出当前 revision 中的对象 |
| `undo` / `redo` | 移动视图指针；账本不回滚 |
| `help` / `quit` | 帮助 / 退出 |

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

---

## 目录

| 路径 | 内容 |
|---|---|
| `cas/foundation/` | 互不混用的身份类型与 issuer |
| `cas/syntax/` | 不可变 Term、结构相等/hash/序、de Bruijn 绑定原语 |
| `cas/language/` | Sort、结构签名、定型、Proposition、ProblemSpec、三值 Verdict |
| `cas/algebra/` | 结构协议、parent 描述、ℤ、ℚ、多项式环、有理函数域 |
| `cas/semantics/` | World/Frame、符号表、定义展开、Term↔元素桥、微分结构 |
| `cas/kernel/` | Judgment/Obligation/InferenceRecord、checker 协议、原子账本、commit |
| `cas/math/` | 数学规格与独立 checker（当前仅多项式求导） |
| `cas/workflow/` | 表达式对象、候选、验证关联、事件与 revision |
| `cas/runtime/` | 显式装配的 Runtime 与 workspace 入口 |
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
