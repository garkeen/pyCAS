# pyCAS

一个**纯符号**的计算机代数系统（Python 实现，运行时零第三方依赖），提供**自动**与
**交互**两条通道。

方法论一句话：**只做可判定的内容，片段外诚实未决。**

- 自动化通道一律经 `Verdict` 出口：`Yes / No / Unknown(FRAGMENT | GUARDED |
  UNDECIDABLE | BUDGET)`。未决永远不会被静默当成 Yes 或 No，能力缺失时宁可可
  证地拒答（`raise ...Error`），也不给一个看起来像结论的猜测。
- **求解器与验证器分家**：求解器（tactics / integrate / cad）只产出候选，验证器
  （judge / calculus/*/verify）独立复核后才允许成为可信结论；checker 不得导入它
  所验证的搜索算法。
- 计算一律降为**域元素上的显式代数运算**（±×÷、gcd、求导、结式、投影判等），
  不做数值采样冒充证明、不做形状猜测。

> **项目仍在长期更新中。** 接口会随架构演进而调整（例如数学上下文现在是每个算
> 法的显式首参数），当前不承诺 API 稳定；以 `progress.md` 与 `cas_v4_arch.md`
> 为准。

---

## 一、能力现状（速览）

**已经能做的事**

| 领域 | 内容 |
|---|---|
| 项与模式 | 驻留（hash-consing）项层 + AC 规范形；模式元语言与项层分离（`PatternVar`/`PatternSeq` 不是项）；基于 de Bruijn 索引的绑定与实例化 |
| 数域 | ℤ、ℚ、ℚ(i)、K[x]、K(x)，带能力字段（`is_field` / `is_ordered` / `is_euclidean` / 导子…）与投影阶梯；精确有理字面算术 |
| 判定 | 三值判定管线：指针/数值 → 账本 → 投影判零 → 区间传播 → 序链推理 → 派生规则 → 声明引理 |
| 内核 | 追加式账本；作用域**版本链**（Γ 冻结、谱系与版本分离）；条件生命周期（清偿与否证）；十步 `commit` 及其可证明的四步特化；真 undo/redo（只移指针、不删历史） |
| 符号计算 | 声明化规则引擎（行式 DSL，auto 规则无守卫并按成本严格下降终止）；微分（含分段谨慎通道，分段点显式标注未验证）；多项式片段积分与三值独立验证；一维 CAD（Sturm 实根隔离）；线性方程组/线性代数（行阶梯、秩、核、Bareiss 行列式）；结式与 Yun 无平方分解；线性丢番图碎片与整数根 |
| 分段 | 有序首中语义的分段容器、逐支投影、提升（带预算与相邻同值支合并）、覆盖/冲突检查、分段方程求解、定义域条件 |
| 交互 | REPL：断言/化简/求解/代入/分支/diff/integrate/check/steps/undo |

**尚未实现（遇到就诚实拒答，不是 bug）**

完整 Risch 积分（参数与超越数积分）、完整 CAD（多变量实代数投影 + 胞腔分解）、
Gröbner 基方法、三角/指数展开与同类项收集、部分分式与 Hermite 归约、Zassenhaus
因式分解、超越根对象与条件答案容器、工作流序列化与回放。

> 举例：`∫exp(x)·sin(x)dx` 这样的循环积分目前会停在「未决」——微分层能验证它，
> 但判零通道还不能把差值展开为零。这类能力缺口会如实报告为 `Unknown(FRAGMENT)`。

---

## 二、快速上手

### 环境

- **Python ≥ 3.10**（开发用 3.12）；
- **运行时零第三方依赖**（只用标准库）；
- 跑测试需要 `pytest`（`pytest.ini` 里配置了 `timeout`，因此还需 `pytest-timeout`）。

不需要安装，直接在仓库根目录运行即可（`cas` 是普通包）。

### 交互使用

```console
$ python repl.py
pyCAS REPL. Type 'help' for commands.
> x^2 - 1 == 0        # 直接输入表达式/方程 = 断言进账本（Claim）
> solve x             # 线性求解：战术层给候选，checker 独立回代判定后才 commit
> check               # 对当前解做回代验证
> diff x              # 求导（域层导数交叉验证）
> integrate x         # 多项式片段不定积分（独立验证 d/dx F = f）
> int x 0 1           # 定积分（端点差 + 独立复核）
> norm                # 域标准形
> steps               # 列出当前视图中的步骤
> undo                # 真 undo：回退一步事件指针（记录不删）
> rules / apply <id>  # 列出、应用声明规则
> help / quit
```

要点：

- 每一步都会显示状态（`committed` / `refused` / `undecided`）与步骤号；`refused`
  表示被独立验证器否证，`undecided` 表示验证通道覆盖不到（**不是**「错」）。
- 除上面的命令外还有：`both add|sub|mul|div <expr>`（两边同时操作）、
  `subst <var> = <expr>`、`split <cond>`（分支，前置 `!` 取否定支）。

### 程序化使用

```python
from cas.runtime import bootstrap
from cas.runtime.dispatch import install

install(bootstrap())          # 显式装配：import 期不修改任何全局状态

import cas.api as api
from cas.frontend.parser import parse

api.differentiate(parse("x^2"), parse("x"))          # 求导
api.solve_linear(parse("2*x + 3 == 7"), parse("x"))  # 线性求解
api.integrate_term(parse("x^2"), parse("x"))         # 不定积分
api.guard_report([parse("x > 0")], parse("x"), parse("2"))   # 逐条守卫判定
```

三点约定：

1. **`cas/api.py` 是前端门面**：前端（含 REPL）只经 `api` / `workflow` / `runtime`
   触达计算，不直接 import `cas.math`。
2. **算法层一律以数学上下文为第一参数**（`MathContext`，含声明查询面与装配期配置）。
   门面会替你注入；直接调 math 层时显式传：
   ```python
   from cas.runtime import get_runtime
   from cas.kernel.scope import Assumptions
   from cas.math.decide import decide

   decide(get_runtime().math, parse("x > 0"), Assumptions())
   ```
   这样「忘了装配」不会变成深层算法里的运行时惊喜，而是调用点就写不出来。
3. **未装配就读语义会报错**：必须先 `install(bootstrap())`（REPL 入口已自动完成）。

---

## 三、目录结构

| 路径 | 内容 | 依赖方向 |
|---|---|---|
| `cas/syntax/` | 驻留项、模式元语言、匹配、项路径、抽象 | 只依赖标准库 |
| `cas/kernel/` | `Verdict`、模型（Judgment/Scope/…）、证据、`commit`、账本、检查器注册表 | 只依赖 `syntax` |
| `cas/workflow/` | 工作流、命令、Artifact/Task/Event 三图、分支 | 依赖 `syntax` + `kernel` |
| `cas/math/domains/` | ℤ、ℚ、ℚ(i)、K[x]、K(x) 与域协议、线性代数 | 依赖 `syntax` |
| `cas/math/` | `context`、`project`、`decide`、`diff`、`integrate`、`cad`、`tactics`、`piecewise`、`domcond`、`rules`、`simplify`、`judge`、`constraints`、`loader` 与 `base/` `elementary/` `calculus/` `solving/` | 依赖 `syntax`+`kernel`+`workflow`+`math.domains`；**永不**导入 runtime |
| `cas/runtime/` | 装配：`registry`（Builder）→ `runtime`（只读 Runtime）→ `bootstrap` → `dispatch` | 唯一装配者 |
| `cas/frontend/` + `cas/api.py` | 解析器、打印器、REPL；计算门面 | 只经 `api` / `dispatch` |

依赖方向由 CI 门禁机械检查（`tests/contract/test_v4_invariants.py`），不靠人工审查。

---

## 四、测试

```console
pytest tests                 # 全部：确定性钉子 + 10 个随机自证台架
pytest -m random             # 只跑随机台架（数学性质是否出错）
pytest -m "not random"       # 只跑确定性钉子（结构与契约是否退化）
pytest tests/contract        # 架构门禁：依赖方向、不变量、DSL 准入、语言纪律
pytest tests/unit -q         # 单模块行为
```

测试按种类分目录、按 marker 可筛（`unit` / `contract` / `integration` /
`regression` / `random`）：

- `tests/random/` 是**自证性质的随机台架**：机器生成实例、机器验证数学性质
  （无外部真值），直接 `python tests/random/random_diff.py [rounds] [seed]` 也能
  单独跑，失败会打印最小反例与种子。
- `tests/regression/` 是「钉子」：每个文件钉一个曾经出过的缺陷。
- `tests/contract/` 是架构门禁，例如：内核不含数学 head 字面量、checker 不导入
  自己的求解器、math 层不得持有模块级装配状态、被删的装配句柄不得回潮、源码
  只写英文且不得引用设计文档。

---

## 五、文档地图

| 文件 | 作用 |
|---|---|
| `progress.md` | **当前进度与下一步**：已实现地基、未实现清单、已知缺陷 |
| `cas_v4_arch.md` | **设计裁定**：对象模型、依赖方向、算法语义（有争议时以此为准） |
| `AGENTS.md` | **工程纪律**：六条硬约束与各章门限（实现前先读） |
| `reference.md` | 参考实现索引（主要权威：Maxima、FriCAS） |
| `maple.md` / `mathematica.md` | 参考系统笔记 |

---

## 六、长期更新中

本项目是长期工程，按「先地基、后功能」的节奏推进，**目标是三项，其余功能都建立
在这三项之上**：

1. **完整 Risch 积分**（参数积分与超越数积分，参照 FriCAS）；
2. **完整 CAD**（多变量实代数投影 + 胞腔分解；当前的一维实代数胞腔只是它的地基）；
3. **Gröbner 基方法**（多元多项式理想论：理想属员、方程系统、代数预处理）。

持续开发中的纪律（也是提 issue / 提 PR 的判据）：

- **禁止硬编码、禁止特判**：数学语义（常数、函数、规则、导数模板、定义域条件）
  一律以**数据 + 声明（DSL）+ 注册**表达，不写死在代码里，也不为个别输入开专用
  分支绕过通用算法；能力缺失时拒绝是正确行为。
- **严格域分发**：按域协议的能力字段分派，不按 Python 类型、不按节点名字嗅探。
- **诚实拒答**：自动化结论一律经 `Verdict`；`Unknown` 不得被当作 `Yes`/`No`。
- **单一定义处**：数学语义住在 `cas/math/**`，经 `install(builder)` 装配；内核不认
  识任何数学函数名；import 期不修改全局状态。
- **文档中文、源码英文**：代码与注释不得引用设计文档，理由直述。
- **提交前两步**：`pytest -m random` 与其余 `tests/`。

因此，README 里的能力清单会随 `progress.md` 一起更新；**看到「未实现」条目请不要
当成 bug**——那是刻意的边界，而不是遗漏。
