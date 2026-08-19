# pyCAS 探索笔记（修订裁定 · 调研 · 经验教训）

> 与 `cas_v2_arch.md`（纯架构设计）分工：本文承载**过程性内容**——
> 修订史与长期裁定、成熟系统调研、参考系统教训、开发中踩坑换来的经验。
> 逐次变更的完整日志见 git 历史（M0→M3 收尾）。

---

## 1. 修订史与长期裁定

### 1.1 阶段精要

- **地基期**：环规范化下沉构造器（mk 即规范化，`is ZERO` 指针判零可靠）；`^` 右结合；
  Neg 幽灵头清理（负号统一 Times(-1,·)）；decide 区间传播通道（含等式代入）；ex falso 锁生效。
- **M2.0 反硬编码**：FunctionSpec 注册表落地（消费者全部读表，硬编码表退役）；
  数值求值层 + sympy 差分测试；equivalent 统一判等管线；KernelCmd 注册表消除 REPL 硬编码。
- **债务清偿**：多元 gcd（mgcd + div_exact）；显式工作栈全额清偿（核心/展示路径零递归）；
  OneIdentity；subst 复合项替换；义务重放全式搜索。
- **M3 分析层**：级数/极限/定积分三件套 + 正/反向换元 + 反常积分判敛 + 分段积分 +
  ODE 四题型；转录 DSL（:save/:replay + 规则指纹）；两批采购清单
  （:rule/:value/:refine/:latex/:solveset/:series/:isteps + Protected）。
- **剩余结构债**：ℚ(params) 系数域全参数化（前置 = ℚ(params) 因式分解）；RootOf 复根隔离。

### 1.2 立场裁定（长期有效，改动需重新论证）

1. **FullSimplify 式搜索化简不做**。价值前提是大定理库 + 调校过的 ComplexityFunction；
   Richardson 定理保证超越函数类无终止保证，只能预算硬切。
   重估条件：规则库百条级且 auto 的 cost 单调准则成为可证瓶颈。
2. **规则库 = 定理库**。表示归并进构造器、定理进规则文件、过程性算法进内核代码 +
   verify 背书。判断口诀见架构 §5.1。
3. **数值采样只进验证/抽查通道**（标 PROBABLE），永不进 decide 的 YES 通道、不产否证。
4. **算法步不做微观解释**（verify 背书即解释），规则步逐条可解释。
5. **启发式探测必须回验裁决**：换元/分类等探测产出的结果，逐个微分回验，
   未过继续试下一候选——伪换元 x³/(x²−1) 曾泄漏错误原函数且被标 VERIFIED，此裁定由此而来。
6. **新增函数反硬编码纪律**：只写 spec 注册 + 规则文件，禁止消费者模块加 if 分支。
7. **变更命令必入转录**（:value/:refine/:rule 等）——否则回放无法重建推导。
   会话规则不计规则指纹（由转录自重建），否则回放被自己的新规则拒死。

### 1.3 诚实记录（已知局限）

- apart 实现依赖 Zassenhaus 因式分解（非纯 CRT 路线）。
- RootOf 实根有 Sturm 隔离区间；复根仍只有共轭类编号。
- 三角积分路径的 [VERIFIED] 只覆盖 t 域有理积分，半角代回本身未单独验证。
- 主支逆求解不给周期族通解（诚实标注 principal branch）。
- 绑定词打印变量名取首次驻留的 hint（α 等价代价，语义无影响）。

---

## 2. 判等与化简：成熟系统调研

**根本事实（Richardson 定理）**：含 sin/exp/abs 的函数类零等价不可判定——
**全局规范形不存在也不可能存在**。这不是实现缺陷，是数学定理。
Mathematica / Maple / Maxima / SymPy 一致收敛于同一套三件套：
**分层规范形 + 跨层翻译算子 + 层外搜索式化简**，判等 = **多阶段管线 + 诚实 UNKNOWN**。

### 2.1 成熟系统实际做法

| 系统 | 层内规范形 | 跨层/搜索 | 判等 |
|------|-----------|----------|------|
| Mathematica | Automatic simplification（环层规范）；Together/Expand 有理函数 | FullSimplify = 变换空间搜索 + ComplexityFunction；TrigToExp/FunctionExpand/PowerExpand 为翻译算子 | Equal：结构化简归零 + Together；PossibleZeroQ 数值启发式；$Assumptions 下 Refine |
| Maple | automatic simplification | simplify 族按域 | testeq：符号尝试 + 随机数值采样（概率性，官方明言） |
| Maxima | CRE 规范有理形；radcan（exp-log 塔规范形，基于 Risch 结构定理） | ratsimp/trigsimp 按域 | equal() = ratsimp(a−b)=0；is() 走假设库；判不了 asksign 提问 |
| SymPy | 构造即规范化（环层） | simplify 编排各域 simplifier；fu 算法（三角） | equals()：符号尝试 + 随机数值采样 |

**共性要点**：
1. **环层（多项式/有理函数）是唯一全局可判定层**——驻留/CRE/Together 都在解这一层（pyCAS 已对齐）。
2. **每个超越函数族各有自己的"小规范形"**：三角多项式（商环 ℚ[sin,cos]/⟨sin²+cos²−1⟩，
   SymPy trigsimp_groebner 同款，pyCAS 多角度基已落地）、exp-log 塔（Risch 结构定理保证
   表示唯一，Maxima radcan 的理论基础，pyCAS M5）、代数数（minpoly 判等，pyCAS algnum 已落地）。
3. **层间不做规范形合并，只做带条件的策略性翻译**（Mathematica convert 思想）：
   Exponentialize/PowerExpand 是策略动作，带守卫/义务，不是化简义务。
4. **判等是管线不是单一算法**：指针 → 归零 → 层内决策过程 → 翻译重试 → 数值采样 → UNKNOWN。
5. **数值采样是探测器不是证明**：Maple testeq / SymPy equals 都用，但结论带概率色彩；
   pyCAS 只允许它进验证/抽查通道（标 PROBABLE）。
6. **微分验证是不对称捷径**：验证 D(F)=f 往往比直接判等容易——verify 通道已落地。

### 2.2 pyCAS 形态：equivalent(a, b, ctx) 统一管线（✓ 全通）

```
1. 指针同一（驻留免费）                                        -> YES
2. simplify(a−b) 归零（环层规范形）                            -> YES
3. 层内决策：多项式恒等（_poly_eq_check）/ 三角多项式多角度基
   （trig_equivalent）/ 代数数 minpoly（algnum，积分层在用）    -> YES / NO
4. 账本片段（decide Eq）+ 翻译算子重试（策略动作，带义务）      -> YES / NO
5. 数值采样抽查：结构化采样点 + 极点保护                        -> PROBABLE（不产否证）
6. 全部未命中                                                  -> UNKNOWN（拒答，永不静默错）
```

---

## 3. 参考系统教训（实据读源版）

> 通读本地五份参考源码（maxima / mathics-core / expreduce / yacas / SAINT）后的实据结论。
> 立场：**借思想不搬实现**（ask-in-place、大而全比较器、递归求值循环一律不搬）。

| 系统 | 实据（文件级） | 教训 → pyCAS 动作 |
|------|--------------|------------------|
| expreduce | `eval.go`：求值 = 哈希比较 fixpoint 循环 + 每项 `EvaledHash` 缓存（命中即跳过）；属性（Flat/Orderless/Hold/Listable）按头查询；Trace 是事后表达式 | ① 项 id 记忆化 ✓（simplify._MEMO，驻留免费）② 属性 = 按头声明式行为 → 并入 FunctionSpec |
| mathics-core | `core/attributes.py`：16 属性位集，含 OneIdentity、NumericFunction、Protected | OneIdentity ✓（裸项匹配 + 单位元入洞）；Protected → Session._RESERVED 内建头拒覆盖 |
| yacas | `scripts/stdarith.ys`：仅加法归约 ≈40 条声明式规则，带优先级与谓词守卫（`_x_IsNumber`）；内核小、数学全在脚本库 | ① 环规范化下沉构造器被反证为正确（yacas 为此付出几百条规则）② 规则优先级/类型洞进 DSL ✓ |
| SAINT | `slagle.py`：AlgorithmRule（确定性单结果）vs HeuristicRule（候选列表）分裂；deriv 是 2700 行 if-elif 链（反面教材）；带类型洞 `Symbol('a',[CONST])` | ① 四通道设计获原型印证 ② FunctionSpec 的反面教材 ③ 类型洞前身 |
| maxima | 92MB / 5100 文件（Lisp）；`defint.lisp` 3787 行定积分"技巧博物馆" | 规模感：通用 CAS 代码量 10⁵ 行级；pyCAS 以"可判定片段 + 拒答"为生存策略；定积分技巧 = 半统一框架（NL+域验证/Meijer G/creative telescoping/围道），不做通用实现 |

**散点教训（开发中实证）**：
- 哑变量捕获是符号计算的经典静默错误源——L0 用 de Bruijn + α 躲避从根上处理。
- 四家 CAS 的 equal 全是递归树比较（Maxima 有 equal 漏洞修复史）——驻留从根上消灭。
- Maxima 事实库 eager 全量推理是性能坑——pyCAS 只做查询触发的窄判定。
- Maxima 提问卡死脚本是设计级痛点——义务队列把"问"变成异步 + 重放。
- 通用 AC 穷举匹配是 NP——全序排序使常见情形无回溯。
- 单调接受准则（cost 不增才收）是化简停机的最简充分条件。
- 规则数量必然爆炸（yacas 标准库数万行脚本）——这正是三分边界（§架构 5.1）的生存理由。

### 3.1 可验证转录 DSL 的生态位（调研结论）

主流 CAS 均无可回放验证的推导 DSL；最接近的形态：证明助手的 tactic 脚本
（Coq/Lean/Isabelle，校验逻辑规则而非计算）、Theorema（Mathematica 上的证明导向计算）、
Axiom/FriCAS（类型系统静态验证，无过程层）、SAINT 推导树（只展示不校验）、
Mathematica notebook（无指纹无验证态）。pyCAS 的"转录 + 规则指纹 + 验证态 +
驻留指针同一"处于 notebook 与证明脚本之间的空档——交互式 CAS 的可抄作业是
**人机分工的模式**（Maxima asksign/noun-verb、manualintegrate 步树元数据、
SAINT 规则分裂），不是算法本身。

---

## 4. 场景 → 机制对照（验收清单）

| 场景 | 机制 |
|------|------|
| ×cosx/cosx 需 cosx≠0 | 守卫 3VL → Unknown 记义务 / Proviso |
| x²<0 在 R 上 | 域公理 → decide 检出矛盾 → 冻结 + 矛盾链 |
| 积分需分类讨论 | sign 族判定 → 分支账本 → 结果合并 |
| 分段函数 | Piecewise 一等头 + 分段归一 |
| ln(xy) 双向 | 方向标签成对规则，用户/cost 选向 |
| 换元（不定/定积分） | 正向：defint_auto 新限正向求值不求逆；反向：bsub 主支逆 + 符号窗口 |
| 条件收敛级数重排 | 带守卫策略规则，不可判 → Proviso"形式结果" |
| 用约束化简 | 账本等式即规则（auto 消费）+ refine 通道 |
| 结构替换 | 规范形上匹配：x³ 认出 x² 并替换 |
| 可解释 | step log：规则步逐条 / 算法步报名+验证态 |
| 积分结果验证 | verify 三值 + PROBABLE 采样抽查 |
| 计算复现 | 转录 DSL：:save/:replay + 规则指纹 + 指针同一 |
