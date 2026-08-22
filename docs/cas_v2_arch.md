# pyCAS v2 架构设计

> 本文只讲**架构设计**：数据结构、分层、机制、纪律。
> 修订裁定、探索过程、成熟系统调研与参考系统教训见 `docs/notes.md`；
> 使用教程见 `docs/manual.md`；API 参考见 `docs/api.md`。
>
> 定位：**交互式、通用、纯符号 CAS**。计算优先；正确性 = **永不静默错**，不是定理证明器。

---

## 0. 目标与边界

- **交互式通用符号 CAS**。中枢原子操作 = `apply(rule, path)`：对当前式的指定位置应用一条规则。
  四通道：**手动**（用户选规则+位置）/ **建议**（系统列该位置可套的规则）/ **启发式**（有界搜索）/
  **机械算法**（内核算法黑盒直出，快捷方式，不是主路径）。
- **手动/自动语法分层**：`:` 前缀 = 手动操作（逐步可控，每步入账可撤销可解释）；
  `!` 前缀 = 自动求解（算法黑盒直出，verify 背书）。语法即语义，用户一眼区分
  "这步我控制"vs"算法直出"；手动表达式可被自动求解继续处理（混合工作流）。
- **纯符号、精确**：任意大整数、精确有理数。无浮点、无数值通道（数值层只做验证抽查）。
- **积分 / 求解 / 极限 / ODE = 策略插件**。地基只铺前置（多项式 gcd、有理函数规范形、
  FunctionSpec、decide 表）。
- **边界**：判定只限可判定片段；片段外**拒答 / 带 Proviso / 惰性**，绝不静默错；
  矛盾检出即锁（防 ex falso）。
- **完备性的诚实立场**：通用完备不可能（零等价、初等常数等价不可判定）。能做到的最好形态 =
  **可判定片段内完备 + 片段外拒答**。分段承诺：有理函数积分 = 完备；初等函数 = Risch 分期逼近；
  定积分 = 仅承诺有初等原函数的情形。
- **双执行通道**：黑盒结果允许；目标是**可解释步骤链**（step log 天生产出）。
- **设计立场**：数据结构、工作流、算法全部自主设计；参考系统只借思想不搬实现。

---

## 1. 五支柱

### 1.1 驻留项 InternedTerm（L0 数据结构）
- `Expr` 不可变 `(head, args)`，构造时进**全局驻留表**（内容寻址）。
  **equal = 指针比较，O(1)**；哈希键免费；匹配/化简结果按项 id 记忆化（simplify._MEMO）。
- 原子：`Sym` / `Int` / `Rat` / 常量（π,e,i,γ）/ 特殊项（TRUE/FALSE/Undefined/Infinity/EmptySet）。
- **构造即规范化（mk 是唯一构造入口，系统里不存在未规范化对象）**：
  AC 头 flatten + 全序 + 常量折叠；**环规范化内建于构造器**：Plus 合并同类项、
  Times 合并同底整数幂（x·x⁻¹ → 1，**generic 语义**，定义域由 dom_condition 按需提取）、
  Power 归约（x¹→x、x⁰→1、(xⁱ)ʲ→xⁱʲ，整数指数；非整数指数不合并，分支切割安全）、
  `e^a` 规范为 Exp(a)、i 整数幂 mod 4 折叠。
  由此 **`is ZERO` 指针判零对一切经 mk 构造的环表达式可靠**（矩阵消元/求解/验证均依赖它）。
  每头规范化扩展入口 = `term.register_norm`（Conjugate/Piecewise 在用）。
- **模式（含洞）同样经 mk 规范化**：规则在规范形上匹配；被构造器吸收的归并不再进规则库。
- **绑定词（哑变量）一等表示**：`Bound(hint, body)` 节点承载 ∫/Σ/Π/lim 的哑变量；
  body 为 **de Bruijn 索引**（α 等价 = 结构相等）；替换做 α 躲避；
  `open_bound` 还原为 hint 符号供环运算/打印。
  已知行为：打印用积分变量名取首次驻留的 hint（α 等价的代价，语义无影响）。

### 1.2 账本上下文 Context Ledger（L4 数据结构）
- 上下文 = **有序账本**：条目 `(fact, kind, origin)`，origin = `user | step# | axiom | obl#…`。
  约束、换元等式、已推导结果**全部显式在账、带出处、可按 step 回滚**。
- **查询驱动**：插入只记账；判定只在查询时发生（惰性）。
- 作用域 = 账本回滚点栈：压点、回滚，局部假设不外泄。

### 1.3 义务队列 Obligations（提问工作流）
- **计算绝不阻塞等用户**。不可判定条件出现 → 生成义务
  `Obligation(question, affects: [step_id], pending)` 入会话；当前计算**带 Proviso 继续**。
- 用户**事后**作答 → 答案入账本 → 按 step log **重放受影响步骤**（全式搜索匹配位置）。

### 1.4 步骤日志 Step Log（可解释性底座）
- 每步 = `(sid, rule_id, path, before, after, guard:3值, Δcost, note)`。
  规则步逐条可解释；内核算法步只记算法名+验证态（verify 背书即解释，不做微观步骤）。
- 撤销 / 重放 / 解释 / 义务影响面分析，全部建在日志上。
- **位置路径 `path`**（根到子项的索引序列）是唯一寻址方案，四通道统一。

### 1.5 决定表 decide()（可判定片段）
- 分层管线，命中即返回：`semantic`（数值/同一/多项式恒等）→ `ledger`（事实匹配/取反/
  传递闭包）→ `interval`（数值区间传播，含账本等式代入）→ `derive`（声明式推导规则
  注册表，`q(fact)` 递归子查询可组合）→ `axiom`（常数区间、|sin|≤1 等，spec.bound 生成）。
  全未命中 → UNKNOWN。
- `decide(fact, ledger) -> Yes | No | Unknown`；**三值逻辑（3VL，Kleene）**做 And/Or/Not 组合；
  `T3.PROBABLE` 仅供数值采样通道，**不进 decide 的 YES 通道**。
- **区间通道**：把 `a op b` 归为 `d = a−b` 对 0 的区间比较；区间来源 = 数值原子 / 常数公理界 /
  账本界 / 等式代入 / Plus 求和 / 标量缩放 / 偶次幂与 Abs 非负 / integer 属性收紧。
  只读 term + 账本，不回调 decide（防循环）。
- **纪律**：结构不等**不**产出 No（`_poly_eq_check` 只证 Yes 不证 No）——No 必须来自账本或域，
  避免结构性结论短路账本推导。
- **规模纪律**：decide 总量 ≈ 一个小型命题+序算术检查器，不更大；加新推理 = 加一条 derive 规则。

### 1.6 域对象与域推理
- `domain.py`：`R/Q/Z/C` 单例；原子谓词 `nonneg/pos/contains` 返回 True/False/None
  （零依赖，只读 term + 账本，不调 decide——防循环）。结构组合归 decide 的 derive 规则。
- `dom_condition(t)`：递归提取定义域约束（Log→arg>0、负整数幂→≠0、偶分母有理幂→≥0…），
  纯结构不判值。
- `satisfiable(constraints, ctx)`：3VL 可满足性（证伪才答 NO，排自证）；
  `domain_ok = satisfiable ∘ dom_condition` = assume 的域闸门。
- **默认策略与行业一致**：变换 generic，域问题按需检出；assume 时条件本身无定义
  （如 `ln(-x²)≠0`）→ 直接拒绝（"domain empty"）。

---

## 2. 分层

```
L7  策略      cost 单调的化简策略；积分/求解策略（istrategy/bsub/ode）
L6  会话      当前式 + step log + 义务 + 账本 + 规则库 + 转录；四通道；path 寻址
L5  化简      simplify 显式栈重建（经 mk）+ cost + refine（账本驱动）
L4  上下文    账本 + decide 管线 + 义务队列 + ex falso 锁
L3  领域      四梯队（§4）+ FunctionSpec 注册表（地基）
L2  规则      Rule = (pattern, template, guard, 方向, 通道, 优先级)；per-head 索引；热重载
L1  匹配      洞模式；规范形上匹配；AC 归并 + 有界回溯；类型洞；OneIdentity
L0  项        驻留不可变 Expr + 绑定词；构造即规范化；equal = 指针
```

**效率分层**：规则/上下文 = **外壳**（交互层）；规范形+算法 = **内核**（热路径直达，不过规则链）。
**工程约束**：纯 Python；核心与展示路径全部**显式工作栈**（simplify/subst/cost/expand/to_str/
latex/refine 零递归）；预算按节点计。

---

## 3. 匹配器

- 模式 = 项 + 洞：`?x` 单参洞、`??x` 序列洞、**类型洞 `?x::pred`**（num/int/rat/sym/const/expr，
  匹配时结构检查；语义谓词走 guard/decide）、**同名重复洞**（驻留后指针判等，O(1)）。
- **在驻留规范形上匹配**："x³ 里认出 x²" 这类结构出现天然成立；替换后重构造自动再规范化。
- **AC 头归并匹配**：参数已全序排序 ⇒ 双指针归并；仅多序列洞触发回溯，设枚举上限。
- **OneIdentity**：带单位元的 AC 头（Plus→0、Times→1）模式可匹配裸项（`?a+?b` 匹配 `x`）；
  序列洞可绑空元组；类型洞守卫在单位元绑定上同样生效；**非洞子模式不吸收单位元**。
- **匹配与求值解耦**：quote 形式可被匹配和替换；规则左侧天然不求值。quote（`'expr`）是**真 hold**：parser 的 quote 分支跳过 mk 规范化（走 `_intern_expr` 纯驻留），保留原始结构与域约束（反化简形 `'cos(x)/cos(x)^2`、借用形 `'ln(x-k)/ln(x-k)` 保 `x-k>0` 域约束）；`subst`/`instantiate` 遇 Quote 走 raw 路径（`_subst_raw`/`_instantiate_raw` 保 held 结构）；`:value` 脱壳 release，之后走规范形。held 项是数据公民（可构造/显示/匹配/域检查），不参与自动 mk 合并——与 Mathematica `HoldForm` 同地位。
- **绑定词交互**：洞不得落在绑定变量位；body 内被绑变量不透明，外界替换不得捕获。
- **等式即规则**：账本等式在 auto 中作双向替换消费（cost 严格下降才接受）。
- **守卫 = 3VL**：Yes 应用 / No 跳过 / Unknown：自动通道跳过、建议通道呈现并记义务。

---

## 4. 领域地图（四梯队，按依赖排序）

> 地图由**目标驱动**（积分/ODE 终点），每个域标注谁消费它；梯队 = 建造依赖顺序。
> 当前完成状态：M0–M3 已收官 + 后 M3 批次（ℚ(params) 全参数化、真 hold、变形/域 proviso）+ M4 求和（Faulhaber + Gosper）；✓ = 已落地。

### 梯队一：算术与多项式代数 ✓
| 域 | 内容 |
|----|------|
| Z/Q | 精确算术、gcd/lcm |
| 多项式 | 稀疏字典、带余除、ugcd/mgcd（原始伪除 PRS + 递归 content）、div_exact、resultant、discriminant、Zassenhaus 因式分解、ℚ(params) 符号系数域（SymRat 全参数化） |
| 有理函数 | 互素规范形（RatFunc）、apart 部分分式 |
| 代数数 | RootOf 名词 + ℚ(α) 域 + 幂和迹 + Sturm 实根隔离（复根隔离待建） |

### 梯队二：等式与不等式求解 ✓
| 域 | 内容 |
|----|------|
| 方程求解 | 线性/二次（含复根）/有理根/参数低次（proviso）/主支逆（spec.inv）/不可约高次 RootOf 实根（Sturm 隔离序 + 因子整除回验） |
| 方程组 | Gröbner 消元（Buchberger + reduced basis，零维全解 / 正维诚实拒答 / 非有理根截断标注） |
| 线性代数 | 精确消元（det/rank/inv/solve）+ 谱理论（charpoly 排列展开/eigenvalues/eigenvectors） |
| 不等式 | 一元线性链 + 一元多项式 Sturm 符号表（偶重根不换号）；解集一等结构（FiniteSet/Interval/Union） |

### 梯队三：初等函数域 ✓
| 域 | 内容 |
|----|------|
| 幂/根 | 幂律合并（构造器整数幂；带守卫幂律在 power.rules）；√(x²)=|x| |
| exp/log | e^a 规范形；exp 加法定律（化简层）；log 双向带域守卫 |
| trig/双曲 | 多角度基规范形（trig_reduce）+ tan(x/2) 积分；双曲域 spec 注册 + hyp.rules |
| 分段/绝对值 | Piecewise 一等头（mk 归一/逐分支求导）；abs = 分段定理 |

### 梯队四：微积分与分析目标层（主体 ✓）
| 域 | 内容 | 状态 |
|----|------|------|
| 导数 D | 微分器（读 spec.deriv）+ verify 回验通道 | ✓ |
| 极限 | 三值引擎（代入/消去/首阶/洛必达）+ ±∞ + log/exp/atan 支配通道（Gruntz 一期） | ✓（Gruntz 完备化待建） |
| 级数 | Taylor 引擎（截断幂级数 + O 项头 + series_term） | ✓（幂级数算术/收敛半径待建） |
| Σ/Π 求和 | Faulhaber 幂和 + Gosper 有理函数不定/定界求和（常系数递推待建） | ✓（部分） |
| ODE | 四题型分类（direct/可分离/一阶线性/二阶常系数齐次）+ 回代回验 | ✓（非齐次/系统/高阶待建） |
| 不定积分 | spec anti 表（含线性复合）→ 自动正向换元 → Hermite+RT → tan(x/2)；策略步树 istrategy | ✓（Risch 分期 = M5） |
| 定积分 | Newton-Leibniz + 奇点拆分 + 端点极限 + 交叉核对；正向换元（不求逆）+ 反向换元（主支逆+符号窗口）+ 反常判敛 + Piecewise 分段 | ✓ |

### 横切能力
- **equivalent(a, b)**：统一判等管线（指针 → 归零 → 三角层 → 账本/多项式片段 → 采样
  PROBABLE → UNKNOWN）。管线设计调研见 notes.md §2。
- **数值求值层**（evalnum）：eval_exact / eval_approx（spec.numeric）/ sample_agrees；
  只产一致/未知，**绝不产否证**；不进主通道。
- **差分测试**：sympy 仅作测试期预言机，运行时零依赖。

## 系数域支持矩阵（手册级语义声明）

每个能力模块必须明确声明其系数域。当前实测状态（含已知缺口，逐项
对应修复里程碑）。域记号：ℤ⊂ℚ⊂ℚ(i)⊂ℚ(α₁..αₙ)（代数扩张）⊂
ℚ(a,b,...)（超越参数=不透明符号，零等价=有理函数恒等，可判定）
⊂ 可计算常数（ln2、e³、sin1 等——零等价一般不可判定/Richardson，
仅可走数值 PROBABLE 或符号参数化）。

| 能力 | 实际域 | 缺口与计划 |
|---|---|---|
| 多项式算术/gcd/结式 | ℚ ⊂ ℚ(i) ⊂ ℚ(params)（SymRat） | ✓ 全通 |
| 有理函数积分（Hermite+RT） | 同上 | ✓ |
| Risch 塔（exp/log/三角复指数） | ℚ(i)(x,...)；塔内嵌套任意层 | 一般 ℚ(α)=M5.4；符号参数进塔=M5.6 |
| 方程求解 solve | ℚ 上精确；实代数根经 RootOf（实根升序前缀语义） | 复根仅编号；ℚ(i) 解未接 |
| 线性方程组 msolve / Gröbner gsolve | ℚ（params 经 SymRat 应可用，未系统测试） | 待验证清单化 |
| 常微分方程 dsolve | 常系数线性（特征方程→RootOf）；题型分类制 | 变系数/系统=M4 后扩展项 |
| 不等式 solveineq | ℚ 上 Sturm 维一 | CAD/VTS=M7d |
| 积分中的超越常量（ln2、e³…） | ✗ **不支持**——实证：∫2^x dx 当前 unsupported | 修法已定：Log(非零常量) 参数化为命名常量 c∈ℚ(c)（积分全程无需此类常量间关系 => Richardson 安全子集），出口回代。排入 M5.6 首项 |

**微分/积分的域不对称性**（实证）：d(2^x) = log(2)·2^x **可算**——
符号微分是纯结构变换，超越常量保持未求值项即可；而积分要求 η′=log 2
进入系数域做线性代数（待定系数矩阵元素参与 ±×÷ 与零比较），故必须
先把此类常量纳入精确参数域。同一常量，微分免费、积分收费。

**总原则**：任何能力不得静默降域——输入超出声明域时必须显式
unsupported 并注明卡点（现有纪律），本矩阵即声明的权威出处。
新功能合入时同步更新本表。

### 里程碑与路线图
- **M0–M3 ✓ 已收官**（机制基底 → 多项式/有理积分 → 初等域/交互层 → 分析层/ODE/换元双通道；
  逐期内容见 notes.md §1 修订史）。
- **M4 求和/差分 ✓**：Faulhaber 幂和 + Gosper 有理函数不定/定界求和（常系数递推待建）。
- **M5 Risch 分期（进行中）**：M5.0 微分域塔 ✓ → M5.1 exp case（Hermite 推广 +
  Rothstein-Trager residue ✓ / RDE 多项式部分 ✓，exp(−x²) 类不可初等证明已落地）
  → M5.2 primitive/log + 参数化 log deriv + 递归塔（M5.2c 塔域 RDE **完备判定**
  进行中：可积给解/不可积给证明/超界诚实拒答，设计见 m52c2_design.md，
  唯一算法参考 FriCAS intpar.spad，不参考 sympy——实测其 wn→rischDE 链有
  右端缩放缺陷）→ M5.2.5 ℚ(i) ✓ Gaussian rational 系数域（第一个代数常数扩张基建）
  → M5.3 三角经复指数 ✓（trigs_to_exp 重写 + exp 视角 special 分母的
  Laurent 对角下降；tan/eˣsin/eˣcos VERIFIED、sin(x)/x proved；
  复形态出口实化回 sin/cos 待做）→ **M5.4 代数
  常数域泛化**（ℚ(i) 基建参数化极小多项式 → 任意 ℚ(α) 单/多扩张；因子分解
  经 Trager 归约回 ℚ——**代数数完全可判定，非 Richardson 障碍**；不可判定性
  仅出现于超越常数符号（e/π 不透明组合的零等价，Richardson 定理），届时按
  三态纪律输出 undecidable 并注明卡点）→ **M5.5 特殊函数输出层**（Ei/erf/Li₂
  作为答案而非 proved 拒答——FriCAS rdeefx ei_int primpart 形态；判定逻辑
  不变，产品级增量）→ **M5.6 符号参数积分**（参数并入常数域 ℚ(a)：零等价 =
  有理函数恒等式，精确可判；generic 答案 + **条件标注/退化分支**——∫x^a 在
  a=−1、∫e^{ax} 在 a=0 时塔结构塌缩，答案须声明成立条件，绝不静默）。
  终点 = 超越函数范围内完整 Risch 决策程序，含不可初等证明（e^{-x²}、li(x)、
   Si(x) 类带证明拒答——sympy 全缺）。接线裁定：Risch 为 **!integrate 黑盒
  通道**判定终点站（初等原函数 VERIFIED / NOT ELEMENTARY proved + 各层
  失败证据链）；可解释步骤链由 M6 通道②承担（见 M6 定位裁定）。
  FriCAS 对照实据：顶层 trigs2explogs 前置重写 + lfintegrate 五类 kernel 分派；
  **对齐差距清单**（M5.4 后逐项评估价值密度）：代数函数积分（= M7a，M5.4 的
  ℚ(α) 基建即其直接前置）、tan 核（我们走复指数路线，结果等价路径不同）、
  参数化 RDE 装置（可实现——intpar.spad 全套已读通；单条积分不需要，查询类
  功能"哪些常数组合可积"/常数依赖强化时再做）、微分核/用户自定义核扩展
  （可扩展性非核心）、常数依赖引擎强化（符号常数线性关系启发判定）。
- **ODE 扩展**：非齐次（待定系数/常数变易）、常系数系统（exp(At)，特征值前置已就绪）。
- **剩余结构债**：RootOf 复根隔离（已裁定注销：RootOf 语义 = 实根升序前缀 + 复根仅编号，
  SymPy CRootOf 同款边界；除非需要 Mathematica 式全根几何序）。代数数系数多项式
  （Gröbner 回代遇根式/RootOf 解的继续化）。

### M6 规则启发式搜索积分引擎（SAINT/Rubi 路线）

> **定位裁定（三通道产品结构）**：积分有三条执行通道，产出物不同——
> ① 完全手动（`:usub`/`:parts` 战术命令，用户驱动，已有 ✓）；
> ② **自动化手动**（`:isteps`：系统自动搜出一条由手动战术组成的路径，
> 每步与 `:tactic` 同构、可重放可中途接管——现仅 61 行展示雏形，
> **M6 主战场**）；③ 完全黑盒（`!integrate`：内核直出 + verify 背书，
> 已有 + M5 增强）。SAINT/Rubi 天然属于通道②——Slagle 目标即模拟数学家
> 解题，Rubi ShowStep 输出人类可读步骤。黑盒通道不需要 M6：Risch 不可
> 解释是本质属性而非缺陷（价值 = 快 + 塔内完备 + 证明）；可解释性由
> 通道②承担。"黑盒结果允许，目标是可解释步骤链"由此完整落地。
>
> 与 Risch 分工：M6 = 广度引擎（规则覆盖面 + 每步可解释）；
> Risch = 黑盒通道判定权威（塔内完备 + 不可初等证明）。同一问题三解，
> 混合工作流：`:isteps` 出策略树 → `:replay` 全自动重放或中途接管；
> `!integrate` 直出答案作手动继续起点。六系统调研实证：SAINT/Rubi/
> manualintegrate 均为"人类步骤模拟"路线，与算法内核互补而非竞争。

- **M6.0 步树升级裁定**：IntStep 从展示结构（explain 只读树）升级为
  **可执行/可重放的战术序列**——每步 = 战术单元（lhs 匹配 + 变换 +
  note 文本 + D-check 证书），与 `:usub`/`:parts` 手动命令同构；
  step log 接线、预算控制、已见集合防循环。附带裁定：Rubi 规则翻译
  目标形态 = 战术单元（非黑盒变换函数）；L2 规则层复用边界
  （Rubi DownValues 按特异性排序 = 决策树 ≠ 裸 lhs→rhs 改写）。
- **M6.1 SAINT 核心循环**：goal tree 搜索——终结检查（anti 表命中/
  有理检测/塔检测）+ 变换生成（usub/分部/三角代换/规则库匹配，有序
  展开）+ 已见集合 + 深度限制。Slagle 论文的 algorithm rules vs
  heuristic rules 二分对应"终结检查 vs 变换生成"。
  参考实现：本地 `pyCAS/SAINT`（Slagle 论文 Python 复刻，slagle.py
  规则编号与论文对应）；验收 = Slagle 论文原题集 + 每题步骤链可重放。
- **M6.2 Rubi 精选翻译（战术库扩充）**：按章节树分期（1 代数/binomial
  products → 2 exp → 3 log → 4-5 trig/反三角 → 6-7 双曲 → 8 特殊函数）；
  conditions → guard 3VL 映射；**每条入库自动 D-check 验证**（规则库
  本身不得成为静默错源）；ShowStep ↔ step log/note 同构。
  参考实据：expreduce `resources/rubi/` 全章节 .m 快照。
- **M6.3 混合工作流整合**：`:isteps` 步骤链 → `:replay` 重放接线；
  中途接管（重放暂停 → 手动继续）；失败语义链统一（搜索穷尽时各分支
  失败原因机器可读汇总——拒答本身可解释）。

### M7 远期扩展候选（启动前需重新论证价值密度）

> 共同纪律：每项都是"可判定片段内完备 + 片段外拒答"，证书背书形态随项标注；
> 前置设施多数已在 M0–M5 铺设（Gröbner/Sturm/结式/algnum/义务队列）。

- **M7a 代数函数积分（Trager 算法）**：∫R(x, α)（α 为多项式根，如 √(x²+1)、
  √(x³+1)）。前置：ℚ(α) 单扩张域运算（**M5.4 基建直接复用** + algnum 已有底子）
  → 多扩张 + primitive
  element 定理 → Trager resultant/norm 路线。FriCAS 参照 intaf/intalg/primelt
  （~80KB SPAD，主要工程量来源）。验收：∫dx/√(x²+1) = log(x+√(x²+1))；
  椭圆积分类（∫dx/√(x³+1) 无初等原函数）给带证明拒答。
- **M7b 丢番图方程（数论）**：对标 Mathematica `Solve[..., Integers]`/`Reduce`。
  可判定片段分层：线性 ax+by=c（uexgcd 已有）→ Pell 方程与二元二次
  （循环连分数周期 + 判别式分类）→ 平方和（Fermat 两平方和 + Lagrange 四平方和，
  定理表驱动）。**边界裁定：一般多项式丢番图不可判定（Matiyasevich/DPRM）——
  片段外拒答是定理要求而非实现缺陷**。证书 = 解代回（易）+ 片段内完备性论证
  （难，随片段写明依据定理）。
- **M7c 平面几何定理证明（吴消去法/消点法）**：几何谓词（共线/垂直/等距/共圆）
  坐标化为多项式组 → 理想成员性判定。两条技术路线：Gröbner 基（✓ 已有前置）
  或 Wu 特征列（伪除构造，对几何问题常更高效）；消点法（张景中）作为面积/比例
  语法的补充表示。非退化条件（分母 ≠ 0、点不重合类）走义务队列显式化——
  绝不静默假设一般位置。证书 = 多项式恒等式（mk 归零验证）。
  验收：垂心、九点圆、Simson 线类经典定理自动证明。
- **M7d 实不等式决策（CAD/VTS）**：Tarski-Seidenberg 定理保证实闭域一阶理论
  可判定。技术路线：Collins CAD（投影-提升）或 Weispfenning 虚拟替代（低维常更快）。
  接入 decide 作新通道——**YES/NO 均可信的决策程序，区别于数值采样的 PROBABLE**
  （补上 decide 管线"结构不等不产 No"之外的语义否证能力）。复杂度双指数——
  只承诺低维（≤3 变量）小次数片段，超限诚实拒答。前置全就绪：
  Gröbner ✓、Sturm（dim 1 特例 ✓）、结式 ✓。对标 Mathematica `Reduce[..., Reals]`/`Resolve`。

---

## 5. 规则与 DSL（规则 = 定理库）

```
rule log_e = log(?x*?y) -> log(?x)+log(?y)   guard ?x>0 && ?y>0   as expand
rule log_c = log(?x)+log(?y) -> log(?x*?y)   guard ?x>0 && ?y>0   as combine
rule pow_mul = (?x*?y)^?a -> ?x^?a*?y^?a     guard ?x>0 && ?y>0   as expand  prio 90  auto
```

- 语法：`rule <id> = <lhs> -> <rhs> [guard c] [as dir] [channels a,b] [prio N] [auto]`；
  方向标签成对呈现；`auto` 通道仅收无条件安全规则；`prio` 小者先试；热重载。
- **会话内联**：`:rule` 定义（origin='session'，转录收录回放重建；不计规则指纹）。

### 5.1 三分边界（normalizer / 规则库 / 内核算法）

| 内容 | 去处 | 理由 |
|---|---|---|
| 表示归并（flatten/排序/合并同类项/幂合并） | 构造器 mk | 纯表示同一性；驻留要求"等项 = 指针"；无条件安全 |
| 定理（恒等式、带域守卫的推导、换元等式、spec 公理派生） | 规则文件 | 声明式、可审计、用户可扩展 |
| 过程性算法（消元/因式分解/Hermite/Gröbner） | 内核代码 | 是过程不是改写规则；正确性由 verify 背书（回乘/回微分） |

`auto` 通道 = normalizer ∪ {auto 规则}，接受准则 = cost 单调不增（预算内 fixpoint）。

### 5.2 函数内核注册表 FunctionSpec（反硬编码地基，cas/spec.py）

每个函数头一份声明式注册，消费者全部读表：

```python
FunctionSpec(name="Sin", arity=1, print_name="sin", parity="odd",
             deriv=..., bound=(-1,1), special={0:0, π:0, π/2:1},
             dom=..., numeric=math.sin, anti=..., inv="Arcsin")
```

- **消费者**：mk（special 折叠）/ diff（deriv）/ decide（bound 公理自动生成）/
  domain（dom）/ pprint·latex（print_name）/ evalnum（numeric）/ integrate（anti，含线性复合）/
  solve·bsub（inv 主支逆）/ loader（parity 生成奇偶规则，origin='spec'）。
- **已注册**：Sin/Cos/Tan/Atan/Arcsin/Arccos/Exp/Log/Abs/Sinh/Cosh/Tanh。
- **纪律（代码评审验收标准）**：新增函数只允许写 spec 注册 + 规则文件；
  **禁止在任何消费者模块里为新函数加 if 分支**。这是"未来实现积分/微分方程不返工"的制度保证。

---

## 6. 化简 / 规范形 / 停机

- **核心化简器只放无条件安全变换**；带条件规则只在手动/建议/策略通道。核心化简永不提问。
  分工：环层规范形在构造器 mk；`simplify` = 显式栈自底向上重建（每层经 mk，子项变化向上传播）
  + 化简层无条件恒等（exp 加法定律：exp(a)exp(b)→exp(a+b)、Exp(a)ⁿ→Exp(n·a)）+ 预算 +
  项 id 记忆化；`refine` = 账本驱动化简（只重写 decide=YES 的结构）。
- **cost(e) = 加权节点计数**；自动策略**单调下降才接受**（停机充分条件）。
- **分层规范形**（全局规范形不存在——Richardson 定理；成熟系统一致收敛于"分层投降"）：
  | 层 | 规范形机制 | 状态 |
  |----|-----------|------|
  | 整数/有理 | 构造即规范化（term.py） | ✓ |
  | 多项式/有理函数 | 降幂字典（poly.py）/ 互素规范形（ratfunc.py） | ✓ |
  | 三角多项式 | 多角度基：ℚ[sin,cos]/⟨sin²+cos²−1⟩ 商环唯一线性组合 | ✓ |
  | exp/log 塔 | Risch 结构定理（塔内表示唯一、零等价可判定） | M5 |
  | 分段 | 条件序归并（mk 剪 false/true 截断/单支塌缩） | ✓ |
  跨层翻译算子（策略动作，带守卫/义务，不进规范形）：Exponentialize、PowerExpand（走域闸门）。
  层外混合式 = 策略通道（方向标签成对规则 + cost 单调 + 义务队列），不承诺完备，结果可解释。
- **求值预算**：显式栈 + 步数上限，超限即停报告（用户规则无法静态保证停机）。
- **形式层 vs 分析层**：形式恒等式无条件进核心；换序/重排/Σ↔∫ 带收敛条件走策略规则，
  不可判定收敛 → Proviso 标"形式结果"或记义务。
- **常数问题（诚实边界）**：超越混合零等价不可判定 → UNKNOWN 拒答；verify 同为三值
  （已验证/未通过/未验证如实报告）；数值采样只做 PROBABLE 抽查。
- **FullSimplify 式搜索不做**：价值前提是大定理库 + 调校过的 ComplexityFunction；
  重估条件 = 规则库百条级且 cost 单调准则成为可证瓶颈（裁定过程见 notes.md §3）。

---

## 7. 上下文细则

### 7.1 约束生命周期
**来源五类**（统一入账本，origin 标注）：① 用户 assume/declare；② 规则守卫；
③ 域公理（分母≠0、log 定义域）；④ 分支切割（log/atan 辐角条件）；⑤ 换元条件。
`收集` → `分析`（惰性：查询时 decide + 矛盾锁）→ `消费`（等式即规则重写；不等式划分支）→
`裁决`（义务队列：作答 → 重放）→ `回滚`（作用域退出/撤步）。

### 7.2 ex falso 锁
decide 检出矛盾 → 会话冻结：后续 feed/apply/auto/answer 一律拒绝，报告**矛盾链**
（账本 origin 使矛盾可解释）；undo 撤掉引发步自动解锁。

### 7.3 分支与闸门
- `check_and_assume(fact) -> (T3, why)`：**统一入账闸门**（域检死 → 矛盾锁 → 入账）；
  Session 三入口（assume/answer/规则 guard）全部走它，无绕过路径。
- `branch(c1, c2, ...)`：每条件 = clone + 闸门入账 → Branch(cond, ctx, status∈open/empty)；
  **分支空 = 与父账本矛盾的检出**。
- declare 属性消费：符号属性（positive…）映射为不等式事实；integer 收紧区间通道界。

---

## 8. 模块清单（实际文件，与代码同步）

| 文件 | 内容 | 层 |
|------|------|----|
| `cas/term.py` | 驻留 Expr / 原子 / Bound（de Bruijn）/ 构造即规范化（环层 + register_norm）/ subst / open_bound | L0 |
| `cas/match.py` | 洞模式匹配：结构 / AC 归并+有界回溯 / 类型洞 / OneIdentity | L1 |
| `cas/rules.py` `cas/loader.py` | Rule/RuleSet/apply_rule/Step + DSL 解析热重载 | L2 |
| `cas/context.py` `cas/decide.py` `cas/domain.py` | 账本 + check_and_assume 闸门 / 三值 decide（区间通道+derive+公理）/ 域谓词与 dom_condition | L4 |
| `cas/simplify.py` `cas/refine.py` | 显式栈重建化简（exp 加法定律合并）/ 账本驱动化简 | L5 |
| `cas/poly.py` `cas/ratfunc.py` `cas/factor.py` `cas/apart.py` | 多项式（含 mgcd/div_exact）/ 有理函数 / Zassenhaus 因式分解 / 部分分式 | L3 |
| `cas/algnum.py` `cas/sturm.py` | 代数数 ℚ(α) + RootOf + 幂和迹 / Sturm 实根隔离 | L3 |
| `cas/solve.py` `cas/matrix.py` `cas/ineq.py` `cas/sets.py` `cas/groebner.py` | 方程求解（含参数低次/主支逆/RootOf 实根）/ 矩阵+谱理论 / 多项式不等式 / 解集一等结构 / Gröbner 消元方程组 | L3 |
| `cas/ops.py` | 项层结构 API：together/cancel/collect/coefficient/numerator/denominator | L3 |
| `cas/spec.py` | FunctionSpec 注册表（导数/打印名/奇偶/特殊点/有界/定义域/anti/inv/numeric） | L3 地基 |
| `cas/trig.py` | 三角多角度基规范形（trig_reduce/trig_equivalent） | L3 |
| `cas/diff.py` | 微分器（读 spec.deriv）+ verify 回验 | L3 |
| `cas/integrate.py` | 不定积分（spec anti/usub/Hermite+RT/tan 半角）+ 定积分（defint/反常/分段/正向换元） | L3/L7 |
| `cas/istrategy.py` `cas/bsub.py` | 积分策略步树（IntStep）/ 反向换元（主支逆+符号窗口） |
| `cas/risch.py` | 微分域塔（DiffExt 塔构建 + derivation 塔上求导；M5 Risch 地基） | L7 |
| `cas/series.py` `cas/limits.py` | Taylor 级数引擎（含 O 项）/ 三值极限（含 ±∞ 与支配通道） | L3 |
| `cas/ode.py` | ODE 四题型分类求解 + 回验 | L3 |
| `cas/evalnum.py` | 数值求值层（仅验证/抽查通道） | 横切 |
| `cas/session.py` | REPL/转录 DSL/四通道/义务/KernelCmd 注册表 | L6 |
| `cas/parser.py` `cas/pprint.py` `cas/latex.py` | 解析 / 打印 / LaTeX | L6 |
| `cas/errors.py` | 异常协议（预算/解析/多项式，不崩溃不静默） | L0 |
| `rules/*.rules` | 定理库：basic/log/trig/hyp/power/piecewise | L2/L3 |
| `examples/*.pycas` | 可回放验证案例（转录 DSL 成品） | L6 |
| `tests/` | 按模块拆分 + sympy 差分测试 + examples 回放断言 | 全线 |

---

## 9. 数据结构草图

```
Expr          = (head: Sym, args: tuple)        # 不可变、驻留、构造即规范化；equal = 指针
Atom          = Sym | Int | Rat | Const(π,e,i,γ) | Special | BVal | DB
Pattern       = Expr + 洞(?x / ??x / ?x::pred)
Rule          = {id, pattern, template, guard, direction, channels, auto, origin, priority}
LedgerEntry   = {fact, kind, origin}
Context       = {entries: [LedgerEntry], marks: [int]}
Obligation    = {oid, question, affects, note, pending: [(rule, path)]}
Step          = {sid, rule_id, path, before, after, guard, dcost, note}
Session       = {current, log: [Step], obligations, ctx, rules, history,
                 transcript, defs, kernel: {name: KernelCmd}, budget}

decide(fact, ctx) -> Yes | No | Unknown        # 分层管线 + 3VL
equivalent(a, b, ctx) -> YES | NO | PROBABLE | UNKNOWN   # 统一判等管线
```
