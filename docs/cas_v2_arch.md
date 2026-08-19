# pyCAS v2 架构（自主设计版·定稿）

> **2026-08 地基修订**：环规范化下沉构造器（mk 即规范化，`is ZERO` 判零可靠）；
> parser `^` 右结合；decide 新增区间传播通道（含等式代入）；ex falso 锁实际生效；
> Neg 幽灵头清理（负号统一为 Times(-1, ·)）；规则库与文档承诺对齐。
> **2026-08 地基补强规划**：新增 §5.2 函数内核注册表 FunctionSpec（反硬编码地基）、
> §11 判等与化简（成熟系统做法 + equivalent 统一管线）、M2.0 地基补强里程碑；
> 数值求值层与差分测试提升为近期必建。
> **2026-08 M2.0 规则实处化**：FunctionSpec 落地（cas/spec.py，八函数注册；导数表/打印名/
> 有界公理/定义域/特殊点折叠/奇偶规则全部改从注册表读取，diff._TABLE 等硬编码退役）；
> 类型洞 `?x::pred`（num/int/rat/sym/const/expr，yacas 同款）；apply 无参全式搜索；
> auto 重写循环写 step log（防振荡）；规则优先级 + DSL `prio N`。
> **2026-08 M2.0 判等收口与验证层**：数值求值层 cas/evalnum.py（环层精确有理 + 超越函数
> 走 FunctionSpec.numeric + 采样带极点保护，只产 PROBABLE 不产否证）；equivalent 统一管线
> 接入三角层（sin²+cos²=1 符号 YES）与采样通道（T3.PROBABLE）；sympy 差分测试
> （仅测试期预言机）；内核命令注册表 KernelCmd（消除 REPL 硬编码）。测试按模块拆分。
> **2026-08 基础功能补全**：复数域（i 整数幂折叠、纯常数乘积自动展开、Conjugate 规范化、
> 二次方程复根）；项层结构 API（cas/ops.py：together/cancel/collect/coefficient/numerator/denominator）；
> 等式即规则落地（auto 消费账本等式，cost 严格下降）；Sturm 实根隔离（cas/sturm.py）+
> 一元多项式不等式（cas/ineq.py，区间并解集）；RootOf 实根获隔离区间（algnum.real_isolation）；
> declare/属性消费闭环（integer 区间收紧）；power.rules（sqrt(x²)=|x| auto + 带守卫幂律）。
> 底层修复：subst 支持复合项替换；比较头参数递归规范化；义务重放改全式搜索；replay 账本清理。
> **2026-08 结构性债务清偿**：多元 gcd（poly.mgcd，原始伪除 PRS + 递归 content）与
> 精确除法 div_exact——多变量 together/cancel/RatFunc 约分全线打通；参数化低次求解
> （solve 对 a·x²+b·x+c 给通用求根公式 + proviso）；显式工作栈落地（simplify/subst
> 迭代化，recursionlimit=120 下 300 层深表达式安全）。
> **2026-08 匹配器与展示层收官**：OneIdentity 落地（Plus/Times 模式匹配裸项，单位元
> 入洞：?a+?b 可匹配 x，类型洞守卫生效，非洞子模式不吸收；mathics 属性同款）；
> 显式工作栈**全额清偿**（cost/expand/to_str 亦迭代化，核心与展示路径零递归）。
> **立场裁定**：FullSimplify 式搜索化简**现段不做**——价值前提是大定理库与调校过的
> ComplexityFunction，现规则库规模无搜索素材；Richardson 定理保证无终止保证，
> 只能预算硬切。重估条件：规则库百条级且 auto 的 cost 单调接受准则成为可证瓶颈。
> **2026-08 M2 收官**：双曲函数域（Sinh/Cosh/Tanh 注册 spec 即得导数/打印名/奇偶规则/
> 特殊点折叠/数值层，零核心改动，FunctionSpec 红利验收）+ hyp.rules（cosh²−sinh²=1、
> 指数定义双向）；可解释步骤统一（规则步逐条推导；内核算法步只记算法名+验证态入
> step log，单算法调用不做微观解释，verify 背书即解释；integrate 报所用方法）；
> REPL 重设计（%N 历史复用按高优先级渲染补括号、:steps/:hist、规则应用当场给可解释反馈）。

> 定位：**交互式、通用、纯符号 CAS**。计算优先；正确性 = **永不静默错**，不是定理证明器。
> 设计立场：**数据结构、工作流、算法全部自主设计**。参考系统（maxima / mathics-core /
> expreduce / yacas）只提供两类输入：**教训**（什么坑不能踩）与**规模感**（做多大算够）。
> 它们的机制形态（ask-in-place、大而全比较器、递归求值循环）**一律不搬**。

---

## 0. 目标与边界

- **交互式通用符号 CAS**。中枢原子操作 = `apply(rule, path)`：对当前式的指定位置应用一条规则。
  四通道：**手动**（用户选规则+位置）/ **建议**（系统列该位置可套的规则）/ **启发式**（有界搜索）/
  **机械算法**（内核算法黑盒直出，快捷方式，不是主路径）。
- **纯符号、精确**：任意大整数、精确有理数。无浮点、无数值通道。
- **积分 / 求解 / 极限 = 后期策略插件**。地基只铺前置（多项式 gcd、有理函数规范形、exp 塔、decide 表）。
- **边界**：判定只限可判定片段；片段外**拒答 / 带 Proviso / 惰性**，绝不静默错；
  矛盾检出即锁（防 ex falso）。
- **完备性的诚实立场**：通用完备不可能（零等价、初等常数等价不可判定）。能做到的最好形态 =
  **可判定片段内完备 + 片段外拒答**。分段承诺：有理函数积分 = 完备（M1）；初等函数 = Risch 分期逼近；
  定积分 = 仅承诺有初等原函数的情形。
- **双执行通道**：黑盒结果允许；目标是**可解释步骤链**（step log 天生产出）。

---

## 1. 五支柱（每条 = 我们的设计 + 一句教训）

### 1.1 驻留项 InternedTerm（L0 数据结构）
- `Expr` 不可变 `(head, args)`，构造时进**全局驻留表**（内容寻址）。
  **equal = 指针比较，O(1)**；哈希键免费；匹配/化简结果可按 `项id` 记忆化。
- 原子：`Sym` / `Int` / `Rat` / 常量（π,e,i,γ——常量自带公理条目入上下文）。
- **构造即规范化（mk 是唯一构造入口，系统里不存在未规范化对象）**：
  AC 头 flatten + 全序 + 常量折叠；**环规范化内建于构造器**：Plus 合并同类项、
  Times 合并同底整数幂（x·x⁻¹ → 1，**generic 语义**，定义域由 dom_condition 按需提取）、
  Power 归约（x¹→x、x⁰→1、(xⁱ)ʲ→xⁱʲ，整数指数；非整数指数不合并，分支切割安全）。
  由此 **`is ZERO` 指针判零对一切经 mk 构造的环表达式可靠**（矩阵消元/求解/验证均依赖它）。
  每头规范化扩展入口 = `term.register_norm`（mk 对非 AC/Power 头应用）。
- **模式（含洞）同样经 mk 规范化**：规范化对洞语义保持（目标项同样规范化），
  规则在规范形上匹配；被构造器吸收的规则（如 x¹→x、0+x→x）不再进规则库。
- **绑定词（哑变量）一等表示**：`Bound(var, body)` 节点承载 ∫/Σ/Π/lim/D 的哑变量；
  构造时哑变量**规范化改名**（形状相同的哑变量共享同一驻留名 ⇒ ∫f dx 与 ∫f dt 结构相等）；
  替换做 **α 躲避**（自由变量撞绑定时自动换名）。
  [教训：哑变量捕获是符号计算的经典静默错误源，L0 不处理则积分结果必然出错。]
  [已知行为：驻留键只含 body，**打印用的积分变量名取首次驻留的 hint**，
  后写的 ∫f dt 可能打印为 ∫f dx（α 等价的代价，语义无影响）。]
- [教训：四家 equal 全是递归树比较，Maxima 有 equal 判定漏洞修复史——驻留从根上消灭。]

### 1.2 账本上下文 Context Ledger（L4 数据结构）
- 上下文 = **有序账本**：条目 `(fact, kind, origin)`，origin = `user | step# | axiom`。
  约束、换元等式、已推导结果**全部显式在账、带出处、可按 step 回滚**。
- **查询驱动**：插入只记账；判定只在查询时发生（惰性）。
- 作用域 = 账本回滚点栈：压点、回滚，局部假设不外泄。
- [教训：Maxima 事实库 eager 全量推理是性能坑——我们只做查询触发的窄判定。]

### 1.3 义务队列 Obligations（提问工作流——我们的原创）
- **计算绝不阻塞等用户**。不可判定条件出现 → 生成义务
  `Obligation(question, affects: [step_id], branches)` 入会话；当前计算**带 Proviso 继续**。
- 用户**事后**作答 → 答案入账本 → 按 step log **重放受影响步骤**（日志让重放廉价）。
- [教训：Maxima 提问卡死脚本是设计级痛点——我们把"问"变成异步义务 + 重放。]

### 1.4 步骤日志 Step Log（可解释性底座——我们的原创）
- 每步 = `(step_id, rule_id, path, before, after, guard:3值, Δcost)`。
- 撤销 / 重放 / 解释 / 差分测试 / 义务影响面分析，全部建在日志上。
- **位置路径 `path`**（根到子项的索引序列）是唯一寻址方案，四通道统一。
- [教训：四家都没有把"步骤"做成一等数据——可解释只能靠 Trace 事后还原。]

### 1.5 决定表 decide()（可判定片段——我们的算法）
- 按**谓词族**注册小型判定过程：`sign`（符号）/ `ord`（序）/ `dom`（属域）/ `eq`（相等）。
- `decide(fact, ledger) -> Yes | No | Unknown`；**三值逻辑（3VL，Kleene）**做 And/Or/Not 组合。
- 规模纪律：每族 ≤ 数百行；总量 ≈ 一个小型命题+序算术检查器，**不更大**。
  域公理（ℝ 平方非负、log 定义域、分母≠0）= 注册进表的 axiom 条目，隐蔽矛盾由此现形。
- [教训：yacas 的小型可证明器证明"小片段够有用"；Maxima 的巨型比较器是反例。]

### 1.5b decide 内部 = 分层管线 + 声明式推导规则（2026 修订）

- 管线，命中即返回：`semantic`（数值/同一/多项式恒等）-> `ledger`（事实匹配/取反/反向/传递闭包）
  -> **`interval`（数值区间传播，2026-08 新增）** -> `derive`（声明式规则注册表）-> `axiom`（常数区间、|sin|≤1 等）。全未命中 -> Unknown。
- **区间通道 `_interval`**：把 `a op b` 归为 `d = a−b`（构造器自动合并）对 0 的区间比较；
  区间来源：数值原子 / 常数公理界 / 账本数值界直查 / **账本等式代入（常数等式端点非严格，
  变量等式严格性透明传递）** / Plus 求和 / 数值标量缩放 / 偶次幂与 Abs 非负。
  只读 term + 账本，不回调 decide（防循环）。由此 `x>2 ⊢ x+1>3`、`x=y, y<3 ⊢ x<3`、
  闭区间单点即精确值（`x=5 ⊢ x+1>6` NO）。
- `derive(name, applies, fn)` 注册推导规则；规则内通过 `q(fact)` 递归子查询（depth ≤ 6 防环），
  子查询天然可组合（3VL 拼装）——加新推理 = 加一条规则，不动管线。
- 已注册族：`cmp-flip`（仅左零翻右、表尾兜底）、`ne-from-ord`、`sign-atom`（走域谓词）、
  `sign-times`（因子符号组合）、`sign-even-power` / `sign-abs`（域公理）、`sign-sum`（全正/全负）、
  `eq-times-zero`、`eq-num`。
- 纪律：结构不等**不**产出 No（`_poly_eq_check` 只证 Yes 不证 No）——No 必须来自账本或域，
  避免结构性结论短路账本推导（例：`x=0` 入账后 `x*y=0` 必须 Yes）。

### 1.5c 域对象 Domain（2026 修订）

- `cas/domain.py`：`R/Q/Z/C` 单例；原子谓词 `nonneg(t, ctx)` / `pos(t, ctx)` / `contains(t)`
  返回 `True/False/None`（零依赖，只读 term + 账本，不调 decide——防循环）。
- 原子层只做数值/常数/账本直查；结构组合（Times/Power/Plus 符号）归 decide 的 derive 规则。
- 全局假设集中化：平方非负、|x|≥0、π/e 正性、正有理数折叠条件——全部改走域谓词；
  未来支持复数域 = 换域对象，不挖散落的 if。

### 1.5d 域推理层（2026 修订：变换 generic，域按需）

- `dom_condition(t)`（domain.py）：递归提取定义域约束——`Log(a) -> a>0`、
  负整数幂 `a^-k -> a≠0`、偶分母有理指数 `a^(p/q) -> a≥0`、
  负有理幂 `a^-e`：偶分母 -> `a>0`，奇分母 -> `a≠0`。纯结构，不判值。
- `satisfiable(constraints, ctx)`（decide.py）：3VL 可满足性——对每条约束，在其
  他约束+账本下问 `decide(c)`/`decide(¬c)`，证伪才答 NO（"检死"）；无矛盾 → UNKNOWN。
  排自证：c 自身不入临时账本。
- `domain_ok(fact, ctx)`：`satisfiable(dom_condition(fact), ctx)`——assume 的域闸门。
- **默认策略与行业一致**：变换 generic（不做全量域检查），域问题按需检出；
  比 Mathematica 多一层：assume 条件时若条件本身无定义（如 `ln(-x²)≠0`）→ 直接拒绝
  （"domain empty"），讨论域空提前现形。
- 配套修复：parser 前缀 `-` 绑定松于 `^`（`-x^2 = -(x^2)`，此前误作 `(-x)^2`——
  对 `ln(-x^2)` 的域判定是致命的）；**`^` 为右结合（`2^3^2 = 2^(3^2) = 512`）**；
  `_sign_of_term` 增第四态 2（非负，可能零），
  sign-times 乘积符号精确化（`-x²>0 → NO`、`x²≤0 → UNKNOWN`、`x*y<0` 保持可判）；
  `cmp-via-eq` 规则（账本 `x=5` → `x<3` 判 NO，常数等式绑定的序结论）；
  parser 统一 `ln` → `Log` 头（与 term 构造器一致，消除双头潜伏不一致）。

---

## 2. 分层

```
L7  策略      cost 单调下降的化简策略；[后期] 积分/求解策略 = apply 上的搜索函数
L6  会话      状态 = 当前式 + step log + 义务队列 + 账本 + 规则库；四通道；path 寻址
L5  化简      per-head 分发 + 属性归一 + 规范形注册（自底向上）；eq 三值
L4  上下文    账本 + decide 表 + 义务队列 + ex falso 锁
L3  领域地图  四梯队（§4）：算术/多项式 -> 求解（方程/线代/不等式）-> 初等函数域 -> 微积分目标层
L2  规则      Rule = (pattern, template, guard, 方向, 通道标志)；per-head 索引；热重载
L1  匹配      洞模式；规范形结构上匹配；AC = 排序归并 + 有界回溯；可匹配 quote 形式
L0  项        驻留不可变 Expr + 绑定词；构造即规范化；equal = 指针
```

**效率分层**：规则/上下文 = **外壳**（交互层）；规范形+算法 = **内核**（热路径直达，不过规则链）。
**工程约束**：纯 Python；核心变换路径用**显式工作栈**（simplify/subst/cost/expand/to_str
全部迭代化，核心与展示/分析路径零递归，不依赖 Python 递归栈）；预算按节点计。

---

## 3. 匹配器（我们的算法）

- 模式 = 项 + 洞：`?x` 单参洞、`??x` 序列洞、**类型洞 `?x::pred`（✓ 已落地：num/int/rat/sym/const/expr，
  匹配时结构检查，无需上下文；语义谓词如正负走 guard/decide。yacas `_x_IsNumber` 同款）**、
  洞守卫 `?x :: odd`（语义层，待建）、备选 `?x|?y`、
  **同名重复洞**（同名洞必须匹配同一项--驻留后就是指针判等，O(1) 免费实现）。
- **在驻留规范形上匹配**：双方构造时已规范化 ⇒ "x³ 里认出 x²" 这类**结构出现**天然成立，
  替换后重构造（自动再规范化）。
- **AC 头归并匹配**：参数已全序排序 ⇒ 双指针归并；仅多序列洞触发回溯，且设枚举上限。
  [教训：通用 AC 穷举是 NP——排序使常见情形无回溯。]
- **OneIdentity（✓ 已落地）**：带单位元的 AC 头（Plus→0、Times→1）模式可匹配裸项：
  `?a+?b` 匹配 `x` 产出两组绑定（x,0)/(0,x)，`?a*?b` 同理（单位元 1）；序列洞可绑空元组；
  类型洞守卫在单位元绑定上同样生效（`?a::num` 只吸 0）；**非洞子模式不吸收单位元**
  （2·?u 不匹配裸 x）。[mathics-core attributes.py 同款实据]
- **匹配与求值解耦**：`quote('e)` 形式可被匹配和替换；规则左侧（pattern 段）天然不求值。
- **绑定词交互**：洞不得落在绑定变量位；body 内被绑变量是**不透明符号**，外界同名替换不得捕获。
- **等式即规则（约束消费）**：账本里的等式（如换元 `u = cos x`）注册为**带方向**的替换规则，
  化简按 cost 权衡方向——换元真正生效，不只是记录。
- **守卫 = 3VL**：`Yes` 应用 / `No` 跳过 / `Unknown`：自动通道跳过、建议通道呈现并记义务。
  守卫判定走 decide 表；条件项 `Proviso(expr, cond)` 随结果流动 + 同步入账（双通道）。

---

## 4. 地基领域地图（四梯队，按依赖排序）

> 地图由**目标驱动**（积分终点 + 用户点名清单），不是参考系统目录。
> 每个域标注**谁消费它**--没有消费者的域不上地图。梯队 = 建造依赖顺序。

### 梯队一：算术与多项式代数（一切的基底）

| 域 | 内容 | 谁消费 |
|----|------|--------|
| Z/Q | 精确算术、gcd/lcm、模、素性 | 所有 |
| 多项式 | 稀疏字典、带余除、gcd（Q 上走 primitive part + Gauss 引理）、resultant（Sylvester）、discriminant、**因式分解（Zassenhaus：DDF + Cantor-Zassenhaus + 整数 Hensel 二次提升 + 组合）** | 有理函数积分、方程求解、消元 |
| 有理函数 | 互素规范形、**部分分式 apart（CRT 拆分 + 连除递推；Hermite 分解留给积分层）** | 被积函数主体、恒等化简、求和裂项 |
| 代数数 | **RootOf 名词**（最小多项式+隔离区间索引）、根式表示、minpoly 判等、算术 | **M1 即需要**：RT 对数系数是代数数（∫dx/(x³−1) 的 log 系数）；方程求解闭式。✓ 最小版已落地：RootOf + ℚ(α) 域（扩展 Euclid 求逆）+ 幂和迹 |

### 梯队二：等式与不等式求解（引擎与算法的公共需求）

| 域 | 内容 | 谁消费 |
|----|------|--------|
| 方程求解 | 线性方程/组；多项式方程（低次根式、高次 RootOf 名词）；消元（resultant）；**多元多项式方程组（Gröbner 基，中期）** | 积分中途解方程（待定系数、Risch 方程）、换元反解、递推特征方程 |
| 线性代数 | 矩阵/向量项头、行列式（精确分数消元）、线性系统（高斯消元）、秩、**特征值/特征向量（对角化；dsolve 线性系统前置）** | 待定系数法（部分分式）、Risch 的函数域线性系统、方程组 |
| 不等式 | 一元线性链（全序消解，**可判定**）；**一元多项式 Sturm 符号表 ✓ 已落地**（cas/ineq.py，
  精确有理根 + 根隔离区间端点，偶重根不换号，解集 = 区间并）；**解集输出形态（Interval/FiniteSet/Union 一等结构）** | 定义域、收敛区间、decide 表 `ord` 族的求解侧 |

### 梯队三：初等函数域（被积函数材料）

| 域 | 内容 | 谁消费 |
|----|------|--------|
| 幂/根 | 幂律合并；根式幂化 | csign 依赖、根式积分 |
| exp/log | exp 塔、ln 双向（带条件） | Risch exp/log 子情形 |
| trig/双曲 | 恒等式规则、exponentialize 算子（转 exp 塔） | 三角积分转 exp 域。✓ 已落地：多角度基规范形（trig_reduce）+ tan(x/2) 代换积分（sin x/cos x 有理式，复用 M1，`[VERIFIED]` 链式验证）+ **双曲域**（Sinh/Cosh/Tanh spec 注册 + hyp.rules，导数/奇偶/特殊点/数值层零核心改动）；边界：sin(ax+b)/tan 积分未覆盖 |
| 分段/绝对值 | Piecewise 一等头、分段归一；abs = 分段 | 分段积分、定积分分段 |

### 梯队四：微积分目标层（项目终点）

| 域 | 内容 | 谁消费 |
|----|------|--------|
| 导数 D | 规则式微分器（线性/乘积/链式 + 各函数 D 表） | **verify 通道**（一切积分结果的兜底）、机械算法 |
| 极限 | 首项分析（级数法）、**Gruntz 支配项算法**（exp-log 域完备算法，对标 sympy 701 行）、洛必达/夹逼（带条件策略） | 定积分判敛、级数收敛 |
| 级数 | Taylor 展开、幂级数项头、收敛半径 | 极限工具、渐近展开 |
| Σ/Π 求和 | 线性/指标平移/裂项；**Γ/Pochhammer/阶乘算术**（Gosper 前置，对标 sympy ~1100 行）；超几何项 Gosper（对标 222 行） | 差分方程、差分验证 |
| 常微分方程 | 一阶线性/可分离；常系数线性系统（exp(At) 特征值法）；线性递推（特征方程，见 Σ 行） | 差分验证、dsolve 终点扩展 |
| 差分方程/递推 | 一阶线性差分（= Gosper 核心）、常系数线性递推（特征方程） | 求和闭式、递推化简 |
| 不定积分 | **策略层**：基本表+换元+分部+恒等式重写（可解释）；**算法层**：有理函数 Hermite+Rothstein-Trager（全算法零启发式）；Risch 子情形分期；**Risch 前置真模块：表达式↔微分域塔转换器**（塔 = 单项列上的多项式/有理函数）+ **塔上导数表**（Dt = D(inner)）--没有它 Risch 无法启动 | 终点能力 |
| 定积分 | NL 定理（连续性条件）、分段处理、瑕积分判敛（可判定比较片段）、换元换限（单调条件）；**不承诺无初等原函数情形**（∫₀^∞ sinx/x 类需留数/参数微分，远期可选） | 终点能力 |

### 横切能力（跨梯队，随用随建）

- **equivalent(a, b) 三值**：符号相等判定的**统一公共 API**——指针同构 -> simplify 归零 ->
  decide 片段（poly_eq/账本）-> 诚实 UNKNOWN。现状：等价能力散在四处（simplify 归零、verify 微分、
  decide 片段、驻留指针），各自为政；收拢为一个入口后所有梯队共享（化简目标、验证、条件合并都用它）。
  详细管线设计见 §11。
- **步骤保真验证**：step log 已记 before/after，补"每步变换保持等价"的验证通道（新式减旧式化简检 0），
  可解释性的核心——每个 step 都能回答"这步为什么合法"。
- **判别树**：匹配器性能（已知债务 3），规则库增大时启用。
- **数值求值层（✓ 已落地：cas/evalnum.py，验证/抽查工具，非计算通道）**：
  `eval_exact`（环层精确有理）/ `eval_approx`（超越函数走 FunctionSpec.numeric）/
  `sample_agrees`（结构化采样 + 极点保护，只产一致/未知，**绝不产否证**）。
  与"纯符号、无浮点"哲学不冲突：工具只做裁决，不进主通道。
- **差分测试（✓ 已落地：tests/test_differential.py）**：sympy 仅作测试预言机，
  对照环层求值/化简保语义/积分回微分/因式分解 factor_list；仅测试期依赖，运行时零依赖。

### 里程碑（自包含路线）

- **M0 机制基底**：L0–L2、L4–L6 骨架 + 导数 + verify 通道（diff 化简判 0）。
- **M1 多项式闭环**：梯队一 -> **有理函数不定积分**（Hermite+RT，只用 gcd/带余除/结式）+ verify。
  ✓ 已落地：代数数最小版（ℚ(α) 域 / RootOf / 幂和迹）、
  Hermite 单因子幂递推（apart 分解后逐因子降幂）、对数部分（线性闭式 + 高次 RootOf：
  Σ_j C(β_j)·ln(x−β_j)，C = f·inv(p') mod p）、**符号精确验证通道**（D(结果) 逐项
  合成回 P/Q：有理项 + 线性 log 组 + RootOf 组的迹公式 Σ_r (−1)^r·Tr(C·e_r^{(j)})·x^{n−1−r}）、
  REPL `:integrate`（输出带 [VERIFIED] 标记）。
  [诚实记录：当前 apart 实现依赖 Zassenhaus 因式分解（非纯 CRT 路线）；
  RootOf 实根已获 Sturm 隔离区间（algnum.real_isolation），复根仍只有共轭类编号；
  三角路径的 [VERIFIED] 只覆盖 t 域有理积分，半角代回本身未验证。]
- **M2.0 地基补强（反硬编码 + 判等收口，一切后续函数域的前置）**：
  ① FunctionSpec 函数内核注册表 ✓ **已落地**（cas/spec.py；奇偶规则自动生成；硬编码表退役）
  ② 数值求值层 + sympy 差分测试 ✓ **已落地**（cas/evalnum.py + tests/test_differential.py）
  ③ equivalent() 统一管线 ✓ **已落地**（三角层接线 YES；采样标 PROBABLE 不产否证）
  ④ 策略化简器形式化 ✓ **已落地**（auto 写 step log、优先级排序、已见集防振荡）；
  配套：apply 无参全式搜索、类型洞、DSL `prio N`
  ⑤ 内核命令注册机制 ✓ **已落地**（KernelCmd 注册表，消除 REPL 硬编码）
  ⑥ declare/属性消费最小闭环 ✓ **已落地**（integer 区间收紧、符号属性映射）。
  M2.0 收官。此后新增函数域 = 写 spec 条目 + 规则文件，核心代码零改动。
  **结构性债务清偿记录**：多元 gcd ✓（mgcd + div_exact，sympy 差分验证）；
  显式工作栈 ✓✓ **全额清偿**（simplify/subst/cost/expand/to_str 全迭代化，零递归残留）；
  匹配器 OneIdentity ✓（裸项匹配 + 单位元入洞，mathics 属性同款）；
  系数域抽象部分完成：多变量约分/参数有理式/参数化低次求解已通；
  **剩余**：Poly 全参数化系数（ℚ(params) 上的 udivmod/gcd/积分）——前置条件 = ℚ(params) 上的因式分解；
  RootOf 复根隔离（实根已由 Sturm 解决，复根仍为共轭类编号）。
- **M2 初等域 + 教科书积分**：梯队三 + 策略通道可解释积分 + 梯队二基础件（线性系统/线性不等式链）。
  ✓ 已落地：完整多项式算术（resultant/discriminant/Zassenhaus 因式分解/apart 部分分式）+ REPL `:factor` `:apart` +
  三角层（Chebyshev 多角度基规范形 + t=tan(x/2) 积分复用 M1）+ 双曲域（spec 注册 + hyp.rules）+
  **策略通道可解释**（integrate 报所用方法并入 step log；规则步逐条、算法步报名+验证态）+ REPL 交互层（%N 历史/:steps）。
- **M3 定积分**：极限 + 级数 + NL + 分段 + 判敛。
- **M4 求和/差分**：Gosper、常系数递推。
- **M5 Risch 分期**：exp/log 子情形 -> 三角（经 exp 塔）-> 完整决策程序（远期，含不可初等的证明）。

---

## 5. 规则与 DSL（规则=数据）

```
# rules/trig.rules
rule sin2   = sin(?x)^2 + cos(?x)^2 -> 1
rule sin_neg = sin(-?x) -> -sin(?x)

# rules/log.rules   —— 同一恒等式两个方向，成对呈现
rule log_e = log(?x*?y)  -> log(?x)+log(?y)   guard ?x>0 && ?y>0   as expand
rule log_c = log(?x)+log(?y) -> log(?x*?y)    guard ?x>0 && ?y>0   as combine

# rules/sum.rules   —— 分析性质 = 带条件策略规则
rule sum_swap = sum(sum(?f,?k),?l) -> sum(sum(?f,?l),?k)   guard abs-conv(?f)
```

- **方向标签**（expand/combine）：建议通道成对列出，用户选；自动策略按 cost 选。
- **通道标志**：`auto`（化简器内触发，**仅无条件安全规则**）/ `manual` / `suggest` / `strategy`。
- 规则库文件**热重载**；加领域 = 写规则文件，核心代码零改动。

### 5.1 两套机制的边界原则（normalizer vs 规则库）

- **normalizer（Python 注册表）= 表示规范形**：凡"同构类"变换（flatten、全序排序、
  常量折叠、幂合并、`x·x→x²`、同类项合并）必须进 normalizer——驻留项要求"等项 = 指针"，
  一旦同一表示生成两个对象，匹配与相等就崩。此类变换无条件安全、永不 asksign。
  **环规范化已内建于构造器 mk**（basic.rules 的 pow_one/zero_plus/one_times 因此退役）。
- **规则库 = 结构变换**：改变数学结构的变换（`sin²+cos²→1`、log 展开）进规则库，
  带守卫/方向/通道。`auto` 通道是两者汇聚点：`auto = normalizer ∪ {auto 规则}`，
  接受准则 = cost 单调不增（预算内 fixpoint）。
- **规则库的身份 = 定理库**（2026-08 澄清）：规则文件里放的是**声明式数学事实与条件推导**
  （恒等式、带域守卫的展开/合并、换元等式、FunctionSpec 公理派生的定理）——可审计、用户可扩展。
  **代码逻辑性算法不是规则**：高斯消元、因式分解、Hermite 约化等是过程而非改写规则，
  留在内核代码（机械算法通道），正确性由 verify 通道背书（因式回乘、积分回微分），
  不转成规则数据；decide 的 derive 推理规则属元层特例，同样留在代码。
- 判断口诀：**"不改变项语义的表示归并"进 normalizer；"改变项语义（需守卫）的定理"进规则库；
  "过程性算法"进内核代码 + verify 背书。**

### 5.2 函数内核注册表 FunctionSpec（反硬编码地基，✓ 2026-08 落地：cas/spec.py）

**问题**：当前每新增一个函数要同时改 N 处——diff 导数表、decide 公理（手写 |sin|≤1）、
pprint 打印名映射、parser 头名约定、domain 特例、rules 手写奇偶性规则。
硬编码散落 = 每个新函数域都返工；微分方程需要的 Γ/Pochhammer/Bessel 族不可承受。

**形态**：每个函数头一份声明式注册，消费者全部从注册表读取：

```python
FunctionSpec(
    name="Sin", arity=1,
    parity="odd",            # 自动生成 sin(-x) -> -sin(x)（不手写规则）
    period=2π,               # 周期：化简/极限/级数消费
    special={0: 0, π: 0, π/2: 1, ...},   # 特殊点：mk 构造即折叠
    deriv=("Cos",),          # 导数表：diff 消费（替代 _TABLE）
    bound=(-1, 1),           # 有界性：decide 公理自动生成（替代手写 axiom）
    dom=None,                # 定义域：dom_condition 消费
    to_exp=...,              # 到 exp 塔的翻译算子（策略动作，M2+ 消费）
)
```

- **消费者清单**：mk（特殊点折叠）/ loader（奇偶性/周期性规则自动生成）/ diff（导数表）/
  decide（有界公理）/ dom_condition（定义域）/ pprint（打印名）/ evalnum（数值求值 numeric 字段）。
  ✓ 已迁移：diff._TABLE / pprint 小写映射 / decide 手写 |sin|≤1 公理 / dom 的 Log 分支全部退役；
  sin/cos/tan 奇偶规则由 `gen_rules` 自动生成（origin='spec'，auto 通道），trig.rules 手写版退役。
- **纪律**：新增函数只允许写 spec 注册 + 规则文件；**禁止在任何消费者模块里为新函数加 if 分支**
  （作为代码评审验收标准）。这是"未来实现积分/微分方程不返工"的制度保证。
- **已注册**：Sin/Cos/Tan/Exp/Log/Abs/Atan/Arcsin（arity/print_name/parity/deriv/bound/dom/special 按需）。

---

## 6. 化简 / 规范形 / 停机

- **核心化简器只放无条件安全规则**（flatten、排序、常量折叠、属性归一）；
  带条件规则只在手动 / 建议 / 策略通道。核心化简**永不提问**。
  实现分工：环层规范形在构造器 mk 内完成；`simplify` = 自底向上重建（每层经 mk，
  子项变化自动向上传播）+ 预算；`register_norm` 为后续头（如 Piecewise）的扩展入口。
- **cost(e) = 加权节点计数**（权重表用户/规则库可调）。
  自动策略**单调下降才接受**（接受准则保证停机）。
  [教训：单调接受准则是化简停机的最简充分条件——借思想不借实现。]
- **规范形自底向上注册（层表，每层幂等+终止）**：全局规范形不存在（Richardson 定理：
  丰富初等函数类的零等价不可判定）⇒ 参考系统（Mathematica / SymPy / Maxima）一致收敛于
  **"分层投降"：层内规范形 + 跨层翻译算子 + 层外策略搜索**。pyCAS 同款：
  | 层 | 规范形机制 | 状态 |
  |----|-----------|------|
  | 整数/有理 | 构造即规范化（term.py） | ✓ |
  | 多项式 | 降幂系数数组（poly.py） | ✓ |
  | 有理函数 | 互素规范形（ratfunc.py） | ✓ |
  | 三角多项式 | Chebyshev/多角度基：sinⁱx·cosʲx 多项式 → ∑(aₙsin nx + bₙcos nx) 唯一线性组合（= ℚ[sin,cos]/⟨sin²+cos²−1⟩ 商环，成员判定可计算——SymPy trigsimp_groebner 同款）。✓ 已落地：trig_reduce（复数 Laurent 系数）/trig_equivalent；t=tan(x/2) 代换积分复用 M1（sin x/cos x 有理式） | M2 |
  | exp/log 塔 | Risch 结构定理：塔内元素表示唯一、零等价可判定（Maxima radcan 的基础；配合 §4 塔转换器） | M5 |
  | 分段 | 条件序归并规范化（不相交区间、条件归一）；每支递归回本层 | M3 |
  跨层翻译算子（策略动作，不进规范形；带守卫/义务）：Exponentialize（TrigToExp/ExpToTrig）、
  PowerExpand（带假设——走 §1.5d 域闸门，√(x²)=|x| 的分支义务化）。
  层外混合表达式 = 策略通道（方向标签成对规则 + cost 单调下降 + 义务队列）——不承诺完备，
  结果可解释（step log），与"可判定片段内完备 + 片段外拒答"的立场一致。
  可判定片段 eq = `True/False`（指针比较）；不可判定片段（exp/log/trig 混合）eq = `Unknown` → 拒答。
- **求值预算**：显式栈求值器 + 步数上限，超限即停并报告"预算超限"。
  用户规则无法静态保证停机 ⇒ 预算是必加工程件。
- **形式层 vs 分析层**：形式恒等式（Σ 线性/指标平移/拆前缀）无条件进核心；
  换序/重排/Σ↔∫ 带收敛条件走策略规则：可判定收敛片段自动判，否则 Proviso 标"形式结果"或记义务。

- **常数问题（诚实边界）**：超越混合的零等价**不可判定**（Richardson 定理）-> eq = Unknown 拒答；
  **verify 同为三值**：已验证（化简得 0）/ 未通过（化简得非 0，报错）/ **未验证（Unknown，如实报告）**；
  区间算术抽查 = 远期可选兜底。

---

## 7. 上下文细则

### 7.1 约束收集与分析（一等机制）

**来源五类**（各通道产出统一入账本，origin 标注）：
① 用户 `assume`/`declare`；② **规则守卫**（每步 apply 的 guard 条件）；
③ **域公理**（分母≠0、log 定义域）；④ **分支切割**（log/atan 的辐角条件）；
⑤ **换元条件**（可逆性/单调性）。

**生命周期**：
`收集`（各通道 -> 账本条目）-> `分析`（惰性：查询时 decide 三值判定 + 矛盾锁）->
`消费`（等式即规则反向重写表达式；不等式划分支帧）-> `裁决`（义务队列：用户作答 -> 重放）->
`回滚`（作用域退出 / 撤销该步）。

### 7.2 细则

- 账本事实种类：不等式、等式（含换元）、属域、符号、属性；全部带 origin。
- **ex falso 锁**：decide 检出矛盾 → 会话冻结：后续 feed/apply/auto/answer 一律拒绝，
  报告**矛盾链**（账本 origin 使矛盾可解释：哪条用户假设 + 哪步推导 + 哪条公理冲突）；
  undo 撤掉引发矛盾的步后自动解锁。

### 7.3 分支原语（2026 修订：分类讨论的地基）

- `Context.clone()`：浅拷贝 entries（条目不可变，共享安全）；marks 不复刻（子上下文独立）。
- `Context.check_and_assume(fact) -> (T3, why)`：**统一入账闸门**——域检死（§1.5d）→
  矛盾锁 → 入账。Session 三入口（assume / answer / 规则 guard 入账）全部走它，
  不再有绕过检查的直入账路径。answer 被拒 → 义务保留、原因回报。
- `Context.branch(c1, c2, ...)`：每条件 = clone + 闸门入账 → `Branch(cond, ctx, status)`
  （status ∈ open/empty）。**分支空 = 分支条件与父账本矛盾的检出**；empty 分支不再参与推导。
- `_chain_query` 数值界通道：账本常量界（lo/hi 表）直接裁决——`x>0 → x≥−5 YES`、
  `x>100 → x<10 NO`、`x<3 → x<5 YES`（弥补纯 BFS 对"项间无边"的盲区，分支空检测依赖它）。
- 义务 `pending` 列表化：同一义务可记录多个 (rule, path)，answer 一次逐处重放。
- **域三件套**（符号特征 + 域标志 + 运行时谓词分发）：declare(x, integer) = 账本属性条目；
  "R 上恰好是 Z" = 数据本来就是 `Int` 原子，按实际类型走算法，**无转换机制**。
- 有界性公理条目（|sin|≤1、|cos|≤1）供夹逼与极限。
- 点求值 `at(e, x=a)`：符号算子，作用于 quote 形式（`at('∫x²dx, x=0)` → 0，不算积分）。

---

## 8. 重建清单

| 文件 | 内容 | 层 |
|------|------|----|
| `cas/term.py` | 驻留 Expr / 原子 / quote / 构造即规范化 / 总序 | L0 |
| `cas/match.py` | 洞模式匹配：结构匹配 / AC 归并+有界回溯 / 3VL 守卫 | L1 |
| `cas/rules.py` | Rule / RuleSet / apply(rule,path) / per-head 索引 | L2 |
| `cas/loader.py` | DSL 解析 → RuleSet，热重载 | L2 |
| `cas/context.py` | 账本 / 回滚点栈 / ex falso 锁 / 等式即规则注册 | L4 |
| `cas/decide.py` | 谓词族判定表 sign/ord/dom/eq + 3VL 组合 + 域公理 | L4 |
| `cas/simplify.py` | per-head 化简 / 属性归一 / 规范形注册 / cost | L5 |
| `cas/arith.py` `cas/poly.py` `cas/ratfunc.py` | 梯队一：精确算术 / 多项式 / 有理函数 | L3 |
| `cas/solve.py` `cas/linalg.py` `cas/inequal.py` | 梯队二：方程求解 / 线性代数 / 不等式 | L3 |
| `cas/power.py` `cas/exp_log.py` `cas/trig.py` `cas/piecewise.py` | 梯队三：幂根 / exp-log / 三角 / 分段 | L3 |
| `cas/diff.py` `cas/limit.py` `cas/series.py` `cas/sum.py` `cas/recurrence.py` | 梯队四：导数 / 极限 / 级数 / 求和 / 差分递推 | L3 |
| `cas/integrate.py` | 不定/定积分：策略通道（可解释）+ 算法通道（Hermite+RT；Risch 分期）+ verify | L3/L7 |
| `cas/session.py` | REPL 四通道 / step log / 义务队列 / 重放 / path 导航 | L6 |
| `cas/parser.py` `cas/pprint.py` | 解析 / 打印 | L6 |
| `cas/errors.py` | `Undefined`/`Infinity` 原子 / 预算超限协议（不崩溃不静默） | L0 |
| `rules/*.rules` | 领域规则库（trig/log/sum/strategy…） | L2/L3 |
| `tests/` | 差分测试（符号 vs 数值抽查）+ 验收回归 | 全线 |

**建造顺序（按里程碑，对应 §4）**：
**M0** L0 驻留项+quote -> L1 匹配器 -> L2 规则+apply+step log+预算+DSL -> 导数+verify ->
L4 账本+decide+义务 -> L5 化简+规范形 -> L6 会话。
**M1** 梯队一（Z/Q -> 多项式+gcd -> 有理函数）+ **代数数最小版（RootOf 名词/根式/minpoly 判等）** -> 有理函数不定积分（Hermite+RT）。
**M2** 梯队三初等域 + 策略通道积分 + 梯队二基础件 + **因式分解（Zassenhaus）**。
**M3** 极限（Gruntz）+级数 -> 定积分。**M4** 求和+差分（Γ/Pochhammer -> Gosper/递推）。**M5** Risch 分期。

---

## 9. 验收清单（用户点名的场景）

| 场景 | 机制 |
|------|------|
| ×cosx/cosx 需 cosx≠0 | 守卫 3VL → Unknown 记义务 / Proviso 双通道 |
| x²<0 在 R 上 | 域公理条目 → decide 检出矛盾 → 冻结 + 矛盾链报告 |
| 积分中途解方程 | 子目标 = 换一套规则集继续 apply（无特殊子目标抽象） |
| 积分需分类讨论 | sign 族判定 → 每分支一个账本回滚点 → 结果合并 |
| 分段函数 | Piecewise 一等头 + 分段归一 |
| ln(xy) 双向 | 方向标签成对规则，用户/cost 选向 |
| 换元 | 等式入账（origin=user）+ 注册为带方向替换 |
| 条件收敛级数重排 | 带守卫策略规则：可判定收敛自动判，否则 Proviso"形式结果" |
| R 恰好是 Z | 运行时类型分发，Int 原子直走 Z 算法 |
| 用约束化简 | 账本等式（x²=1）注册替换 → x³−x → 0 |
| 结构替换 | 规范形上匹配：x³ 认出 x² 并替换 |
| 点求值 | at(e, x=a) 作用于 quote 形式 |
| 可解释 | step log：每步规则+位置+前后+守卫值，随时回放 |
| 积分中途解方程（待定系数） | 子目标=换规则集；线性系统走 linalg 精确消元 |
| 瑕积分判敛 | 可判定比较片段自动判，否则 Proviso/义务 |
| 积分结果验证 | verify 三值：化简得 0=已验证 / 非 0=未通过（报错）/ Unknown=未验证（如实报告），强制过 |

---

## 10. 数据结构草图

```
ExprId        = int                                  # 驻留表句柄
Expr          = (head: Sym, args: tuple[ExprId])     # 不可变、驻留、构造即规范化
Atom          = Sym(name) | Int(v) | Rat(p,q) | Const(π,e,i,γ)
Pattern       = Expr + 洞(?x / ??x / ?x::guard)
Rule          = {id, pattern, template, guard,
                 tags: {direction, channels, auto}, cost_hint}
LedgerEntry   = {fact: Expr, kind, origin: user|step(id)|axiom}
Context       = {entries: [LedgerEntry], marks: [int]}   # marks = 回滚点栈
Obligation    = {q: Expr, affects: [step_id], branches: [{ans, consequence}]}
Proviso       = 项头 Proviso(expr, cond)                 # 条件随结果流动
Step          = {id, rule_id, path, before, after, guard: Yes|No|Unknown, dcost}
Session       = {current: ExprId, log: [Step], obligations: [Obligation],
                 ctx: Context, rules: RuleSet, budget: int}

decide(fact, ctx) -> Yes | No | Unknown       # 谓词族注册表 + 3VL 组合

# 求值 = 显式工作栈 + 预算 + 步骤日志（非递归，Python 栈安全）
def run(e, ctx, sess):
    work = [Job(e, root_path)]; budget = sess.budget
    while work:
        budget -= 1
        if budget < 0: raise BudgetExceeded(step_log=sess.log)
        job = work.pop()
        for r in sess.rules.indexed_for(job.head):
            m = match(r.pattern, job.expr)               # 规范形上匹配
            if m:
                g = decide(r.guard, m ⊕ ctx)             # 3VL
                if g is Yes:   push(Subst(r.template, m)); break
                if g is Unknown: sess.note_obligation(r, m)   # 不阻塞
        else:
            push(Kernel(job))    # per-head 内核分发（热路径，不过规则链）
```

---

## 11. 判等与化简：成熟系统的做法与 pyCAS 形态（2026-08 新增）

**根本事实（Richardson 定理）**：含 sin/exp/abs 的函数类零等价不可判定——
**全局规范形不存在也不可能存在**。这不是实现缺陷，是数学定理。
Mathematica / Maple / Maxima / SymPy 一致收敛于同一套三件套：
**分层规范形 + 跨层翻译算子 + 层外搜索式化简**，判等 = **多阶段管线 + 诚实 UNKNOWN**。

### 11.1 成熟系统实际做法

| 系统 | 层内规范形 | 跨层/搜索 | 判等 |
|------|-----------|----------|------|
| Mathematica | Automatic simplification（环层规范）；Together/Expand 有理函数 | FullSimplify = 变换空间搜索 + ComplexityFunction；TrigToExp/FunctionExpand/PowerExpand 为翻译算子 | Equal：结构化简归零 + Together；PossibleZeroQ 数值启发式；$Assumptions 下 Refine |
| Maple | automatic simplification | simplify 族按域 | testeq：符号尝试 + 随机数值采样（概率性，官方明言） |
| Maxima | CRE 规范有理形；radcan（exp-log 塔规范形，基于 Risch 结构定理） | ratsimp/trigsimp 按域 | equal() = ratsimp(a−b)=0；is() 走假设库；判不了 asksign 提问 |
| SymPy | 构造即规范化（环层） | simplify 编排各域 simplifier；fu 算法（三角） | equals()：符号尝试 + 随机数值采样 |

**共性要点**：
1. **环层（多项式/有理函数）是唯一全局可判定层**——驻留/CRE/Together 都在解这一层（pyCAS 已对齐）。
2. **每个超越函数族各有自己的"小规范形"**：三角多项式（商环 ℚ[sin,cos]/⟨sin²+cos²−1⟩，
   SymPy trigsimp_groebner 同款，pyCAS 多角度基已落地）、exp-log 塔（Risch 结构定理保证表示唯一，
   Maxima radcan 的理论基础，pyCAS M5）、代数数（minpoly 判等，pyCAS algnum 已落地）。
3. **层间不做规范形合并，只做带条件的策略性翻译**（Mathematica convert 思想）：
   Exponentialize/PowerExpand 是策略动作，带守卫/义务，不是化简义务。
4. **判等是管线不是单一算法**：指针 → 归零 → 层内决策过程 → 翻译重试 → 数值采样 → UNKNOWN。
5. **数值采样是探测器不是证明**：Maple testeq / SymPy equals 都用，但结论带概率色彩；
   pyCAS 只允许它进验证/抽查通道（标 PROBABLE），不进 decide 的 YES 通道。
6. **微分验证是不对称捷径**：验证 D(F)=f 往往比直接判等容易——verify 通道已落地。

### 11.2 pyCAS 形态：equivalent(a, b, ctx) 统一管线

```
1. 指针同一（驻留免费）                                        -> YES
2. simplify(a−b) 归零（环层规范形）                            -> YES
3. 层内决策：多项式恒等（_poly_eq_check）/ 三角多项式多角度基
   （trig_equivalent，待接入）/ 代数数 minpoly（algnum，积分层在用）  -> YES / NO
4. 账本片段（decide Eq）+ 翻译算子重试（Exponentialize/PowerExpand，
   策略动作，带义务）                                          -> YES / NO
5. 数值采样抽查（✓ 已建）：结构化采样点 + 极点保护 -> PROBABLE（不是 YES，不产否证）
6. 全部未命中                                                  -> UNKNOWN（拒答，永不静默错）
```

现状：管线全通（1/2/3/4/5 均已实现）；三角层已接线（sin²+cos²=1 符号 YES）；
**化简 = 搜索的形态**（层外混合式：cost 单调 + 方向标签成对规则 + 义务队列）已在 §6 定稿。

**FullSimplify 式搜索不做（2026-08 裁定）**：搜索式化简的价值前提是大定理库 +
调校过的 ComplexityFunction——当前规则库规模下搜索无素材；Richardson 定理保证超越函数类
无终止保证，只能预算硬切，投入产出比远低于内核建设。重估条件：规则库百条级且
auto 的 cost 单调接受准则成为可证瓶颈（如大量合法化简被单调性拦截）。

---

## 12. 参考系统教训（2026-08 实据读源版）

> 此前的"教训"是转述；本次通读本地五份参考源码（maxima / mathics-core / expreduce / yacas / SAINT）
> 后换为实据结论。立场不变：借思想不搬实现。

| 系统 | 实据（文件级） | 教训 → pyCAS 动作 |
|------|--------------|------------------|
| expreduce | `eval.go`：求值 = 哈希比较 fixpoint 循环 + 每项 `EvaledHash` 缓存（命中即跳过）；
  属性（Flat/Orderless/Hold/Listable）按头查询；Trace 是事后表达式 | ① 项 id 记忆化 ✓ 已落地（simplify._MEMO，驻留免费）
  ② 属性 = 按头声明式行为 → 并入 FunctionSpec |
| mathics-core | `core/attributes.py`：16 属性位集，含 OneIdentity、NumericFunction | OneIdentity ✓ 已落地（match._match_one_id，裸项匹配 + 单位元入洞）；numeric_function 供数值层（已由 spec.numeric 替代） |
| yacas | `scripts/stdarith.ys`：仅加法归约 ≈40 条声明式规则，带优先级数字与谓词守卫（`_x_IsNumber`）；
  内核小、数学全在脚本库 | ① 环规范化下沉构造器被反证为正确（yacas 为此付出几百条规则）
  ② 规则优先级/排序值得进 DSL（列入 M2.0 备选） |
| SAINT | `slagle.py`：AlgorithmRule（确定性、单结果）vs HeuristicRule（候选列表）分裂；
  `rules.py` 的 deriv 是 2700 行 if-elif 链（反面教材）；带类型洞 `Symbol('a',[CONST])` | ① 四通道设计获原型印证 ② FunctionSpec 的反面教材
  ③ 类型洞 = 洞守卫 `?x :: odd` 的前身（已在规划） |
| maxima | 92MB / 5100 文件（Lisp） | 规模感：通用 CAS 代码量 10⁵ 行级；pyCAS 以"可判定片段 + 拒答"为生存策略 |

**规模感**：yacas 标准规则库数万行脚本；mathics-core 单个 builtin.py 62KB。
规则数量必然爆炸——这正是"同构类变换进构造器/normalizer、规则库只放结构变换"（§5.1）的生存理由。


