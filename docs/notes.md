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
- **后 M3（ℚ(params) 全参数化 + 变形/域 + 真 hold）**：
  ℚ(params) 系数域全参数化（poly.py SymRat 参数有理函数系数域，is_param_poly 检测、
  混合算术、参数判别式 pos/neg/unknown 分类 + proviso，参数积分完备）；
  apart 推广到复合项原子（Log/Sin/Exp 作多项式变量）；
  ops 变形原语（term 层 num_den 支持 cos/log + mulfrac/divfrac）；
  变形命令因子域 proviso（mulfrac/divfrac：NO 拒 domain empty / UNKNOWN 记 proviso）；
  bsub 主支逆无实原像诚实报告（x=t² 识别 surjectivity 域问题，不再误报边界不可比）；
  equivalent 公共域采样（sample_agrees 域过滤，sqrt(x)²~x → PROBABLE）；
  quote 真 hold（parser 跳 mk 规范化保留反化简形 + 域约束；subst/instantiate 走 raw 路径）。
- **M4 求和/差分（一期）**：`cas/summation.py`——Bernoulli 数 + Faulhaber 幂和
  （Σk^p 闭式）、不定求和（差分原函数 S(x)-S(x-1)=f(x)）、定界求和
  （Newton-Leibniz 离散版 S(hi)-S(lo-1)）、差分回验；Gosper 算法（简化 z 多项式
  →完整 normal form 分解 P/Q=(a/b)(c(k+1)/c(k))，z=f/c 有理函数）+ 线性方程组
  求解；`_eval_inert` 接 Sum 名词、:sum 命令（后改 !sum）。覆盖：多项式 + 有理函数
  裂项求和（1/(k(k+1))、1/(k(k+2))），诚实拒答调和类（1/k、1/k²）。
- **手动/自动语法分层**：`:` 前缀 = 手动操作（逐步可控每步入账）；`!` 前缀 = 自动求解
  （算法黑盒 verify 背书）。kernel 注册表拆分（self.kernel 手动 / self.solver 自动），
  不兼容旧 `:integrate` 等（直接改；step log 内部 `kernel:xxx` 标识不变）。
- **手动交互扩展批（子项手术/等式代数/变形工具箱/微积分战术）**：
  调研定案——Maxima eqnflag + distribute_over、Mathematica 等式算术、SymPy Eq 算术
  三家收敛于"等式即二元容器"，pyCAS 以显式命令族落地（mk 保持纯规范化纪律，不做隐式线程化）。
  `:tree` 带路径子项树（选择器）；`:set`/`:rsub` 子项手术（equivalent 三态闸门：
  YES/PROBABLE 提交，UNKNOWN 拒绝——不可验证的篡改不放行，先 :assume 再重试；
  L0 的 term_at/replace_at 对 Bound 体 α-安全，底层零改动）；等式双侧命令族
  （add/sub/mul/div/neg/swap/zero_form/apply_both；div 域闸门 t!=0 记 proviso；
  apply_both 读 spec.injective 新字段做单射性诚实分级）；变形工具箱
  （expand/extract/separate/complete_square，_reshape_drive 统一驱动：等式目标
  自动作用两侧、任一侧失败整体拒绝；extract 逐项整除 + 负幂残留检测——
  mk 不拆 (a·b)^-1 且 times 重构会塌回原形，是两个实测教训）；微积分战术
  （usub 两级策略：精确微分分解 _quotient_cancel 顶层因子消去优先、主支逆退化；
  lhop 手动一步带不定形判定；parts 输出 u/dv/du/v 明细）。steps() 规则步补 note 显示。
  实现权衡判据链：模式可表达 -> 规则；要算才知 -> ops/: 命令；搜索+回验 -> ! 内核；
  原语编排 -> session tactic（本批全部为 tactic/ops 级，零新内核算法）。
- **等式双侧操作的域闸门（借用形教训）**：add/sub/mul both 初版误标"无条件安全"——
  加 ln(x-k) 会把解集静默收窄到 x>k，违反永不静默错。修正：四则统一走
  _term_domain_gate（dom_condition 三态：NO 拒 / UNKNOWN 记 proviso）。
  借用形 +ln(x-k)-ln(x-k) 的正确姿势 = quote（'ln(x-k)-ln(x-k) 保结构不被 mk 消、
  dom_condition 穿透 Quote 提取域约束）；裸形式在 mk 即合并（generic 语义），
  中间步的 proviso 在形式复原后保守保留（中间步确实收窄过，不假装没发生）。
  全命令域审计结论：separate/extract/complete_square/expand 域安全
  （分母保留 / 因子已在 terms 中 / 多项式全纯）；set/rsub 补 _new_domain_conditions
  （公共域采样只在重叠域比对，换入更窄定义域的项须显式记账；恒真约束与
  old 已携带约束跳过）；  extract 验证放宽到 PROBABLE（构造 = 分配律逆，结构可靠，
  超越因子采样最高 PROBABLE）；usub/lhop 的经典条件（g'!=0、G'!=0）由
  verify 背书链承担（docstring + manual 标注）。
- **decide 账本等式代入归一（符号等式背书）**：_eq_subst 原只允许数值侧账本等式
  （t=5 类）代入查询，符号等式（换元定义 t=sin(x)）被跳过——回代只能走会话规则
  权宜。修正：解除数值侧限制，Eq(u,v) 双向代入 + _MAX_DEPTH 防连锁
  （decide 相对账本的含义即"在假设下判定"，代入假设等式保真）。
  examples/06 回代改为 :rsub 直接过闸门（账本 Eq 消费，VERIFIED）。
- **等式链提取与对称性裁定（循环分部自动化）**：等价变换链——step log 每步
  before->after 就是一条等式。:intro_eq <lhs|%N> 把链上任意节点（历史产出经
  %N 展开）与当前式连成方程；iparts 把常数符号拉出绑定体（∫-f=-∫f 线性安全），
  使干净起点的循环名词指针收敛（[loop] 提示）；:fold 线性折叠处理倍数/负号
  起点（I := ∫-f 时循环再现的是 -I，指针天然不同一——初版只救了干净起点，
  是过拟合特例，fold 补为通用常数倍机制）；solveq 裸符号解析定义名。
  对称性裁定：账本等式事实在守卫下对称使用安全（G⟹A=B 当且仅当 G⟹B=A；
  decide 相对整个账本判定，条件随账本走不随方向走）；真正有方向的是非等价
  变换（平方、乘可能零因子）——它们以 step+proviso/note 存在，从不进账本当 Eq。
  守卫在案纪律（硬闸门裁定）：派生等式的守卫 = 链上所有步骤条件的合取；
  域闸门 UNKNOWN 创建义务后，:intro_eq 建立等式前必须结算（:ans 入账）——
  初版只打软提示是真实缺口（等式建出来了、守卫还悬着，消费时静默丢守卫）。
  结算后守卫双重载体随行：账本事实（decide/_eq_subst 消费时相对账本）+
  等式项自身 dom_condition（穿透 Quote 提取）。配套 :add_sub 加零凑形
  （A -> A+'t-'t）：必须走 quote + 纯驻留构造（_intern_expr）——mk 的同类项
  归并会当场消掉 +t-t，连 Eq 构造都会把借用形塌掉（实测 bug）。
  手写方程（feed 层）不受硬闸门限：断言自由但由断言者担责。
- **定积分的定义域特性框架（通用机制，回应特判批评）**：
  反射对称泛化为任意区间（phi=lo+hi-x，关于中点 m 的奇/偶关系；[-a,a] 只是
  lo+hi=0 实例；关系判定走 equivalent 管线严格 YES，采样 PROBABLE 不触发——
  归零是强断言）；周期折叠（spec.period 声明供候选 + _absorb_shift 结构吸收
  做证明——声明即定理，与 deriv/anti 同信任级；只允许在周期头参数顶层加法
  边缘剥 +P，残余偏移经驻留指针比对自然拒绝非周期因子如 x*sin(x)；
  折到单周期防递归，偶型半区间 _no_sym 防常数函数无限折半至空区间截断出错值
  ——两个实测递归/正确性 bug）。配套修复：trig 层 _expand 只认参数恰为 x
  （自己的输出 cos(2x) 都无法再归约——规范形幂等性破坏，equivalent 三角层
  对谐波失明）补整数频率；sin^2 类三角多项式改走多角度基线性化逐项积分
  （连续原函数），绕开 tan-half 原函数 atan(tan(x/2)) 在 x=(2k+1)pi 的分支跳变
  （跨切区间 NL 代限值错误，交叉核对曾正确扣留）；spec 补 Log/Atan anti 表项。
- **无原函数定积分的 verify 裁定**：系统定位拒绝浮点数值通道（无高精度数值
  积分），故找不到原函数时不存在可用的独立验证手段——唯一诚实选项是拒答
  （unsupported: no antiderivative）。Maxima defint 的无原函数闭式全部是符号
  精确方法（Beta/Gamma 表、参数微分、围道留数），各有证书链——pyCAS 远期
  若引入须同样满足证书要求，绝不以数值近似冒充验证。极限的 PROBABLE 数值
  探针限于点态收敛趋势抽查，不为区间积分值背书。
- **两类推导步骤与验证覆盖（裁定，修正"计算即等式链"的过宽表述）**：
  等式链只属于**等价变换类**步骤（before ≡ after，守卫下；:intro_eq/:solveq
  循环消解仅适用此类）。求解类步骤是**问题 -> 答案 + 验证关系**——不存在
  "方程 = 解"的等式；其正确性由证书检查背书，每类计算一个关系：
  不定积分 D(F)=f / 求和 ΔS=f / ODE 解代回 / 方程解代回 / 分解乘回 /
  矩阵逆 M·M⁻¹=I / 线性组 M·x=b / 特征值 charpoly(λ)=0 / 级数系数 vs
  diff 引擎交叉核对 / 极限数值收敛趋势探针（PROBABLE）。审计结论：sum/ode/
  integrate/defint 原有验证；factor/solve/minv/msolve/eigenvalues/limit/series
  七处裸奔已补齐（check_solution 此前存在但未接入管线）。所有 ! 输出统一
  携带 [VERIFIED/PROBABLE/UNVERIFIED, method] 标注。
- **剩余结构债**：RootOf 复根隔离；Gröbner 基（多元方程组）。

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
- usub/lhop 的经典条件（g'!=0、G'!=0）由 verify 背书链承担（docstring + manual 标注）。

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
