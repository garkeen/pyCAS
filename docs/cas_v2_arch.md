# pyCAS v2 架构设计

> 本文是**唯一设计权威**：数据结构、分层、机制、纪律、路线图。
> 修订裁定与教训条款的压缩档案见 `docs/notes.md`；使用教程见
> `docs/manual.md`。定位：**交互式、通用、纯符号 CAS**。
> 正确性 = **永不静默错**：三态判定（VERIFIED/PROBABLE/UNVERIFIED）、
> 片段内完备 + 片段外拒答、假 VERIFIED 是最高违级。

---

## 0. 目标与纪律

- 中枢原子操作 = `apply(rule, path)`；四通道：手动 `:` / 建议 / 启发式 /
  黑盒 `!`（算法直出 + verify 背书）。语法即语义。
- 纯符号精确：任意大整数、精确有理数；无数值主通道（evalnum 只做
  验证抽查与 PROBABLE）。
- 积分/求解/极限/ODE = 策略插件，地基只铺前置代数。
- **通用算术路径纪律（N1 后生效）**：系数域封闭于
  `{Fr ⊂ Ga(ℚ(i),分量可SymRat) ⊂ SymRat}`，Ga 独占全部 i-成分；
  gcd/约分/content 对任意叶类型无条件执行——**禁止**按名字嗅探、
  按 leaf 类型跳过硬操作、形状检测换道绕行。守卫是债务利息：
  新增分支前先问"哪个通用机制缺失"。
- 声明式管线纪律（N2 后生效）：树变换/判零/求解三类分派一律走
  注册表（PRE_PASSES / VERIFY_STAGES / SOLVERS / _EQ_STAGES），
  新增数类或通道只动注册表一处。

## 1. 核心机制（压缩版）

1. **驻留项 InternedTerm**：Expr 不可变 (head,args)，内容寻址驻留，
   equal=指针 O(1)；构造即规范化（AC 归并、整数幂合并、i^n mod 4、
   e^a→Exp(a)）；绑定词 Bound 承载 ∫ΣΠlim（de Bruijn）。
2. **账本上下文 + decide()**：事实条目带出处可回滚；decide 分层管线
   semantic→ledger→interval→derive→axiom，3VL；结构性不等不产 No。
3. **义务队列**：不可判定条件生成 Obligation，计算带 Proviso 继续，
   作答后按 step log 重放受影响步骤。
4. **步骤日志 Step Log**：`(sid, rule_id, path, before, after, guard,
   Δcost, note)`；撤销/重放/解释全建于其上；path 是唯一寻址。
5. **规则 DSL**：`rule id = lhs -> rhs [guard] [as dir] [prio] [auto]`；
   三分边界：表示归并→mk；定理→规则文件；过程算法→内核（verify 背书）。
6. **FunctionSpec 注册表**：每函数头一份声明（deriv/anti/inv/bound/
   numeric/print_name…），消费者全读表；禁止消费者模块为新函数加 if。
7. **Stage/Solver 声明式框架**：
   - `structure.Pass`：name/detect/apply + needs/gated（假设门控，
     如 principal-branch 承诺位）+ degrade 具名降级；
   - `VERIFY_STAGES` 判零族（tower_zero / ratpow_merge* /
     atomize_together*）供 diff.verify 消费；
   - `structs.SOLVERS` 求解总表（五快速通道 + Qx/TanHalf/Tower 三
     Struct 三段式 project/compute/retract）；attempt 协议
     hit/miss 双态，证明性拒答绝不吞；
   - `decide._EQ_STAGES` 判等阶段注册（trig/ledger/sampling +
     tower/ratpow 判等视图）。

## 2. 拒答协议（三异常精确语义）

| 异常 | 语义 | 上抛方 | 调用方义务 |
|---|---|---|---|
| `RischNonElementary` | **证明性不可初等**（带证据链） | Risch 判定链 | 可尝试特殊函数出口后仍上抛；绝不吞 |
| `RischUnsupported` | 当前理论超界（诚实拒答载体，reason 必填卡点） | 塔/投影/RDE | 记录原因聚合；不得伪装成证明 |
| `PolyError` | 代数层输入不合法（非多项式/除零/变量失配） | poly/ratfunc | 底层语义错误；策略层捕获转为 unsupported 聚合 |

## 3. 分层

```
L7 策略    istrategy 步树 / bsub / SOLVERS 声明表消费
L6 会话    session 四通道 / step log / 义务 / 转录
L5 化简    simplify 显式栈重建 / refine（账本驱动）
L4 上下文  账本 + decide 3VL + 义务 + ex falso 锁
L3 领域    poly/ratfunc/factor/apart/sturm/algnum/groebner/
           solve/matrix/ineq/sets + spec/trig/diff/integrate/ode
           + risch 塔 + structure(Stage) + structs(Solver)
L2 规则    Rule/RuleSet/loader 热重载
L0 项      term 驻留规范化 / gaussian(Ga) / errors
```

效率分层：规则/上下文=外壳，规范形+算法=内核（热路径直达）。
核心与展示路径全部显式工作栈，预算按节点计。

## 4. 系数域声明（N1 后真态）

```
ℤ ⊂ ℚ(Fr) ⊂ ℚ(i)(Ga) ⊂ ℚ(params)(SymRat) ⊂ ℚ(i,params)(Ga(SymRat,·))
```

- 混算规范方向：任何 SymRat∘Ga 经 NotImplemented 交接产出
  `Ga(SymRat,·)`——系数叶类型恒为 {Fr, Ga, SymRat} 三选一。
- ugcd：域泛化欧几里得+monic（域无 content 概念）。
- mgcd：唯一算法=原始 PRS（递归 content=_primitive_full + _prem
  环伪除 + div_exact）；域叶标量 content 取平凡单位元 1（相差
  单位元语义不变）；非实首项跳过符号规范化。
- RatFunc：无条件约分规范形（分母 monic）。
- 各操作实测矩阵（手册级语义声明，修掉才许改格）：

| 操作 | ℚ | ℚ(i) | 𝔄 代数数 | params | 𝔗 超越常数 |
|---|---|---|---|---|---|
| 多项式 ±×÷/gcd | ✓ | ✓ | 部分(algnum) | ✓ | ✗ hard error |
| 因子分解 factor | ✓ Zassenhaus | ✗ | ✗ | 当额外变量 | ✗ |
| apart/together | ✓ | ✓ | — | ✓ | ✗ |
| solve | ✓ 根式/RootOf | 复根✓ | 输出侧✓ | ✓ 公式(回代 UNVERIFIED) | ✗ |
| msolve | ✓ | ⚠ 未约简+UNVERIFIED | — | ✓ | 未测 |
| gsolve | ✓ | ✗ | ✗ | 未系统验证 | ✗ |
| solveineq | ✓ Sturm | ✗ | 端点✓ | 结构化拒答 | ✗ |
| 不定积分 | ✓ Risch 全链 | ✓ 塔实化全链 | 有理通道✓+特殊出口✓ | 塔内✓/混合✓(N1)/残数根越域拒(C) | Log 参数化✓ |
| defint | ✓ | 同左 | — | 界拒(不可数值比较) | 界✓精确 |
| limit | PROBABLE | 同左 | — | 参数点 UNKNOWN | 经采样 |
| series | ✓ | ✓ | — | ✓ | 系数须数值 |
| 微分 diff | ✓ | ✓ | ✓ | ✓ | ✓ 免费 |
| 判等 decide | ✓ | ✓塔 | 部分 | ✓ SymRat 恒等 | 采样 PROBABLE |

总原则：能力不得静默降域；矩阵与 domain_decls.py 为声明权威，
M6.5 起由测试锁定。

## 5. 模块清单

| 文件 | 内容 |
|----|------|
| term.py | 驻留 Expr/Bound/mk 规范化/subst |
| termpath | 树遍历与重写工具：subst/instantiate/路径寻址（term 末尾回接） |
| gaussian.py | Ga 高斯有理域（分量泛型→ℚ(i,params)） |
| scalarutil.py | 标量域助手单点（Ga 标量算术 + ℚ(i,params) 分解，M6.6） |
| univar.py | K[t] 单变量域多项式稠密算术（M6.4） |
| match/rules/loader | 匹配器 / 规则引擎 / DSL 热重载 |
| context/decide/domain/domain_decls | 账本 / 3VL 判等管线 / 域谓词 / 声明登记 |
| simplify/refine/structure | 化简 / 账本化简 / analyze+Stage+判零族 |
| poly/ratfunc/factor/apart | 多项式(域泛化gcd) / 有理函数 / Zassenhaus / 部分分式 |
| algnum/sturm | ℚ(α) 域运算 / 实根隔离 |
| solve/matrix/ineq/sets/groebner | 方程 / 线性代数 / Sturm 不等式 / 解集 / Gröbner |
| ops/spec/trig/diff | 项层结构API / FunctionSpec / 三角多角度基 / 微分+verify |
| contract | N4 构造期收缩规则集（exp∘log 往返、选择性 exp 和拆分、Log 幂/正实常数剥离、π 有理倍数 ℚ(√d) 全类表；spec.contract 挂载点） |
| radnorm | N1 根式规范化（[m,c,r] 记录形：content/sqfree mod n、指标归约、同次合并 √a·√b→√(ab)；负底奇指标/大数诚实边界） |
| denest | N3 域内完全幂判定（Groebner 坐标法三态：范数预筛 proved-no、有界精确枚举快路、商式编码方程组后备；规模闸诚实 unknown；rsimp.spad 同题参照） | N1 根式规范化（[m,c,r] 记录形：content/sqfree mod n、指标归约、同次合并 √a·√b→√(ab)；负底奇指标/大数诚实边界） |
| kernelreg | N6-P1 核关系统一注册表门面（代数区=ALG_FIELDS 统一视图 API；超越常数关系区 const_face_key 两面孔同键 E≡exp(1)；P2 z-符号合一/P3 四孤岛迁移的接缝） |
| ratexit | N8 出口共轭有理化（root_reduce 项级局部重写：平方根类叶、分母一次闭式；逐叶多遍不动点；无注册表依赖零泄漏面） |
| integrate/istrategy/bsub | 积分入口(SOLVERS 消费) / 步树 / 反向换元 |
| risch_core | 微分塔地基：DiffExt/build_extension/derivation/trigs_to_exp/代数常数登记 |
| risch_exp | exp 层积分：Hermite 推广+RT 残数、K[t] 视图、log 配对实化 |
| risch_rdesup | RDE 支撑：weak normalization/split/limited_integrate/视图导子 |
| risch_prde | 参数化判定件：_pld_solve 三态/_ldrad_base/_is_logderiv_radical |
| risch_rde | 塔上 RDE 完备求解器（ok/proved/undecided）+ exp 频率分量 + Laurent 实化 |
| risch | 门面+递归驱动：_risch_rec/_integrate_in_K/_risch_rec_mixed/integrate_exp_tower |
| structs | Struct 协议 + SOLVERS 总表 |
| series/limits/ode/summation | Taylor / 极限 / ODE / Faulhaber+Gosper |
| evalnum/session/parser/pprint/latex/errors | 数值抽查 / REPL / 解析 / 打印 / 异常协议 |

补充行（M6.7 拆分登记）：

| 文件 | 内容 |
|----|------|
| ratint | 有理积分核：Hermite+RootOf/atan、AN 区间精确符号、根式/常数参数化收集 |
| intcore | 不定积分入口与快速通道：u-sub/spec anti 表/tan-half/特殊函数出口/SOLVERS 瀑布 |
| defint | 定积分：NL+奇点拆分+反常判敛+分段+中点反射/周期折叠 |
| integrate | 兼容门面：ratint/intcore/defint 全部历史名显式重导出（零行为差） |
| session_cmds | 内核命令 handler（_k_*）+ 惰性形式求值助手（_eval_inert 等） |
| session_core | SessionBase：状态/账本/规则应用/定义展开/撤销重放 |
| session_kernel | KernelOpsMixin：! 前缀算法入口 + :value 族 + refine/LaTeX |
| session_manual | ManualOpsMixin：子项手术/等式双侧/变形工具箱/微积分战术 |
| session_dispatch | DispatchMixin：分发/帮助表/转录 DSL（save/replay） |
| session | 组装门面：四 Mixin 合成 Session + REPL 入口 |
| algfield | ℚ(B)[α] 代数扩张域（M7.0）：AlgField/AlgElem 单一表示、mod minpoly 算术、迹/范数/结式 |

懒导入断环登记（M6.7，三处，均为函数级 import）：build_extension→
risch_prde._is_logderiv_radical；_limited_integrate/_exp_freq_part→
risch._integrate_in_K。

## 6. 里程碑（单一 M 系列；基于当前代码实证状态）

### 已收官
- **M0–M3 ✓**：L0 地基 → 多项式/有理积分 → 初等域/交互 → 分析层/ODE/换元。
- **M4 ✓**：Faulhaber 幂和 + Gosper 有理求和。
- **M5 ✓ Risch 决策程序**（超越函数范围内完备判定，含不可初等证明）：
  塔/DiffExt · exp case(Hermite+RT) · primitive/log · 塔域 RDE 完备
  （spde/no_cancel/Laurent 对角/cancellation）· prde 判定件
  （is_logderiv_radical / _pld_solve 三态参数化 / limited_integrate
  比率定理）· ℚ(i) 全链+实化 · 三角复指数化 · AN 根式有理通道
  （作用域参数化）· Trager 范数分解(deg≥3) · 混合域共轭拆分全通 ·
  特殊函数出口族(Si/Ei/li/Ci/erf，verify 背书) · 符号参数积分
  （x^a/(c·x)^a generic+proviso、常量项收集）。
- **架构批 ✓（并入 M5 收官，原审计编号废止）**：系数域总算术
  （混算规范形/原始 PRS 统一 mgcd/无条件约分/虚单位收口）、
  Stage 注册表（Pass.needs 门控 + VERIFY_STAGES + SOLVERS 总表）、
  solveineq 结构化拒答、_pld_solve 方向性隐患根治。

### 进行中 / 待办

- **M6 架构统一 ✓（还债批，全部来自 2026-08 全码审计；e1ec8c0→
  本批六项全绿，555 测试）**
  - M6.1 双塔合一 ✓(e1ec8c0)：integrate_exp_tower 已薄壳委托
    TowerStruct（project/compute 唯一实现）
  - M6.2 判零框架收敛 ✓：判零序列唯一实现 = diff._ratpow_zero_run
    （直零→equivalent 符号回退→塔零；显式 x 参数，None 跳塔层）；
    _eq_stage_ratpow（decide 视图：principal 门控+单变元扫描）与
    RatpowMergeStage（verify 视图：needs 门控）均委托之；
    tower 零判定唯一核 = diff._tower_zero（自带入口归一+异常安全），
    _eq_stage_tower 为其门控视图
  - M6.3 拒答协议落地 ✓（raise 点 76 处全审计）：
    重分类 5 处——integrate 瀑布兜底+判别式防御、apart 参数分解
    次数界、tan-half 未匹配 → RischUnsupported；groebner 预算 ×2
    → BudgetExceeded。处理器加宽 10 处（session ×4/ode ×3/defint ×2/
    solve_system）。审计后保留三类并记录理由：共轭拆分零分母对
    （真·除零输入契约）、u_inv_mod 的 RischUnsupported（须走 RDE
    拒绝路由）、_frac_num 的 PolyError（build_extension 边界已统一
    翻译为 RischUnsupported）。测试期望同步：sin(x)/log(x) 拒绝
    载体改为 RischUnsupported
  - M6.4 单变量域塔代数模块化 ✓：cas/univar.py（K[t] 稠密算术
    19 函数，升序系数 list、域元素系数、monic gcd；契约与 Poly
    换算边界见模块 docstring；from_poly 为正向转换，反向
    _from_univar 因塔嵌入耦合留 risch）
  - M6.5 文档-现实锁定 ✓：tests/test_registry_lock.py（9 测试）——
    §5 模块表↔磁盘双向锁、DOMAIN_DECLS 完整性、四大注册表成员/
    顺序/门控逐项断言、scalarutil/univar 公开面。落地即抓两处漂移：
    _EQ_STAGES 注册序颠倒原硬编码顺序（已修正为 tower 零判定先于
    ratpow 合并）、__main__ 豁免登记
  - M6.6 标量域助手归拢 ✓：cas/scalarutil.py 单点（Ga 标量簇
    rf_const_ga/ga_den/lcm2/ga_vec_to_ints/mk_zero_like + ℚ(i,params)
    分解簇 leaf_has_ga/symrat_has_ga/coef_zero/coef_re_im/poly_re_im；
    公开名去下划线，risch/integrate 顶层导入，跨模块懒导入清除）
- **M78 代数扩张与混合塔（原 M7+M8 合并；FriCAS
  FunctionFieldCategory/intalg/intaf/intpar 完整对齐）**
  合并裁定：M7.2 实测证明"常数码化"路线存在原则性阻塞——符号底
  残根使塔上系数域变为 ℚ(a)[α]，商环感知算术不可回避；而代数层
  入塔（原 M8.1）正是它的正解。两条线本是一件事：**代数对象以
  一等公民身份进入微分塔**。单一线性塔目标不变：
  ℚ(x,params) ⊂ ℚ(...,α) ⊂ ℚ(...,α,τ) ⊂ …（α 代数生成元、
  τ=exp/log 生成元，顺序不限）。
  - M78.0 ℚ(B)[α] 域算术通用化 ✓(0adaf88)：cas/algfield.py
    AlgField/AlgElem 单一表示（K 叶鸭子类型：Fr/Ga/SymRat/RatFunc），
    mod minpoly 算术/xgcd/牛顿幂和迹/Sylvester 范数与结式；三套并行
    注册表退役合一为 algfield.ALG_FIELDS（域对象携带极小多项式+出处键
    +实嵌入区间），poly/apart/ratint/structs/structure 全部读端迁移，
    alg_suspend 改可重入计数并升级为原始多项式原语作用域纪律
    （ugcd/mgcd/div_exact 强制自由变量语义——notes.md #1 算法层兑现）
  - M78.1 z-常数中间层 ✓(d952306)：数值底代数常数残根落域——
    _constant_roots 经 _collect_radical 建 AlgField、参数化符号穿
    系数算术，TowerStruct.compute 出口统一回化再 verify。解锁
    ∫eˣ/(e²ˣ−2) VERIFIED；∫dx/(eˣ+x) 查明本就是正确 proved 拒答
    （arch 原描述失真已修正，回归钉锁定方向安全序）；附带修复
    integrate 字符串变量名未归一错拒缺陷
  - M78.2 代数扩张判定装置 ✓(e096593)：poly.sqrfree_mults 多元
    无平方重数分解 + perfect_power_part 完全幂检测（乘回精确验证）
    + algfield.binomial_irreducible Capelli 完整判定（含 −4K⁴ 判据；
    T⁴+4 可约/T⁴+16 不可约锚点）+ _collect_radical 符号底泛化
  - M78.3 代数层入塔 ✓：DiffExt 新增 'algebraic' case——生成元 ϑ
    携带首一极小关系 ϑ^q = Mp（有理根式经整化 ϑ=θ·rd 保证 monic）；
    D(ϑ) = η·ϑ 与 exp 层导数规则同构（dpair 直接复用，η=D(Mp)/(q·Mp)）；
    塔不变量 = 全部代数层指数 < q，由 _ta_reduce 在 derivation 出口
    维护；build_extension 接受变元底根式建层（_collect_alg_candidates
    扫描 + Capelli 门槛，退化根式 √((x+1)²) 类诚实拒绝）；前向
    leaf ↦ ϑ/rd 与回代 sym ↦ leaf·rd 方向一致性；混合塔
    ℚ(x)⊂ℚ(x,τ)⊂ℚ(x,τ,α) 构建通过。验收 = derivation 与 diff.d
    数值对拍（独立预言机）+ 塔不变量钉 + 混合建层钉
  - M78.4 架构裁定与规范形算术（进行中，一等交付物）。
    **双阶梯原则**（FriCAS expr.spad/algext.spad、Maxima rat3e.lisp/
    ratmac.lisp 证据）：数域=显式数据结构（SAE 模式：Rep=次数<deg(M)
    多项式，乘法出口 reduce；AlgField 即其等价物）；函数域=平表示+
    分类谓词+分发表（intef.spad lfintegrate 模式），无塔型数据结构；
    算法内部允许临时工作域对象（intaf.spad RadicalFunctionField 模式：
    建→算→映回→弃）。现存实现三分类：
    - **A 分发路（保留）**：SpecAnti 表、_try_usup（对标 tryChangeVar）、
      QxStruct 有理层全套、TowerStruct 初等塔层、trig.py 与
      trigs_to_exp 双规范形、defint NL+奇点拆分（_numeric_cross 标注
      为启发式证据不冒充证明）、evalnum/decide、Gosper、各系数域
      各自的 gcd（ugcd/mgcd/u_gcd/_monic_gcd）。
    - **B 拆除（重复登记与契约破洞，非窄域快路）**：B1 自创根式剥离
      三函数（已删）；B2 四处独立根式登记（QxStruct _rcN /
      _collect_radical _aN / 塔层 / solve Phase α① 游走）收敛到唯一
      核注册表，四处降级为消费者；B3 Capelli 降为快筛，门卫改
      建域+诚实拒答（依赖 N2）；B4 apart._det_poly → 统一 Bareiss；
      B5 _mk_rat 混合叶跳规范化契约洞；B6 RatFunc 缺 __eq__；
      B7 istrategy 步树从单一执行踪迹派生（已兑现：intcore _LAST_TRACE
      埋点全路径，explain 为纯踪迹投影）；B8 simplify/refine 游离
      pass 并入构造期折叠+规则注册表（已兑现：_SIMPLIFY_PASSES /
      _REFINE_RULES 注册表化）；B9 TanHalfStruct 共享登记否则拆
      （裁定：共享——全链单一定义、零独立登记，防泄漏钉在册）。
    - **N 缺失件（依赖序施工）**：
      N4 构造期收缩规则集——exp(a+b)=exp(a)exp(b)、Exp(Log u)→u、
        Exp(k·Log u)→u^k、Log(正实常数·u)=c+Log u（主分支安全，
        需常数符号表 e,π>0）、sin/cos 的 π 有理倍数精确值表（结果
        落 𝔄）（elemntry.spad iiilog/ilog 逻辑）；只收无条件恒等式，
        一般 Log(a b) 不拆（分支破裂）。
      N1 froot 链——有理底 n 次根构造期归一 [m,c,r] 记录使
        f^(1/n)=c·r^(1/m)：content 抽整、sqfree 重数 mod n、同次
        合并 √a·√b→√(ab)（正有理底无条件；一般复底不合并）
        （manip.spad zroot(:83)/nthr/iroot(:90)/froot(:182) 逻辑）。
      N8 表达式层除法出口共轭有理化（expr.spad root_reduce 闭式
        d₁=c₀²dn−aₙc₁²；多核逐层 univariate 提升）。
      N3 落域判定 denesting——新代数核注册前先判"在已注册域内是否
        完全幂"，成功就地坍缩不建新核（√(3+2√2)→1+√2），失败诚实
        建嵌套塔（rsimp.spad Borodin-Zippel 候选多项式 p₂..p₁₁ +
        复合指数素数组合）。与 N2 同币两面：N3 构造期便宜版，
        N2 事后完备版。
      N6 核关系注册表统一——ALG_FIELDS 推广：任意核 ↦ minPoly
        （fspace kernel 协议），四孤岛销户后全部分发器查同一份。
      N5 统一投影服务——expr ↦ (系数域标签, 核集标签) 喂分发器
        （SMP(R,Kernel) 投影惯例），随消费者迁移渐进成型。
      N2 𝔄 上多项式因子分解（范数法/InnerAlgFactor 逻辑）→ 解锁
        𝔄(x) 部分分式、an_factor 去限、B3 门替换。
      **入域闸门链**（新代数对象统一流水线，例子只是回归钉）：
      ①折叠(N4)→②落域判定(N3)→③重数归一(N1)→④注册/复用(N6)
      →⑤出口持续归约(AlgField+N8)。
  - M78.5 注册表统一与投影迁移（N6/N5/B2/B3/B9 收尾）
  - M78.6 代数域因子分解 N2 与 B4 清理
  - M78.7 代数层上的积分算法：Hermite 迹推广 +
    Trager 范数残数（intalg.spad DoubleResultant 对标）+ RDE/prde
    系数域升格 ℚ(x,α[,τ])（intpar.spad 全套在函数域系数上运行）。
    解锁目标：∫dx/√(x²+1)=log(x+√(x²+1)) VERIFIED、
    ∫eˣ/(e²ˣ+a·eˣ+1) VERIFIED、椭圆积分类 proved 拒答。
    已知边界：RootOf 形态残根。前置 normalize（efstruc.spad
    rischNormalize 逻辑，核最小化重写）随 N5/N6 就位后接入。
  - M78.8 primelt 多符号归一（ℚ(√2,√3)→ℚ(√2+√3)）；出口回化主支
    proviso 体系；diff.verify 穿越代数层的精确判等（minpoly 驱动归零）
  - M78.9 **双轨验收（生成器为主 + 钉子库为锚，角色不同不互替）**
    - **回积生成器（覆盖率与进度量化）**：文法随机生成初等 F
      （叶 {x,有理数,参数}，运算 {+-×÷,整幂,n次根(代数层),Exp,Log,
      sin/cos/tan 经复指数化}，深度有界，种子固定，语料入库）；
      f := simplify(dF/dx) → integrate(f)=G 且 verify=VERIFIED
      （G 不必等于 F）。F 初等 ⟹ f 必可积（Risch 完备性），任何
      失败 = 引擎真实缺口，归档并定位卡点层。切片通过率
      （纯超越/纯代数/混合交错）为 M78 进度指标。
    - **钉子库（回归锚 + 对照锚，手工策展且只增不删）**：
      每钉 = 精确期望形态 + 历史缺陷类别标签。两类来源：
      ① 边界结构博物馆——共振/cancellation/Laurent 特殊分母/
      共轭实化/平凡参数化/负幂残根等随机树采不到的退化形态
      （如 ∫√(eˣ+1)、∫eˣ/√(eˣ+1)、√(eˣ+1)/(eˣ+1)² 类）；
      ② 生成器失败案例修复后的固化（bug→钉）。每钉在 FriCAS
      跑形态对照（非仅判定对照）。
    - **反向采样（打假证明专用）**：直接采 f；判 proved 时数值
      搜索反例——假 VERIFIED 同级高危，零容忍。
    - 对齐宣称门槛 = 三切片通过率达标（FriCAS 对照集校准）
      + 全部钉子绿 + 反向采样零假阳；tan 核复指数路线差异照旧记录
- **M9 可解释积分引擎（SAINT/Rubi 路线）**
  - 步树战术单元（:isteps 自动搜出可重放手动路径）/ Slagle 核心
    循环 / Rubi 精选翻译（每条 D-check 入库）/ 混合工作流
    （:replay 接管）。Risch 保持黑盒判定权威，M9 供可解释性与广度。
- **M10 分析层完备化**
  - Gruntz 极限完备化 / 幂级数算术+收敛半径 / 常系数递推求和 /
    ODE 非齐次+系统+高阶 / 参数 RootOf case-split（CAD 接口，
    低维片段）/ 常数依赖引擎强化
- **M11 远期分支（启动前重估价值密度）**
  - M11.a 丢番图（线性/Pell/平方和；一般情形不可判定为定理边界）
  - M11.b 平面几何吴消去
  - M11.c 实不等式 CAD/VTS（≤3 变量小次数；YES/NO 双可信决策）
  （变元基底代数积分与混合塔已合并为 M78——构成 FriCAS 积分判定面
   的完整对齐）

### 理论不可解边界（非债务，处理方式已定）
Richardson 超越常数零等价：数值采样 PROBABLE + 拒答，永不进 YES 通道。

## 7. 化简/规范形/停机（要点）

分层投降：整数/有理→多项式→三角多角度基→exp-log 塔(Risch 唯一
表示)→分段归并；跨层翻译=带守卫的策略动作。cost 单调下降才接受；
FullSimplify 式搜索不做。verify 同为三值诚实。

## 8. 数据草图（关键结构签名）

```
Expr=(head,args) 驻留;  DiffExt{levels,cases,ws,terms,minpolys}
Poly(vars,{mono:coeff});  RatFunc(p,q) 规范形
Pass{name,detect,apply,needs,gated};  Struct{project,compute,retract}
Solver.attempt(t,x)->('hit',F,method,provisos[,ok])|('miss',reason)
decide(fact,ctx)->Yes|No|Unknown;  equivalent(a,b)->T3
verify(F,x,f)->VERIFIED|FAILED|PROBABLE|UNVERIFIED
```
