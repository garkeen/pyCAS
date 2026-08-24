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
- **M7 代数扩张完备域（常数字幕 + 变元字幕统一基建）**
  共用底座：ℚ(B)[α] 通用代数扩张算术——minpoly 登记/约简/求逆/
  uexgcd/迹/范数/结式（B = 常量域或 ℚ(x,params) 多项式环；
  algnum.py 与 M5.4 Trager 装置为起点）。
  - M7.0 ℚ(B)[α] 域算术通用化 ✓(0adaf88)：cas/algfield.py
    AlgField/AlgElem 单一表示（K 叶鸭子类型：Fr/Ga/SymRat/RatFunc），
    mod minpoly 算术/xgcd/牛顿幂和迹/Sylvester 范数与结式；三套并行
    注册表退役合一为 algfield.ALG_FIELDS（域对象携带极小多项式+出处键
    +实嵌入区间），poly/apart/ratint/structs/structure 全部读端迁移，
    alg_suspend 保留为作用域语义声明
  - M7.1 残数域装置 ✓：z-常数中间层落地——_constant_roots 对根式
    形态代数常数残根经 _collect_radical 建 AlgField、参数化符号穿
    系数算术（乘积出口模约简），TowerStruct.compute 出口统一回化
    根式形态再 verify。解锁 ∫eˣ/(e²ˣ−2) 型（残数 ±1/(2√2) ∈
    ℚ(√2)）VERIFIED；∫dx/(eˣ+x) 经查本就是正确 proved 拒答（残数
    1/(1−x) 非常数，非 'und'——arch 原描述失真已修正，回归钉锁定
    方向安全序）。附带修复 integrate 字符串变量名未归一的错拒缺陷。
    边界：RootOf/嵌套根式形态残根仍诚实拒答（→M7.2/M7.3）
  - M7.2 RT 残数根落域：√(a²−4) 类残根直接驻留代数扩张
    （解锁 ∫dx/(eˣ+(a+i)) 诚实拒答转 VERIFIED；RootOf/嵌套形态
    残根落域亦在此收口）
  - M7.3 本原元多符号：乘法闭包归一或 primelt（√2·√3→√6；
    解锁多 AN 符号 apart）
  - M7.4 变元基底纯代数积分：∫dx/√(x²+1)
    = log(x+√(x²+1)) VERIFIED；Hermite 推广 + Trager 范数/结式；
    椭圆积分类 proved 拒答（FriCAS intaf/intalg 对标）
- **M8 混合超越-代数塔（FriCAS Risch 完整对齐收口）**
  代数层与超越层任意交错的单一线性塔：ℚ(x,params) ⊂ ℚ(...,α) ⊂
  ℚ(...,α,τ) ⊂ …（α 代数生成元、τ=exp/log 生成元，顺序不限）。
  - M8.1 DiffExt 新增 'algebraic' 层类型：生成元携带 minpoly，
    D(t) 由 minpoly 形式微分导出的有理式给出；build_extension 接受
    变元底根式建层（替代现拒绝路径），依赖检测 = minpoly 在既有
    域上可约性测试（可约 ⟹ 已在域内，回代映射）
  - M8.2 RDE/prde 全链在函数域系数上运行：spde/no_cancel/
    bound_degree/_pld_solve 的系数域升格 ℚ(x,α[,τ])（依赖 M6.4
    univar 模块 + M7.0 域算术）；残数经 M7.1 装置落扩张域
  - M8.3 出口回化：代数生成元还原根式形态 + 主支 proviso；
    diff.verify 支持穿越代数层的精确判等（minpoly 驱动归零）
  - M8.4 **双轨验收（生成器为主 + 钉子库为锚，角色不同不互替）**
    - **回积生成器（覆盖率与进度量化）**：文法随机生成初等 F
      （叶 {x,有理数,参数}，运算 {+-×÷,整幂,n次根(代数层),Exp,Log,
      sin/cos/tan 经复指数化}，深度有界，种子固定，语料入库）；
      f := simplify(dF/dx) → integrate(f)=G 且 verify=VERIFIED
      （G 不必等于 F）。F 初等 ⟹ f 必可积（Risch 完备性），任何
      失败 = 引擎真实缺口，归档并定位卡点层。切片通过率
      （纯超越/纯代数/混合交错）为 M7/M8 进度指标。
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
  （变元基底代数积分已并入 M7.4；混合塔为 M8——两者合计构成
   FriCAS 积分判定面的完整对齐）

### 理论不可解边界（非债务，处理方式已定）
Richardson 超越常数零等价：数值采样 PROBABLE + 拒答，永不进 YES 通道。

## 7. 化简/规范形/停机（要点）

分层投降：整数/有理→多项式→三角多角度基→exp-log 塔(Risch 唯一
表示)→分段归并；跨层翻译=带守卫的策略动作。cost 单调下降才接受；
FullSimplify 式搜索不做。verify 同为三值诚实。

## 8. 数据草图（关键结构签名）

```
Expr=(head,args) 驻留;  DiffExt{levels,cases,ws,terms}
Poly(vars,{mono:coeff});  RatFunc(p,q) 规范形
Pass{name,detect,apply,needs,gated};  Struct{project,compute,retract}
Solver.attempt(t,x)->('hit',F,method,provisos[,ok])|('miss',reason)
decide(fact,ctx)->Yes|No|Unknown;  equivalent(a,b)->T3
verify(F,x,f)->VERIFIED|FAILED|PROBABLE|UNVERIFIED
```
