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
| gaussian.py | Ga 高斯有理域（分量泛型→ℚ(i,params)） |
| match/rules/loader | 匹配器 / 规则引擎 / DSL 热重载 |
| context/decide/domain/domain_decls | 账本 / 3VL 判等管线 / 域谓词 / 声明登记 |
| simplify/refine/structure | 化简 / 账本化简 / analyze+Stage+判零族 |
| poly/ratfunc/factor/apart | 多项式(域泛化gcd) / 有理函数 / Zassenhaus / 部分分式 |
| algnum/sturm | ℚ(α) 域运算 / 实根隔离 |
| solve/matrix/ineq/sets/groebner | 方程 / 线性代数 / Sturm 不等式 / 解集 / Gröbner |
| ops/spec/trig/diff | 项层结构API / FunctionSpec / 三角多角度基 / 微分+verify |
| integrate/istrategy/bsub | 积分入口(SOLVERS 消费) / 步树 / 反向换元 |
| risch | 微分塔全套（DiffExt/RDE 三态/prde 判定件/_pld_solve） |
| structs | Struct 协议 + SOLVERS 总表 |
| series/limits/ode/summation | Taylor / 极限 / ODE / Faulhaber+Gosper |
| evalnum/session/parser/pprint/latex/errors | 数值抽查 / REPL / 解析 / 打印 / 异常协议 |

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

- **M6 架构统一（还债批，全部来自 2026-08 全码审计）**
  - M6.1 双塔合一：`risch.integrate_exp_tower` 改为薄壳委托
    TowerStruct（现存两份完整拷贝，已漂移一次）
  - M6.2 判零框架收敛：tower_zero/ratpow_merge 在 _EQ_STAGES 与
    VERIFY_STAGES 双注册——保留判等视图于 _EQ_STAGES，
    VERIFY_STAGES 仅存 needs 门控差异并复用其 run
  - M6.3 拒答协议落地：按 §2 语义表统一抛出点（现 PolyError×50
    与 RischUnsupported×24 混用于同类场景）
  - M6.4 单变量域塔代数模块化：risch 内嵌 `_univar/_u_*` 十余函数
    提取为 `cas/univar.py`（契约：系数为域元素的 K[t]），写明与
    Poly 的换算边界
  - M6.5 文档-现实锁定：domain_decls/arch 矩阵改为导入期测试断言
    （导出面 ↔ 声明一致；杜绝 SOLVERS 式虚报复发）
  - M6.6 标量域助手归拢：_rf_const_ga/_coef_re_im/_ga_vec_to_ints
    等 → cas/scalarutil.py 单点
- **M7 代数扩张完备域（常数字幕 + 变元字幕统一基建）**
  共用底座：ℚ(B)[α] 通用代数扩张算术——minpoly 登记/约简/求逆/
  uexgcd/迹/范数/结式（B = 常量域或 ℚ(x,params) 多项式环；
  algnum.py 与 M5.4 Trager 装置为起点）。
  - M7.0 ℚ(B)[α] 域算术通用化（单一代数对象表示，消灭
    "常量 α / 变元 α / 参数根式"三套表示并行）
  - M7.1 残数域装置：z-常数中间层的 K[root] 约束计算
    （解锁 1/(eˣ+x) 型 _pld_solve 'und'）
  - M7.2 RT 残数根落域：√(a²−4) 类残根直接驻留代数扩张
    （解锁 ∫dx/(eˣ+(a+i)) 诚实拒答转 VERIFIED）
  - M7.3 本原元多符号：乘法闭包归一或 primelt（√2·√3→√6；
    解锁多 AN 符号 apart）
  - M7.4 变元基底代数积分 Trager 全链：∫dx/√(x²+1)
    = log(x+√(x²+1)) VERIFIED；Hermite 推广 + Trager 范数/结式；
    椭圆积分类 proved 拒答（FriCAS intaf/intalg 对标）
- **M8 可解释积分引擎（SAINT/Rubi 路线）**
  - 步树战术单元（:isteps 自动搜出可重放手动路径）/ Slagle 核心
    循环 / Rubi 精选翻译（每条 D-check 入库）/ 混合工作流
    （:replay 接管）。Risch 保持黑盒判定权威，M8 供可解释性与广度。
- **M9 分析层完备化**
  - Gruntz 极限完备化 / 幂级数算术+收敛半径 / 常系数递推求和 /
    ODE 非齐次+系统+高阶 / 参数 RootOf case-split（CAD 接口，
    低维片段）/ 常数依赖引擎强化
- **M10 远期分支（启动前重估价值密度）**
  - M10.a 丢番图（线性/Pell/平方和；一般情形不可判定为定理边界）
  - M10.b 平面几何吴消去
  - M10.c 实不等式 CAD/VTS（≤3 变量小次数；YES/NO 双可信决策）
  （变元基底代数积分已升格为 M7.4——与常数字幕共享同一扩张基建，
   分立会重复建设）

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
