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
- **M5.2a primitive case 积分（K 域升级 + limited_integrate 循环）**：
  K 从"隐式 Q(x) + 全局分母 wd 技巧"升级为显式 RatFunc 域——_u_* 工具族
  系数全换，_u_divmod 真除法。**隐患修复**：旧 _u_divmod 用 Poly.udivmod
  做"域除法"，只在首系数好除时正确（M5.1a 测试全绿纯属 exp 塔分母系数
  多为常数的幸运）；_u_gcd/_u_inv_mod 的 is_const 检查是 Poly 时代非域
  遗留（域中任何非零元素可逆），1/(x*log(x)) 首触发。
  _derive_ut 双 case：exp 对角（t^k -> t^k）vs primitive 移位（θ^{k+1}
  贡献 (k+1)vθ^k）。**数学发现：primitive 无 special 因子**（gcd(θ,v)=1，
  θ 正规）——全部因子走 normal 路线，比 exp 干净；exp 的 t 因子 special
  （gcd(t,Dt)=t）源于 Dt=η't。
  多项式部分 = sympy integrate_primitive_polynomial 同构的 limited_integrate
  循环：每轮取残差最高次系数 a，求 (b,c) 使 Db + c·v = a（c = ∫a 的
  log(u) 成分系数——齐次常数与升次统一于此），贡献 c·θ^{m+1}/(m+1) +
  b·θ^m，残差严格降次终止。**工作方式教训（用户裁定）**：设计算法前先查
  参考源码（sympy/FriCAS/maxima 本地全有）——手推的"逐阶下降 + 升次判定 +
  齐次约束检测"三件套被 limited_integrate 一个循环统一替代，且手推版漏掉
  齐次常数由下层可积性反推的机制（∫(log x+1)/x 类）。非 log(u) 成分 =
  需新 primitive 层，诚实拒答（不是不可积证明——塔覆盖不足 ≠ 初等无解）。
  实测 bug：_from_univar 重写两处——shift 把 embed 后已有 t 维度的 key
  再插入一维（len-3 key，应为替换位置 j）；分母 qe 误带 θ^e 权重
  （c·θ^e = c.p·θ^e / c.q，分母不带权重）。
  验收：log 族全对含升次 log(x)/x = log(x)²/2、嵌套 1/(x·log(x)) =
  log(log(x))、1/log(x) -> NOT ELEMENTARY (proved)（li(x) 类证明性拒答，
  sympy risch 同判）。445 tests。
- **M5.2c 塔域 RDE（进行中，i 阶段已提交 64d2664）**：_rde_tower_solve
  解 exp 层频率方程 D(y)+f·y=g（y ∈ K_j 含低层塔变量）。f=k·η' 不含塔
  变量（exp 守卫）=> 极点分析免 weak_normalizer 直接成立。当前实现 =
  K 域待定系数 + 精确验证兜底。
  **ii 阶段（weak_normalizer 全链）实测发现的核心问题**：按 sympy
  rde.py weak_normalizer -> normal_denom -> spde -> no_cancel 流程移植，
  数值对照实验表明 **sympy 自身在该案例产出不满足原方程的解**
  （F=1+1/x, G=1: wn 吸收 q=x、f_new=1，链路给 y=1，但 D(1)+(1+1/x)=
  1+1/x ≠ 1——差 1/x）。推导确认：wn 变换 f_new=f−q'/q 对应 v=y·q 且
  右端应为 q·G（非 G）；sympy rischDE 未做该右端缩放。两个可能：
  (a) sympy 该路径 bug/调用契约有未理解的隐含约束；(b) integrate_
  hyperexponential_polynomial 的调用场景恰好保证 q=1。**下一步必须先
  对照 FriCAS rdeefx.spad 的 weak_normalization 语义裁定正确变换方向，
  再恢复 ii 实现**（组件代码已验证可用的部分存 stash：_gcdex_qx/
  _wn_qx/_nden_qx/_bd_qx/_spde_qx/_no_cancel_large_qx/_RdeFail）。
  **M5.2c-ii 首轮尝试失败（已回滚，核心未决问题记录）**：
按 sympy rde.py 移植 weak_normalizer→normal_denom→spde→no_cancel 全链，
组件单测全过，但端到端出现**错误否证**（把可积的 eˣ(1/x+log x) 判成
proved 不可积——最严重违反类型）。根因分析：(1) 数值实验确认 sympy
自身 wn→rischDE 链在该类案例同样产出不满足原方程的解（F=1+1/x,G=1:
wn 吸收 q=x 后链路给 y=1，验证差 1/x；用官方测试同款 extension={'D':...}
构造复现）；(2) 数学推导：wn 变换 f_new=f−q'/q 对应 v=y·q 且右端须缩放
为 q·G，sympy rischDE 未做；(3) 修正缩放后仍错——primitive 移位耦合下
"每轮低层 RDE 独立可解"的贪心归约不完备（ℓ¹ 项求解依赖 ℓ⁰ 项配合时，
逐项独立判 FAIL 会误否证整体）。结论：**不能照抄 sympy rde.py 该路径**，
必须先读 FriCAS rdeefx.spad 的 no_cancel_b_large/small/equal 与
weak_normalization 完整语义（其调用契约与右端处理），弄清归约的严格
适用条件后重做。防御性验证器再次拦下错误输出（设计生效）。
**M5.2c-ii 落地（FriCAS 拓扑重做成功）**：
推翻首轮贪心归约后按 intpar.spad 拓扑重建，核心结构 = wn(右端缩放)→
normal denominator(z=h·y, 方程×dh)→界(sympy bound_degree 移植)→
spde 核(a,b,c 各自除 gcd！曾犯 aa=cn/g 污染)→终解分派(large/small/
equal/cancellation 逐度下降)。关键语义修正三处：(1) primitive 视角
耦合项是 (jd+1)·dk·s_{jd+1} 进低次方程（exp 视角才是 f0+j·η 对角）——
上轮失败根因即两者混用；(2) 空列表=零多项式，分母单位必须是 [one]，
fu 运算入口强制规范化；(3) 基层 ℚ(x) 不进塔机制（_univar 剥唯一变量
产生 ()-变组系数与 (x,) 域错位），j==1 直接委托极点分析。切片边界
S-a/S-b/S-c（radical/常数依赖/完整 limited_integrate）触发时诚实
undecided；da=db==0 时 naive 界 n>=dc 不截断故跳过共振修正是可证安全。
验收：e^x*log(x)=Ei 类 proved 与 e^x(1/x+log x)=e^x log x VERIFIED
形成判定分界，差异精确来自 round0 方程 D(s)+s=-1/x 的可解性——算法
正确区分。447 tests 全绿。
**M5.3 三角经复指数落地**：
trigs_to_exp 前置重写（Sin/Cos/Tan/Sinh/Cosh/Tanh，自底向上）+ 虚单位
保留名 i 直通 Poly._build/_frac_num 为 Ga 常量（升参数会丢 i^2=-1 关系
——归组 _ratio 与塔构建全链因此打通）。关键补片三处：(1) exp 视角
special 型 tau-分母（tau 幂单项式）的 Laurent 对角下降——FriCAS
do_SPSE_exp0 的 GP 形态，e^x*sin x 的频率系数恰带 t^-1；(2) m>0 分支
漏掉 special->pos_freqs 转换（m==0 有、m>0 无的不对称，tan 案例暴露）；
(3) _tower_zero 复指数化前置 + Poly.content/RatFunc 构造的域系数泛化
（content 在域上恒为单位元）。新增常被积函数快捷通道（∫c dx=cx，
置于重写前保形态）。旗舰验收：tan/e^x sin/e^x cos 全 VERIFIED（复
形态精确，实化回 sin/cos 属出口层后续），sin(x)/x = Si 类 proved。
行为升级连带三个旧测试期望更新（PROBABLE->VERIFIED 强证书化、parts
不再拒绝可积 dv、sin(y) 常量通道），均逐个验证数学正确性后放行。464 绿。
**出口实化切片一落地（共轭对实化，纯可判定）**：
设计要点：(1) 实性判定 = y == C*(y)（子域叶系数 Ga 共轭 + tau 反转，
RatFunc 分子 is_zero 精确非数值）；(2) 配对公式 s_e*tau^e+s_-e*tau^-e =
2a*cos(e*theta)-2b*sin(e*theta) 直接产出，无幂展开无启发式化简；
(3) 钩子层级教训：实化必须含 t^k 频率因子所在层——先在 Laurent 出口
做丢了外层 e^x 因子，移到 _exp_freq_part 组装层后 b 本身实化（tau=
虚指数层符号）+ 外层实指数因子项形态外乘；(4) term 树结构相等不可靠
（顺序敏感），共轭比较用 RatFunc 差零判定。工程事故记录：patch 脚本
区间替换误删相邻函数（_solve_low/_rde_base_rde/_poly_final），从 git
HEAD 恢复拼接——大文件手术前后必须 grep 函数清单核对。验收：e^x sin/
e^x cos/e^2x sin 教科书形态 VERIFIED；tan 的 log 配对留切片二（诚实
保留复形态）。464 绿。
**实化补片：单层塔 ±k 频率对合并实化（sin(2x) 类）**：
用户压测暴露的缺口——单个 k 分量不实（b_1=1/(2i) 纯虚），±k 对合并
后才实。通道 A（顶层即虚指数层）：全部 ±k 的 b_k 装入显式指数字典
（_from_univar 从 0 起算须乘 tau^klo 补偏移——两次踩坑记录），一次
_realify_laurent；通道 B（嵌套，虚层在系数域）：逐 k 实化 b 本身 +
外层实因子项形态外乘。元组顺序事故：(k,rf) extend 进 (bk,k) 循环 =>
int.to_term 崩溃。验收矩阵：2cos2x->sin2x、cos3x->sin3x/3、
sincos->-cos2x/4、cos^3->3sin/4+sin3x/12 全教科书形态 VERIFIED；
e^ax*sin(bx) 族标准公式形态；嵌套 sin(sinx)/e^sinx 导数在瀑布层被
u=sinx 正向换元截获（真实形态直出），强制复路线则诚实 unsupported
（外层 exp 底含内层塔变量=覆盖边界）。464 绿。
**M5.2c-iii #1 落地：对数导数-根式判定（is_logderiv_radical 移植）**：
最难的升级，一次移植三处收益。数学要点：(1) 守卫判据是 n·D(base)=
D(w)/w（对底数的导数判定）——直接判 base 会漏 e^{log x/2}=√x 类无极点
代数情形（残数视角看不见）；(2) dlog 残数 = 指数·Dπ(根)，在 exp 层带
η 因子而非裸整数——cot 复形态残数 ±i 与 sin-elem 指数 1 一致性由此
调和；(3) sympy heu 的 z-has-no-t 结构定理限制，用常数 P 平凡参数化
（v=1, n·P=m·η, P/η∈ℚ）补全 cot/tan 场景。工程修复链：_tower_deriv_frac
返回单 RatFunc 非元组；base 层剥唯一变量须 _uni_strip 投影；RatFunc
自动约分会吃掉 τ-free 表示（1/(2x)→1/4 事故——系数域与函数域混淆）；
±ix 组成员方向须同步登记进工作 subs（复合底下一轮解析依赖）；
_constant_roots 升级 ℚ(i) 根解析 + 二次精确回退（_ga_sqrt_exact：
norm 开方+半角公式，非完全平方诚实 None）。验收：√log x 拒/嵌套塔
建、x^x 链与 e^{eˣ} 链复 Risch 直出 VERIFIED、∫x^x dx 证明性拒答、
477 tests 全绿（新增 14）。剩余切片：parametric_log_deriv 完整版
（heu 之外的结构定理路径）、limited_integrate 完整版（S-c prim 界
修正）、is_deriv_in_field（S-b B=0 cancellation）、log 配对实化。
**阶段一 #2 落地（S-b 修复 + exp 界修正升级）**：
(1) S-b B=0 cancellation：D(u)=c 纯塔积分经 lam=0 统一下降完备处理——
exp 视角对角（每度独立 D_K(s)=c_jd）、primitive 视角三角（der_fn 移位
进残差），基层落点 λ=0 补 integrate_rational 分支（含 term->RatFunc
包装，此前重构时并掉了 λ=0 分支导致 degenerate 假异常）。验收：
D(u)=x -> x²/2、D(u)=θ -> x·θ−x²/2 精确零检查。(2) exp da==db 共振界
修正从常数比值紧刻画升级为 _pld_heu 全判据（sympy bound_degree exp
分支语义：n_lower==1 时以 m 抬界；heu None 混合证明否定/受限故保守
undecided）。顺带消解 rho.const_val 的 Ga 潜在崩溃点。剩余：S-a/S-c
的 limited_integrate 完整版（primitive db==da±1 修正在用紧刻画）。
**阶段一 #3 落地（limited_integrate 可判定探测版）**：
设计迭代三次的教训浓缩：(1) 首选 Hermite 残数比例判据失败——primitive
塔的 α 极点藏在系数域内部而非 τ-结构层，层内 sqf 对比全盲；(2) 符号-m
线程到底层太重；(3) 终案 = 有界整数探测（m∈1..16）+ _integrate_in_K
域界受限积分探针——复用已证明管线，z 的域界由层参数天然强制。两个
深坑：(a) 基层 λ=0 有理积分以实形态吐 Log 绕过域界（log(x+1) 实为
已建层符号的实形态！）=> _term_within_field 后验门（Log/Exp 参数须
匹配允许层 terms）；(b) 探针返回 term 非 RatFunc 需包装。三态语义
收敛：'no' 不单独存在（范围内全排除与理论受限统一 'und'）——漏修正
会欠界导致误证不可积（最严重违反），多抬界只损失效率，方向安全压倒
覆盖完备。接线双分支：db==da−1 主修正 + db==da 二阶 beta 修正（radical
n_l==1 时 beta=−(a·Dz+b·z).lc/(z·a.lc)）。验收：双层 log 塔正例返最小
有效整数、域外极点负例保守 und，481 绿。
 工程教训：多 patch 脚本区间替换会误删相邻块（fix_ts3 把 [_gcdex..]
   全吃了）——大文件改造必须每步跑测试 + git diff 审查。
**M5.4-c 落地（有理积分通道接受根式系数；假 VERIFIED 事故的架构根治）**：
   **事故复盘（前一会话）**：让根式经全局 ALG_MODULI 注册表进有理通道，
   ∫1/(x²-2) 产出 log(x±2) 形态错误答案却标 VERIFIED——回代映射被
   注册表往返污染（α 塌缩为其极小多项式常数项 2），而验证通道在同一
   变换空间内自洽，假证书闭环。全部回退。**教训定性**：ConstParam 式
   参数化 + 全局关系约简 + RT 求根三者共享可变全局状态时互踩语义；
   验证若在变换后的影子空间进行，证书不覆盖回代步。
   **正确架构（作用域声明而非全局状态）**：QxStruct 投影期局部参数化
   （_collect_rad_params：数值底>0 有理指数幂叶 → _rcN 不透明符号，
   同形共享/异形独立，纯局部映射零全局副作用）；通道内按互相超越独立
   参数做全部判定——**形式恒等 ⇒ 一致特化保真**（多项式恒等证书在
   系数特化 α→√2 下保持：特化是环同态，D 与系数特化可交换），故
   只可能少化简（异形幂不合并、判别式符号 unknown 走 atan 通形），
   不可能错；出口回代还原根式 + free_vars 残留守卫（回代不完整
   诚实降级 UNVERIFIED——上次事故失效形态的直接防线）。
   alg_suspend 保留为防御层（外部残留注册表不干扰本通道）。
   验收：1/((x-√2)(x+√2)) = [log(x-√2)-log(x+√2)]/(2√2) 教科书
   VERIFIED + 数值回验；∛3 线性因子 log(∛3·x+1)/∛3、⁴√2 系数
   atan(x)·⁴√2、混合因子 1/(x(x-√2)) 全通；嵌套根式 √(1+√2) 由
   usub 通道合法截获（非本通道职责）；变量底代数核 1/√(x²+1) 仍
   诚实拒答（M7a 边界）。513 tests。
**M5.4-c 收尾批落地（A1-A4；一次审计牵出三个休眠 bug）**：
   **A4 混合有理积分**：∫1/(x²+i·a) 实测挂死——faulthandler 定位
   ugcd 伪除在"SymRat 内嵌 Ga 叶"的分数塔上指数爆炸（每步系数运算
   经 _rat_add/_rat_mul 嵌套增长，度数有界但规模失控）。修复双头：
   入口守卫识别内嵌 Ga 跳过 gcd（不约分只损效率）；_ga_rational_split
   重写为系数级 (re,im) 对拆分——逐系数取复数对（内嵌 Ga 分母
   有理化：乘共轭，全 Poly 有限运算），Q·Q̄ 实、P·Q̄ 劈实虚，
   两通道各走完整纯参数链。实现教训：首版 Ga 分量组合公式把纯虚
   分量当已具象虚部（i → re=−1！），产出 ∫1/(x²+i) = ∫1/(x²−1) 的
   错答案——数值回验 harness 当场拦截；HEAD 版本对照确认系新引入。
   **A2 AN 符号精确判定通道**：判别式符号分类此前对根式常数一律
   unknown（decide 判不了自由符号）→ 复 atan 通形 + proviso，且
   负判别式形态含负底分数幂、evalnum 拒绝求值（用户无法数值探测）。
   新通道：投影期登记 α 的严格隔离区间（整数缩放 + 二分 floor，
   Fr 端点），符号判定走精确区间算术——四则向外取界、覆盖整个
   区间即穷举证明。这是隔离判定而非数值采样，不违反"采样永不进
   YES 通道"纪律（与 Sturm 同信任级）。验收：1/(x²-√2) 出实 ln 差
   形态零 proviso；x²±√2 两支符号全对。
   **审计牵出休眠 bug 一（M5.4a 极小多项式坏键）**：探针发现
   α·α ≡ 4——_collect_radical 登记的模是零维 Poly((), {(1,):1,
   (0,):-2})，键 (1,) 在 () 空间被 _reduce_alg_var 的 kk[0] 读作
   次数 1 ⇒ 约简按 X−2 进行 ⇒ α≡2 静默错域。M5.4b 的出口约简
   从合入起就在错误模上工作，仅因此前无端到端消费者而休眠。修复 =
   Poly((sym,), {(q,):1,(0,):-(b^p)})。教训：域基建的登记物必须有
   "形状断言"级单测（vars 元数 vs 键元数），否则坏键潜伏到消费方。
   **A3 Trager 范数因子分解**：p ∈ ℚ(α)[x] 的范数 = 乘法矩阵行列式
   （ℚ[x][α]/(m) 自由模，两变量 Poly 构造 + _reduce_alg_var 约简；
   余子式展开 det，n≤5 上限）→ ℚ[x] 上 Zassenhaus 分解 → 逐轨道积
   F 取 gcd_{K[x]}(p,F)。gcd 内部每步余式显式模约简（外层 alg_suspend
   保持参数语义，关系语义仅在 gcd 局部开启——两层语义的作用域隔离）。
   接线教训：初版无条件劫持 is_param_poly 分支，把 deg≤2 也吃了——
   x²-α² 被"分解"为 x²-2（ℚ 因子），教科书 log(x±√2) 形态退化为
   RootOf 形态；修正 = deg≥3 门控（二次保持判别式平方根路径）。
   配套完整性守卫：提取因子次数和 ≠ deg(g) 时诚实放弃。
   **审计牵出休眠 bug 二（_verify 关系盲假阴性）**：Trager 旗舰案例
   数值全对却 ok=False——内部证书的字典相等比较对 1/(2α) 与 α/4
   这类"关系等价但结构异形"的系数失效（分数规范化不含关系约简）。
   修复 = _poly_eq_relaware：差值叶系数经模约简后判零才是精确等词。
   教训定性：验证器的等词必须与计算域的等词同构——域推广时所有
   "结构相等即语义相等"的隐含假设都要重审（与 M5.2b 死循环教训
   同类："恰好够用"的简化在域推广后全部重审）。
   **A1 塔通道现状收口**：纯 AN 常数的塔行为电池全过（e^{√2·x}
   直出 / eˣ/(x±√2) proved 拒答符合 Ei 型预期）；混合塔 RDE 门控
   精确边界 = 复合斜率 η'∈(a+i) 类才触发（纯 Ga 或纯参数轨道均已
   通）；解除门控需 spde/no_cancel 全链系统测试（M5.2c 错误否证
   教训在案——域泛化未经系统测试不得接入 RDE 主链）。proved 拒答
   的下降论证入档：RDE 有理解存在性由残数条件刻画，条件为 ℚ(α)
   上多项式恒等、Galois 稳定 ⇒ 常数域扩张不改变可解性（Bronstein
   结构定理标准推论）；完整构造性版本 = parametric_log_deriv
   （FriCAS parlog.spad 路线，远期项）。518 tests。
**M5 收官批（M5.5 扩容 + M5.6 余项清账）**：
   **M5.5 特殊函数出口结构化**：从两条精确模式匹配扩为四候选族——
   Si/Ci、Ei 线性族（e^(ax+b)/(cx+d) 全参数组合）、li 族、erf 族。
   每候选 verify 背书（导数塌缩回初等域精确判等）纪律不变。
   **Ei 系数公式三易其稿的教训**：d(C·Ei(k(cx+d))) 的链式法则里
   u'/u = kc/(k(cx+d)) 化简后剩 c/(cx+d)——首版漏 c、二版多除 a，
   两次都被"单案例通过"掩盖（a=1 时两种错误公式退化正确），直到
   exp(3x+1)/(2x) 数值回验失败才暴露。教训：参数化公式必须多斜率
   点回验，单例通过≠公式正确。终版：C = coef·e^(b-kd)/c。
   **sqrt(π) 参数化**：erf 答案 (√π/2)erf(x) 的验证链需要
   √π/√π 抵消——L0 对非整指数永不合并，环层无法折叠；命名常数幂
   （Power(pi,±1/2)）经 _npK 独立参数进塔零判定后精确归零。独立性
   假设 Richardson 安全（同 _nc 语义）。
   **_tower_zero 入口归一缺口**：Exp(c)·Exp(u) 双层积（链式法则
   产物）未经 expand+simplify 折叠会让 build_extension 报
   "not covered"——补入口归一（与 integrate_exp_tower 同款），
   验证链对任意微分产物形态鲁棒。
   **M5.6 x^a 符号指数幂**：generic 通道 u^(a+1)/((a+1)·slope) +
   [a+1≠0] proviso（退化点 a=-1 的 ln 路径由 proviso 框架声明，
   generic 语义纪律与 e^{ax}/a 一致）。验证缺口：x^{a+1}/x 与 x^a
   的判等需符号指数合并——_merge_ratpow 从 Int/Rat 放宽到任意项
   （principal 承诺门控不变：diff 幂规则已承诺单值主支 Log，合并
   与微分语义一致）。重写时曾破坏递归结构与变量作用域（NameError）
   ——大函数手术必须每步跑测试 + ast.parse 守门。(c·x)^a c≠1 类
   需要跨 Plus 项的指数归一，超出同底合并能力，诚实 PROBABLE 边界。
   **M5.6#1 常量项系数**：∫π·x dx 此前竟拒答——常量参数化只在塔
   路径做，有理通道不认识 π。_collect_const_params 统一三类极大子项
   （根式/命名常数/函数头复合项）局部参数化，QxStruct 一个通道全收；
   根式叶才登记区间+模（非根式常量项无关系语义）。π/sin(1)/e²/
   log(3)/atan(1/2) 作系数全通 + 数值回验。
   **defint 联动升级**：∫₀¹e^(-x²) 从 unsupported 拒答变为
   √π/2·erf(1) VERIFIED（Newton-Leibniz + 特殊函数出口）——测试
   期望随能力升级更新（诚实标注升级原因）。522 tests。
- **M5.2b 递归塔（多层 primitive/exp）**：塔构建多层化（参数重写到当前
  塔上 + 工作队列循环处理嵌套依赖；代数依赖守卫：exp base 含既有塔变量
  => 拒绝）；_risch_rec 统一层积分入口 + _integrate_in_K 递归下降 +
  _limited_integrate（sympy limited_integrate 同构）。**架构关键**：内部
  全程塔符号空间、出口统一回写——低层积分结果若回写成原始 term，外层
  无法区分"塔变量 l"与"新 log 成分"（驻留形态冲突）。
  **死循环根因（重要）**：_derive_ut 的 K 层导数用 a.deriv(x)——把塔
  变量当常数（D(l)=1/x 算成 0），limited 循环残差不降次永不终止。单层时
  K=Q(x) 下 d/dx 与塔上导数等价，故 M5.1/M5.2a 全绿未暴露——**域推广时
  所有"恰好够用"的简化都要重审**。修复 = 塔上导数（derivation 链式法则）。
  **工作方式教训（用户两次纠偏）**：(1) 跑未验证脚本必须设超时（bash
  timeout 参数 + 脚本内 watchdog/循环上限），死循环卡住整个会话；
  (2) 设计算法前先查参考源码——limited_integrate 的"低层积分结果结构化
  表示"问题 sympy 用多项式对全程传递解决（frac_in），我自行发明的 term
  结构分析（塔符号空间转换）绕了远路。
  验收：log(log(x)) -> NOT ELEMENTARY (proved)（下层 li(x) 证明自然传播
  到整体——递归架构的组合语义）；log(log(x))/x = log·log(log) − log
  [VERIFIED]；log(x)*log(log(x)) -> proved（证明消息精确指向 l^-1 残差）；
  exp(x)+exp(x^2) 双层判定。445 tests。
- **路线图重排：M6 = 规则启发式搜索（SAINT/Rubi），原 M6 四候选顺移 M7**。
  动机 = 六参考系统积分管线源码调研（sympy integrals.py / maxima sin.lisp /
  expreduce calculus.m / mathics calculus.py 实测；Mathematica/Maple 文献）：
  无一家"先跑完整 Risch"——便宜优先阶梯 + 启发式中层 + 算法按需的混合体；
  纯规则库路线由 expreduce（Rubi 快照零算法内核）与 Mathematica 反推实证。
  **定位修正（用户裁定，两轮纠偏）**：初版草案把 M6 当成 !integrate 黑盒
  管线的一层（先排尾端"兜底"、又改排"主力层"）——两个版本都是错误框架，
  根因 = 忽略项目三通道产品结构：①完全手动（:usub/:parts 已有）②自动化
  手动（:isteps 自动生成手动可解释步骤——61 行展示雏形，M6 主战场）
  ③完全黑盒（!integrate + Risch）。SAINT/Rubi 天然属于通道②（Slagle 目标
  即模拟数学家解题、Rubi ShowStep 即人类可读步骤）；黑盒通道不需要 M6，
  Risch 不可解释是本质属性而非缺陷。教训：**设计积分管线前先问"产出物
  是什么"（用户的步骤/系统生成的可重放步骤链/答案+证书），通道决定架构，
  不是算法排序决定架构**。M6.0 裁定问题随之改写：IntStep 从展示结构升级
  为可执行/可重放战术序列（与 :tactic 同构），Rubi 规则翻译目标形态 =
  战术单元而非黑盒变换函数。
  **经验来源纪律（本轮教训）**：建议必须标注来源层级——管线实证（maxima
  diffdiv=usub、第三阶段分部递归、expand 重试限 4 层；sympy risch 前置快筛
  vs maxima 末位兜底、manualintegrate 结构 handler）与文献/Rubi 内容补充
  （Chebyshev 判定、配方反三角族、Euler 代换——来自 Bronstein 教材与 Rubi
  binomial products 章节，不在任何主管线显眼处）不可混述。
  M6 分期草案：M6.0 架构裁定（L2 改写规则 vs 积分专用目标制导变换/Rubi
  DownValues 决策树）→ M6.1 SAINT 核心循环（本地 pyCAS/SAINT 是 Slagle 论文
  Python 复刻，规则编号对应，现成结构参考）→ M6.2 Rubi 精选翻译（章节树
  分期、conditions→guard 3VL、入库自动 D-check、ShowStep↔step log 同构）
  → M6.3 !integrate 策略通道整合。分工裁定：Risch = 塔内判定权威（完备 +
  不可积证明）；M6 = 广度引擎（特殊函数形态 + 每步可解释）；失败语义链共享
  （每层失败留机器可读原因，拒答本身可解释——反面教材：maxima rischint
  noun form 静默失败）。接线形态裁定：Risch 为 integrate 判定终点站
  （现有瀑布不动 → 尾端 Risch 通道 → NOT ELEMENTARY (proved) 专属输出 +
  各层失败证据链汇总）。
- **M5.1b RDE exp 分支（不可初等证明落地）**：频率分解 Σ a_k t^k（正幂商 +
  负幂低段 + residue t 幂剩余统一进频率字典；t·t^{-1}=1 类归并后 k=0 进
  x 层）逐阶解 Risch 微分方程 y' + k*eta'*y = a_k。求解器 = 极点分析定
  分母界（p^m ∥ denom(y) => p^{m+1} | denom(g)，eta' 多项式时 f*y 不升阶）
  => D = Π p^{e-1}，z = y*D 多项式化，待定系数线性方程组 + 高斯消元；
  f = k*eta' != 0 保证齐次只有零解 => 解唯一。**任一频率无有理解 =>
  不可初等证明**（t 在 K 上超越 => 频率分量线性无关，和可积 <=> 各项可积）
  ——RischNonElementary 携带完整原因（哪一阶、RDE 形态、eta'）。
  实测：exp(-x^2)/exp(x^2) -> NOT ELEMENTARY (proved: y'+eta'*y=1 无有理解，
  eta'=±2x)；x^2*exp(x) -> e^x(x^2-2x+2)（高阶多项式 RDE 解）；
  exp(x)*exp(-x) -> x（频率归并）。多层 exp 塔诚实拒答（递归塔 pending
  M5.2——系数域含低层变量破坏 K=Q(x) 假设）。死代码清理：M5.1a 的 wd 版
  _hermite_factor 被 wd=1 版覆盖后未删（Python 后定义遮蔽，两份并存）。
- **M5.1a exp 单项式积分（Hermite 推广 + Rothstein-Trager residue）**：
  K[t] 视图（list[Poly] 升序系数，K=Q(x)）；eta'=wn/wd 的分式系数用"全局
  分母 wd"技巧保多项式系数（整除性推导：u ≡ -(e-1)^{-1} r wd inv(P~) mod p
  => wd*a+(e-1)uP~ ≡ wd(a-r) ≡ 0 mod p）；无平方分解（gcd(D,∂D) 递归，
  层差恢复重数）+ 部分分式（inv mod p^e）+ 逐层 Hermite（复用已验证的
  _hermitte_power 结构推广到塔上 D）+ residue（R(z)=res_t(B-zDp,p)，
  Sylvester 矩阵 + Bareiss 行列式；常数根经现有 solve，含 x 的根丢弃=
  不可初等成分的数学语义；solve 定不了根显式异常——绝不静默漏根把可积
  误判为不可积）。剩余整除 p 时商进 leftover（x 层 Hermite+RT 递归）。
  **层级教训（大弯路）**：K[t] 与 K[z] 同构（都是 list[Poly]，系数运算
  全是 Poly 算术）——初版给 K[z] 写独立 _uz_* 层是重复且引层级混乱，
  删掉后 _u_* 直接通用。
  **五个实测 bug**：EEA 初始化反了（s0/s1 互换 => inv(1)=0 => 部分分式
  分子全零静默传播成错误答案 0——符号计算的静默错典型形态）；Poly 坏键
  {(): c}（零维元组，Poly.__init__ 不校验维度，潜伏到 degree 才爆）；
  Poly != int 恒 True（__eq__ NotImplemented 回退身份比较）；_u_pow 初始
  out=[zero]（应为乘法单位 [one]）；测试侧 D-check 语义写反（比较 d(f)
  而非 f 本身——验证关系 D(F)=f 的对象是 f）。验收 = 已知闭式逐项比对
  + D(result) vs f 数值采样双通道。e^{-x^2} 目前 has-poly-part（M5.1b
  RDE 补齐后即完整不可初等证明）。
- **M5.0 微分域塔落地（Risch 一期地基）**：cas/risch.py——DiffExt
  （levels/cases/ws/terms 四表，maxima 属性表存导数同思路）、塔构建
  （log 先 exp 后 = sympy handle_first='log'；integer_powers Fr 倍数归组，
  content=1 规范基；参数限 Q(x)）、derivation（扁平多元 Poly 全变量链式
  法则，maxima spderivative 对应物）、term<->塔双向转换。
  **验收纪律的教训**：冒烟打印"D(f) = -2x/t"当场没看出是错的（应为
  -2xt）——dpair 把 t 因子传进了分母位。三个实测 bug：dpair 参数顺序；
  _ratio 的 deg<=1 提前返回砍掉 e^(x^2)/e^(2x^2) 归组（udivmod 本身就能
  判常数商）；测试侧商法则写错（D(a/d) 分子用 d 不是 D(d) 的分母、分母
  漏 d^2）。**最终正确性证据 = 双实现差分**：derivation（链式法则）vs
  diff.d（spec 表驱动）数值采样交叉核对 + 回写重建塔的规范形逐项还原
  （Q(x,t) 表示唯一性，比 equivalent 采样强——超越式判等只有 PROBABLE）。
  采样点须取正（log 定义域）、容差用相对误差（大数值处 float64 绝对
  误差放大）。诚实拒绝路径全测：代数依赖 exp(log(x)/2)、嵌套超越
  exp(x*e^x)、三角 sin(x)（M5.3 经复指数解除）。
- **RootOf 接线与语义统一（"拿不出根"的诊断与修复）**：诊断——factor 在 Q 上
  本来完备（不可约就是正确结论），缺口是 solve 对不可约 >=3 次直接拒答，而
  RootOf 数据结构 + Sturm 隔离早已存在（被积分器独占）。修复 = 纯组装：
  _poly_solve 尾部 factor 逐因子分派（deg1 线性 / deg2 根式 / >=3 不可约 ->
  RootOf(g,k) 实根）。**语义裁定**：RootOf(m,k) 全根编号（Mathematica
  Root[f,k] 式）——实根按升序占 1..r（Sturm 隔离序），复根占 r+1..deg(m)
  仅编号不承诺几何序；比 SymPy CRootOf（只索引实根）多给稳定编号。积分器
  j=1..n 全根循环天然兼容（迹方法不依赖单根定位）。**复根隔离债务注销**：
  消费场景全在实数域（ineq/solve），除非要 Mathematica 式全根几何序否则无需
  Collins-Krandick 矩形细分。配套：check_solution 加因子整除判定（g 不可约
  即 beta 极小多项式，p(beta)=0 <=> g|p，代数恒真三态完备）；check_solution
  补 expand（复根代回 (i*sqrt(3)/2-1/2)^3-1 类乘积幂需展开后 i 幂才折叠，
  纯 simplify 不展开乘积幂——既有缺口顺手修）。
- **Gröbner 基落地（朴素 Buchberger + 消元求解）**：单项式序 lex/grevlex
  （grevlex key = (总次数, 反转取负)）、多变元完全归约、S-多项式、第一判则
  剪枝（首单项式互素必归零）、reduced basis 迭代重建（成员被其余消去即删除，
  理想不变）。solve_system：lex 消元定理只保证最末变量有单变量基元素
  （正维检测只查 vars[-1]——初版要求每个变量都有是方向性错误）；回代从
  最末变量起，有理解代入继续、根式/RootOf 解诚实截断（partial + note，
  Q 系数域不支持代数数系数多项式——代数数扩张是远期项）。实测教训三个：
  _poly_solve 只认一元 Poly（指数元组 1 维），消元多项式须投影
  （(0,2)->(2,)，否则 monos.get((2,)) 取不到系数产生 Undefined）；_only_in
  初版错误要求每个单项都含目标变量（y-1/2 的常数项被误判）；And 是 n 元头
  （AC flatten），walk 拆方程必须遍历全部 args。!gsolve 语法
  `f1 && f2 for x,y`，解代回验证 VERIFIED。
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
- **剩余结构债**：代数数系数多项式（Gröbner 回代遇根式/RootOf 解的继续化）。

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
- RootOf 实根有 Sturm 隔离区间（升序即 idx 序）；复根仅共轭类编号
  （语义裁定见 §1.1 RootOf 接线条目——除非需要全根几何序，否则不建复根隔离）。
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
