# 进度

本文记录当前实现状态与下一步。与 `docs/cas_v3_arch.md`（设计权威）分开维护。

## 已完成

### 地基
- **L0 驻留项层**（`cas/term.py`）：不可变 hash-consing 树，AC 拉平+排序，绑定变量（de Bruijn），纯句法无域语义；And/Or 句法折叠（真值常元吸收、排中/矛盾律坍缩）
- **ℚ 字面算术**（`cas/qarith.py`）：`fold` 显式折叠（含普适恒等 b^1=b）+ `eval_exact` 环层精确求值
- **域系统**（`cas/domains/`）：`Domain` 协议（normalize/equal/member，`equal` 返回 `bool|None`——None 为非成员越界，片段内无 UNKNOWN）+ `Ring` 协议（含系数导数 `deriv`）。**能力字段**（架构 3.2）：`is_field`/`is_ordered`/`is_euclidean`，算法按能力分派不按类型特判
  - ℤ：`ZZRing`（带余除法/gcd/扩展gcd）+ `ZDomain`——有序欧几里得整环，非域；丢番图可判定碎片的宿主
  - ℚ：`QRing` + `QDomain`
  - ℚ(i)：`QIRing` + `QIDomain`（`cas/domains/qi.py`）——第一个代数扩张 = ℚ[z]/(z²+1)：元素为 (re, im) 标准形对（结构判等），除法走共轭×范数；成员通道 = 闭项 i↦z → ℚ(z) 有理函数 → 模 z²+1 约化（Maxima 代数量模式）；i 常数身份由图书馆声明在投影层注入，不做名字嗅探；能力 is_field=True / **is_ordered=False（复数无序，序判定按能力查表拒绝）** / is_euclidean=False（欧几里得结构属于 ℤ[i]）。参照经验见 reference.md"已消化经验"
  - K[x₁..xₙ]：`PolyDomain`，稀疏系数字典，泛 Ring 协议，单变量欧几里得 GCD + 域系数精确除法 + **域导数 `p_deriv`**；能力：单变量+域系数才是欧几里得
  - K(x₁..xₙ)：`RatFuncDomain`，交叉相乘判等 + 单变量 GCD 约简 + **域导数 `rf_deriv`（商规则）**；能力：恒为域，单变量欧几里得
- **判定契约**（`cas/verdict.py`）：Verdict ADT（`Yes(proof)/No/Unknown(reason)`），理由枚举 FRAGMENT/GUARDED/UNDECIDABLE/BUDGET，and3/or3/not3 传播首个 Unknown 理由
- **域投影层**（`cas/project.py`）：成员测试阶梯 ℤ → ℚ → **ℚ(i)** → K[x] → K(x)——域由投影赋予，不做叶嗅探；`zero_of` 判零快捷通道（常数格统一走域判等，任意常数域泛化）
- **判定管线**（`cas/decide.py`）：全通道返回 Verdict；区间通道（BFS 链查询已修）、结构符号引理、图书馆常数界与函数值域界（端点语义按算子分治）、深度上限 BUDGET 诚实
- **图书馆**（`library/`）：`ConstantDecl`/`FunctionDecl` 冻结 dataclass + 注册表 + 定义域条件注册
  - 常数：π, e, i, γ（正性、粗界、实性声明）
  - 函数：sin, cos, tan, exp, log, sqrt, abs, atan, sinh, cosh, tanh（印名、元数、值域界、定义域条件）
  - **导数模板作为数据**：每函数声明 `deriv` 模板（de Bruijn `DB(0)` 占位）；无条件恒等式才入册；分支破裂者以 Piecewise 容器如实声明（`Abs` 导数 = `piecewise(1 if u>0, -1 if u<0)`，u=0 无支即不可导）
  - 规则声明（exp_add 等）经统一规则引擎装配
- **规则引擎**（`cas/rules.py`）：单引擎；守卫经 decide Verdict；auto 规则仅限无守卫（防 decide↔simplify 互递归）；`autosimplify` 严格代价下降保终止
- **工作流**（`cas/workflow.py`）：Step DAG（七字段：id/content/derivation/guards/status/target/reads/clears/domain）+ 七种推导类型（Claim/BothSides/Rewrite/Solve/Subst/Split/**Diff**）+ 守卫指针去重与 Split 清偿 + 死步骤级联
  - **验证器-求解器独立**：Solve 验证器只做回代判官（代入+投影判零，不重跑求解）；Diff 验证器用域层导数交叉复核项层结果；Rewrite 复核图书馆规则产物；Split 排中律覆盖验证
  - 域归属：步骤内容经投影记录所属域（步骤展示 ∈K[x]/K(x)/Q）
- **战术层**（`cas/tactics.py`）：线性求解战术 + 丢番图碎片——线性丢番图（扩展欧几里得，裴蜀证书+周期参数化）、单变量整数根（有理根定理完备候选）+ **分段方程求解**（`solve_piecewise`）。线性分类内核 `_lin_core` 在**投影标准形**上裁决（语义判据非形状判据）：恒零→恒等式/区域解、无变元非零→矛盾/无贡献、恰一次→-b/a 证书、其余（非线性/多变量/域外）拒答；分段求解逐支消费同一分类（闭式支走判零通道），任支超出片段整体拒答保完备性；只交证书，验证独立
- **公共算法机器**：
  - 线性代数（`cas/domains/linalg.py`）：域上高斯消元、秩、零空间基、方程组求解（特解+齐次基/不相容判定）、Bareiss 整数行列式
  - 结式与无平方（`cas/domains/polytools.py`）：结式（余式序列递归，共根判据+求值锚点）、Yun 无平方分解（monic 因子×重数）
  - 一维 CAD（`cas/cad.py`）：单变量多项式条件 → 有序互斥胞腔（开区间+点），Sturm 根隔离精确定符号；条件非单变量多项式分区按 FRAGMENT/UNDECIDABLE 拒答
  - 积分骨架（`cas/integrate.py`）：多项式幂规则不定积分、分段逐支；定积分遵定义域∩[a,b]（缺口不对 0 积分、点洞拒答）；`verify_antideriv` 微分层独立复核
- **微分**（`cas/diff.py`）：任意数域系数 × 任意已声明函数域的结构微分——线性/莱布尼茨/幂-指数-一般幂规则/图书馆模板实例化×链式法则；缺模板、绑定体内微分诚实抛 `DiffError`。**分段求导审慎通道**（`differentiate_piecewise`）：逐支求导 + 分段点（点胞腔）显式列出未验证——开区间胞腔上导数成立，分段点可导性须极限层（未建），绝不逐支冒充整体导数
- **分段容器**（`cas/piecewise.py`）：`Piecewise(v,c,...)` 语法容器（非数值域）——求值语义为**有序首中**（if/elif/else，`⊤`=否则支；每点至多落一支 → 取值天然唯一，无求值层冲突）：`select` 取值、`coverage` 覆盖、**`collapse` 点塌缩**（任意深度的分段子项按有序首中塌缩为支值，数值点回代判定的公共通道）；分支体**独立投影**无共享宿主（`project_pw`）；运算**逐支笛卡尔提升**（`lift`，`(f⊕g)(x)=f(x)⊕g(x)`，条件取合取、空组合丢弃）；`conflicts` 作**顺序无关性 lint**（交叠处值不等→提示收紧为互斥守卫，判不动即 Unknown，不作求值闸）；`domcond` 对分段产出条件化守卫 ¬cond∨支约束；`fold_nested` 嵌套展平、`domain_cells`/`connected_components` 定义域胞腔与连通分量；`Abs` 导数据此以 Piecewise 如实入册（`sign`，u=0 无支）
- **REPL**（`repl.py`）：claim/both/norm/solve/subst/**split/diff/rules/apply/integrate/int**/check/steps/undo——solve/diff 对分段自动路由：分段方程逐支求解（点解入账走回代判官、区域解/条件解如实报告）、分段求导走审慎通道（分段点未验证标注）；check 对含分段项点塌缩后判零
- **压力台架**（`stress/`）：41 条性质，全自证无外部真值
  - P1-P4：折叠保真、幂等指针、区间真值表、回代判官
  - P5-P9：多项式往返、判等完备、交叉相乘、GCD 整除
  - P10-P13：项层微分 × 域层导数交叉、线性/莱布尼茨/商规则恒等、泰勒 h¹ 系数、验证器独立性
  - P14-P17：秩-零化度、相容/不相容判定、Bareiss 乘法性、丢番图证书（裴蜀/周期本原/整数根全集）
  - P18-P20：结式求值锚点、共根判据×对称性（结式 vs GCD 双算法交叉）、无平方往返
  - P21-P24：分段投影逐支独立、选支语义（具体点参照扫描）、运算逐支提升×逐点一致、守卫条件化+重叠一致性
  - P25-P28：CAD 胞腔排序互斥覆盖、样本点符号一致、拒答理由（FRAGMENT/UNDECIDABLE）、点胞腔符号（Sturm 消没判定）
  - P29-P31：分段归一化往返、连通分量划分、缺口断开
  - P32-P35：不定积分往返+两通道、可加性/FTC、分段定积分、积分拒答边界
  - P36-P38：分段求导两通道交叉+分段点定位、分段解方程独立参照（含区域解/拒答）、工作流端到端（真解入账/伪解否决/Diff 逐支交叉验证）
  - P39-P41：ℚ(i) 双通道交叉（环对偶运算 vs i↦z→ℚ(z)→模约化成员通道）+域公理、成员边界+规范化幂等、阶梯×判零×能力字段×积分常数通道

### 阶段1-5：分段通道（CAD 地基 → 解方程/求导 → REPL 接线）
- 阶段1：最简 CAD——一维实根隔离（Sturm）+ 胞腔分解（开区间/点），条件符号精确判定
- 阶段2：分段归一化（`fold_nested` 嵌套展平）+ 定义域胞腔提取（`domain_cells` 消费 CAD，Undefined 切断）
- 阶段3：手通道定/不定积分骨架——多项式片段 + 独立验证器（微分层复核），定积分定义域诚实边界
- 阶段4：分段求导（审慎通道：逐支导数 + 分段点显式未验证）+ 分段解方程（常值支区域解/线性支条件裁决/非线性拒答）
- 阶段5：REPL 接线（solve/diff 分段自动路由）+ 工作流验证器分段感知——Solve 回代判官经 `collapse` 点塌缩（任意深度分段 + 定义域外判非解），Diff 验证器逐支域层导数交叉；端到端台架 P36-P38

### 架构整修（2026-08-27）
- 裸 `T3` 三值全部替换为带理由的 Verdict ADT
- 废除 `cas/domain.py`、`cas/structure.py`、`cas/domain_decls.py`——域操作支持矩阵的伪登记与叶嗅探分支政策清除
- decide/workflow 中的叶嗅探域判定改为投影层成员测试
- 异常吞没清除；`_chain_query` BFS 陈旧状态 bug 修复
- `term.py` 潜在 NameError（`_fold_bool_ac` 缺失）与 `poly.py` 缺失 `RingError` 导入修复

### 硬编码语义驱逐
- 常数单例从 `cas/term.py` 移至 `library/constants.py`
- `_CONST_BOUNDS` 表从 `decide.py` 移至图书馆 `const_bounds`
- `t is PI or t is E` 特判改为 `library.const_positive/const_real`
- simplify 的 Exp 合并特判删除，规则作为图书馆数据声明
- parser 常数表从图书馆导入

## 未完成（地基优先——Risch 门控）

用户指令：完整 Risch（含参数积分与超越数积分，参照 FriCAS）是最终目标，但**地基完工前不启动**。地基 = 下述算术与结构机器全部就位。

### 交互通道
- [ ] √(u²)→|u| 改写规则：Piecewise 容器与 Abs 导数就位后，尚缺实性假设通道（u 为任意实数才成立），入册前须先接通
- [ ] 工作流序列化与回放
- [ ] 撤销/重做的真正实现（当前只移动指针不删步骤）
- [ ] 版本化上下文折叠（读写双向索引）
- [ ] Split 分支的后续求解（切完未消费）

### 战术层
- [ ] 二次方程求解（判别式分支切割）
- [ ] 循环方程求解（多前驱 DAG + 线性系统）
- [ ] 一般丢番图按定理拒答接线进工作流（UNDECIDABLE 理由通道）
- [ ] 多参数函数偏导、绑定体内微分（依赖量词/积分地基）

### 数域扩展（Risch 前置）
- [ ] ℚ(i)[x]/ℚ(i)(x) 系数环挂载：poly/ratfunc 的闭项系数吸收通道（Ring 吸收 ℚ(i) 常数子项）+ project 多环阶梯（ℚ[x] 落空后试 ℚ(i)[x]）；消费方审计（cad/tactics/workflow 的 Q_RING 硬编码处按能力改派）
- [ ] ℤ[i] 高斯整环：范数带余除法 + gcd（欧几里得）+ 高斯因式分解（参考 fricas gaussfac.spad）
- [ ] ℚ(α) 代数扩张通用化（mod-m 余式 + Thom 编码；元素表示取模 minpoly 多项式形——参考 fricas algext.spad SAE 的 Rep := UP）
- [ ] ℚ(α) 代数扩张（mod-m 余式 + Thom 编码）
- [ ] 参数分式域 ℚ(t₁..tₙ) 作系数环
- [ ] 多变量 GCD（接入 ratfunc 约简标准形）

### 序与根比较（arch §7.4 分层，消费 CAD/判定管线）
- [ ] L2 区间算术比较层：可计算超越函数的任意精度区间求值，分离即判、重叠即 Unknown（接 decide 管线常数比较通道；裸浮点禁止入符号通道）
- [ ] L3 图书馆序引理：单调性/零点集/周期/凸性作为 FunctionDecl 数据入册（准入纪律同导数模板：无条件可证才入册）
- [ ] L4 超越根对象：(方程, 隔离区间) + 加细协议；等号仅在可证时成立
- [ ] 条件化答案容器：端点序未决时按参数条件分支给出答案 + 完备性声明 complete/partial（arch §7.5 出口 1）

### 公共算法机器（Risch 前置）
- [ ] Zassenhaus 因式分解（ℤ 提升）
- [ ] 部分分式、Hermite 约化
- [ ] 子结式链（结式的序判定推广，Thom 编码依赖）
- [ ] 超越塔结构（tower 表示 + 初等扩张判定）——FriCAS 对应层；微分塔上先行，积分塔随后

### 远期
- 不定积分（Risch 完整版）、定积分、极限级数、求和差分、ODE
- 不等式求解与 CAD
- transseries
