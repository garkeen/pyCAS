# 进度

本文记录当前实现状态与下一步。与 `docs/cas_v3_arch.md`（设计权威）分开维护。

## 已完成

### 地基
- **L0 驻留项层**（`cas/term.py`）：不可变 hash-consing 树，AC 拉平+排序，绑定变量（de Bruijn），纯句法无域语义；And/Or 句法折叠（真值常元吸收、排中/矛盾律坍缩）
- **ℚ 字面算术**（`cas/qarith.py`）：`fold` 显式折叠（含普适恒等 b^1=b）+ `eval_exact` 环层精确求值
- **域系统**（`cas/domains/`）：`Domain` 协议（normalize/equal/member，`equal` 返回 `bool|None`——None 为非成员越界，片段内无 UNKNOWN）+ `Ring` 协议（含系数导数 `deriv`）。**能力字段**（架构 3.2）：`is_field`/`is_ordered`/`is_euclidean`，算法按能力分派不按类型特判
  - ℤ：`ZZRing`（带余除法/gcd/扩展gcd）+ `ZDomain`——有序欧几里得整环，非域；丢番图可判定碎片的宿主
  - ℚ：`QRing` + `QDomain`
  - K[x₁..xₙ]：`PolyDomain`，稀疏系数字典，泛 Ring 协议，单变量欧几里得 GCD + 域系数精确除法 + **域导数 `p_deriv`**；能力：单变量+域系数才是欧几里得
  - K(x₁..xₙ)：`RatFuncDomain`，交叉相乘判等 + 单变量 GCD 约简 + **域导数 `rf_deriv`（商规则）**；能力：恒为域，单变量欧几里得
- **判定契约**（`cas/verdict.py`）：Verdict ADT（`Yes(proof)/No/Unknown(reason)`），理由枚举 FRAGMENT/GUARDED/UNDECIDABLE/BUDGET，and3/or3/not3 传播首个 Unknown 理由
- **域投影层**（`cas/project.py`）：成员测试阶梯 ℤ → ℚ → K[x] → K(x)——域由投影赋予，不做叶嗅探；`zero_of` 判零快捷通道
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
- **战术层**（`cas/tactics.py`）：线性求解战术（投影→次数检查→-b/a）+ 丢番图碎片——线性丢番图（扩展欧几里得，裴蜀证书+周期参数化）、单变量整数根（有理根定理完备候选）；只交证书，验证独立
- **公共算法机器**：
  - 线性代数（`cas/domains/linalg.py`）：域上高斯消元、秩、零空间基、方程组求解（特解+齐次基/不相容判定）、Bareiss 整数行列式
  - 结式与无平方（`cas/domains/polytools.py`）：结式（余式序列递归，共根判据+求值锚点）、Yun 无平方分解（monic 因子×重数）
- **微分**（`cas/diff.py`）：任意数域系数 × 任意已声明函数域的结构微分——线性/莱布尼茨/幂-指数-一般幂规则/图书馆模板实例化×链式法则/**分段逐支求导**；缺模板诚实抛 `DiffError`
- **分段容器**（`cas/piecewise.py`）：`Piecewise(v,c,...)` 语法容器（非数值域）——分支体**独立投影**无共享宿主（`project_pw`）、条件交判定管线（`select` 首个真支且其前皆假、`coverage` 覆盖、`conflicts` 重叠一致性逐对判等，判不动以 Unknown 诚实传播）、运算**逐支笛卡尔提升**（`lift`）；`domcond` 对分段产出条件化守卫 ¬cond∨支约束；`Abs` 导数据此以 Piecewise 如实入册（`sign`）
- **REPL**（`repl.py`）：claim/both/norm/solve/subst/**split/diff/rules/apply**/check/steps/undo
- **压力台架**（`stress/`）：24 条性质，全自证无外部真值
  - P1-P4：折叠保真、幂等指针、区间真值表、回代判官
  - P5-P9：多项式往返、判等完备、交叉相乘、GCD 整除
  - P10-P13：项层微分 × 域层导数交叉、线性/莱布尼茨/商规则恒等、泰勒 h¹ 系数、验证器独立性
  - P14-P17：秩-零化度、相容/不相容判定、Bareiss 乘法性、丢番图证书（裴蜀/周期本原/整数根全集）
  - P18-P20：结式求值锚点、共根判据×对称性（结式 vs GCD 双算法交叉）、无平方往返
  - P21-P24：分段投影逐支独立、选支语义（具体点参照扫描）、运算逐支提升×逐点一致、守卫条件化+重叠一致性

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
- [ ] ℚ(i) 高斯域（Ring 协议实现）
- [ ] ℚ(α) 代数扩张（mod-m 余式 + Thom 编码）
- [ ] 参数分式域 ℚ(t₁..tₙ) 作系数环
- [ ] 多变量 GCD（接入 ratfunc 约简标准形）

### 公共算法机器（Risch 前置）
- [ ] Zassenhaus 因式分解（ℤ 提升）
- [ ] 部分分式、Hermite 约化
- [ ] 子结式链（结式的序判定推广，Thom 编码依赖）
- [ ] 超越塔结构（tower 表示 + 初等扩张判定）——FriCAS 对应层；微分塔上先行，积分塔随后

### 远期
- 不定积分（Risch 完整版）、定积分、极限级数、求和差分、ODE
- 不等式求解与 CAD
- transseries
