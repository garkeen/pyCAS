# 进度

本文记录当前实现状态与下一步。与 `docs/cas_v3_arch.md`（设计权威）分开维护。

## 已完成

### 地基
- **L0 驻留项层**（`cas/term.py`）：不可变 hash-consing 树，AC 拉平+排序，绑定变量，纯句法无域语义
- **ℚ 字面算术**（`cas/qarith.py`）：`fold` 显式折叠 + `eval_exact` 环层精确求值
- **数域系统**（`cas/domains/`）：`Domain` ADT（normalize/equal/member）+ `Ring` 协议
  - ℚ：`QRing` + `QDomain`
  - K[x₁..xₙ]：`PolyDomain`，稀疏系数字典，泛 Ring 协议，单变量欧几里得 GCD + 域系数精确除法
  - K(x₁..xₙ)：`RatFuncDomain`，交叉相乘判等 + 单变量 GCD 约简
- **图书馆**（`library/`）：`ConstantDecl`/`FunctionDecl` 冻结 dataclass + 注册表 + 定义域条件注册
  - 常数：π, e, i, γ（正性、粗界、实性声明）
  - 函数：sin, cos, tan, exp, log, sqrt, abs, atan（印名、元数、值域界、定义域条件）
- **判定管线**（`cas/decide.py`）：三值逻辑 + 区间通道 + 常数界引理（走图书馆）+ 命题复合（and3/or3/not3）
- **工作流**（`cas/workflow.py`）：Step DAG + 六种推导类型（Claim/BothSides/Rewrite/Solve/Subst/Split）+ 守卫提取与传播 + 域验证器
- **REPL**（`repl.py`）：交互式命令界面（claim/both/norm/solve/subst/check/steps/undo）
- **压力台架**（`stress/`）：9 条性质 ×5 种子全绿
  - P1-P4：折叠保真、幂等指针、区间真值表、回代判官
  - P5-P9：多项式往返、判等完备、交叉相乘、GCD 整除

### 硬编码语义驱逐
- 常数单例从 `cas/term.py` 移至 `library/constants.py`
- `_CONST_BOUNDS` 表从 `decide.py` 移至图书馆 `const_bounds`
- `t is PI or t is E` 特判改为 `library.const_positive/const_real`
- simplify 的 Exp 合并特判删除，规则作为图书馆数据声明
- parser 常数表从图书馆导入

## 未完成

### 交互通道（当前优先）
- [ ] 规则应用管线：图书馆声明的规则（exp_add 等）未接线进 simplify/workflow
- [ ] Split/Merge 在 REPL 中无命令入口
- [ ] 工作流序列化与回放
- [ ] 撤销/重做的真正实现（当前只移动指针不删步骤）
- [ ] 版本化上下文折叠（读写双向索引）

### 战术层
- [ ] 二次方程求解（判别式分支切割）
- [ ] 有理根定理（完备候选集穷举）
- [ ] 循环方程求解（多前驱 DAG + 线性系统 solve）

### 数域扩展
- [ ] ℚ(i) 高斯域（Ring 协议实现）
- [ ] ℚ(α) 代数扩张（mod-m 余式 + Thom 编码）
- [ ] 多变量 GCD（接入 ratfunc 约简标准形）

### 公共算法机器
- [ ] 无平方分解、结式、Zassenhaus 因式分解
- [ ] 部分分式、Hermite 约化
- [ ] 线性代数（行消元、Bareiss、零空间）

### 远期（路线图见 arch 文档第四节至第六节）
- 微分、不定积分（Risch）、定积分、极限级数、求和差分、ODE
- 不等式与 CAD
- transseries
