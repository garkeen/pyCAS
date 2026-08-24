# M7 设计档案：ℚ(B)[α] 代数扩张完备域

> 调研依据：FriCAS `intalg.spad`/`intaf.spad`（本地 `../fricas/src/algebra/`）
> 全文通读 + pyCAS 代数资产审计。本文是 M7 各步的实现权威；里程碑定义
> 仍以 `cas_v2_arch.md` §6 为准。

## 1. FriCAS 算法骨架（intalg.spad :767 行 / intaf.spad :883 行）

### intalg.spad —— 代数曲线上的一般积分（三件套）

| 包 | 核心 | 算法 |
|----|----|----|
| `DBLRESP` DoubleResultantPackage | `doubleResultant(f, D)` | 残数多项式：r(z) 的根 = f 在全部有限极点处残数的有理倍数。两级结式：先对 θ 结式（`num − z·g·D(d)` 与 definingPolynomial），再对 x 结式消元 |
| `INTHERAL` AlgebraicHermiteIntegration | `HermiteIntegrate(f, D, d0) → [g,h]` | 迹+整基坐标：f 表为整基 w₁..wₙ 坐标向量，`integralDerivationMatrix(D)` 给乘法-导子矩阵；对每个重数>1 的分母因子 v^j 解线性系 mod v^j（对角情形 extendedEuclidean，一般情形 RF 上线性求解）|
| `INTALG` AlgebraicIntegrate | `algintegrate / palgintegrate` | 顶层分类：D(x)/x 为常数倍 → exp 路线（Laurent 分离后 Hermite）；否则 primitive 路线。log 部分走 `alglogint/palglogint` |

**log 部分装置**（palglogint，intalg.spad :403）：
1. doubleResultant 得 r(z)；系数随 D 变动 → fail（varRoot? 守卫）
2. factor(r)，按"有理倍数关系"分组因子（find_multiples：p₁ 与 p(nfac·t)·nfac^(−k) 同组——共轭对称类）
3. 组内偶/奇对称处理 + **divisor/torsion 判定**（FiniteDivisor 减法 + torsionIfCan：找 u 使 div(u)=n·D——这是 ∫dx/√(x²+1) 类 log 项的来源）
4. trace1：残数间 ℚ-线性关系的普遍情形（doubly transitive 假设下单条 generic log）
5. mkLog 输出 (scalar:ℚ, coeff∈K[α], logand∈K[α])；出口前 diff1==0 精确核验

**椭圆分支**：GenerateEllipticIntegrals 仅处理 y²=P₃₄ 曲线，输出第一/第二类椭圆积分特殊形（我们对标为 proved 拒答，不实现生成）。

### intaf.spad —— 纯代数函数的分层快通道

调度序 `palgint(f, x, y)`（intaf.spad :673）：
1. `linearInXIfCan`：minpoly 清分母后对 x 至多一次 → 直接代换 x=h(u)
2. `quadIfCan`：y²=二次式 → **genus-0 有理化** quadsubst：
   - p 无平方：u = den·y − x√a，x=(u²−c)/(b−2u√a)
   - √a 已在常数域：u = (den·y−√c)/x
   - 新引入的 √a/√c 记入 newk，出口 rationalize_ir 用共轭对消去
3. nthRoot → `prootintegrate`：yⁿ=g(x) 归一（chvar），radicand 对候选 u 多项式复合可线性化 → 有理积分；否则 RadicalFunctionField 走 intalg 一般路线
4. rootOf → 直接 AlgebraicFunctionField 一般路线

**关键结构认知**：FriCAS 把"便宜的有理化换元"放在一般理论前面省力，但正确性兜底始终是 intalg 的 Hermite+doubleResultant+torsion 三件套。

### 我们的对标取舍

| FriCAS | pyCAS M7 取舍 |
|----|----|
| FunctionFieldCategory 整基（integral basis） | **不引入整基**——我们的基域是 ℚ(params)(x) 特征零且塔表示自带坐标；Hermite 推广用迹方程直接解（M7.4 时再评估） |
| divisor/torsion（PointsOfFiniteOrder） | M7.1/M7.2 以 z-常数中间层 + K[root] 约束等价实现（残根落域即 torsion 函数的显式载体） |
| genus-0 快通道 | 保留思想：M7.4 入口先试 linearInX/quad 参数化，失败落一般路线 |
| ExpressionFactorPolynomial 常数域分解 | 复用 poly.factor（Zassenhaus，仅 ℚ）+ SymRat 当变量分解 |
| FAIL0..FAIL4 实现不完全错误 | 对应 RischUnsupported 具名卡点（诚实拒答协议） |

## 2. pyCAS 代数资产审计（M6.7 后现状）

**可复用底座（直接消费）：**

| 资产 | 内容 | M7 角色 |
|----|----|----|
| `univar.py` | K[t] 稠密算术 19 函数（升序 list、域系数、monic gcd、u_inv_mod/u_xgcd/u_diophantine/u_gauss_solve_k）；系数域鸭子类型：支持 `+ - * / is_zero one` 即可 | **元素表示层**：K[B][α] 元素 = 约简后的系数 list |
| `algnum.py` | qa_*(mod 算术)/uexgcd/RootOf(Sturm 序)/tr_power_sums/tr_eval(牛顿幂和迹)/real_isolation | ℚ 特例参考实现 + RootOf 编号语义沿用 |
| `poly.py` | uresultant(:375)/udiscriminant(:431)/原始 PRS mgcd/_prem(:595)/SymRat(:692) | 结式参考 + 基环算术 |
| `ratfunc.py` | RatFunc 无条件约分规范形 | B = ℚ(x,params) 函数域的载体 |

**三套并行表示（M7.0 要消灭的债务）：**

| 注册表 | 位置 | 写入方 | 消费方 |
|----|----|----|----|
| `ALG_MODULI`（全局） | poly.py:11 | risch_core:279（根式参数化时同步登记） | Poly._alg_reduce_out 乘积出口自动模约简、apart gcd、ratint:415 合并读取 |
| `ALG_RELATIONS`（全局） | risch_core:245 | risch_core:277 | apart:261、structure Layer.AN 检测 |
| `AN_INTERVALS`/`AN_RELATIONS`（作用域） | ratint.py:216-217 | QxStruct.project 登记/retract 弹除（structs.py:96-129） | ratint._poly_interval_sign 精确符号、QxStruct 回退清理 |

配套机制：`alg_suspend` 上下文管理器（poly.py:17，solve 参数路径用）、`_rcN` 局部参数符号 + `_radical_bracket` 区间隔离（ratint.py:221）。

**债务形态**：同一代数对象（如 √2）的 minpoly 存在两处（ALG_MODULI 全局 / AN_RELATIONS 作用域）、区间一处、根式出处一处（ALG_RELATIONS），生命周期规则各异（全局永不清理 vs QxStruct 手工弹除）。notes.md 裁定 #1 要求作用域声明取代全局状态。

## 3. M7.0 目标：cas/algfield.py 单一代数对象表示

### 表示契约

```
AlgField(K, m, origin?)   # K[B][α] ≅ K[T]/(m)
  m        : monic 不可约极小多项式，升序系数 list（K 元素，鸭子类型：
             支持 +-*/、is_zero()、与标量 Fr 数乘；Fr/Ga/SymRat/RatFunc 皆可）
  origin?  : α 的原始项形态（√2 类 Power term），出口回化用
  构造校验：monic + 无平方（gcd(m,m')=1）；不可约性按契约由调用方保证
             （ℚ 系数可用 af_irreducible_q 辅助验证，不强制自动跑）

AlgElem(fld, cs)          # cs 升序系数 list，构造即 mod m 约简 + trim 规范形
  + - * neg **int / inv == hash  is_zero  deg
```

### 必备运算（arch §M7.0 清单）

| 运算 | 实现 | 备注 |
|----|----|----|
| minpoly 登记/约简 | 构造时持有 m；乘法出口 u_divmod 取余 | 取代 ALG_MODULI 逐变量余式 |
| 求逆 | univar.u_xgcd mod m | gcd≠单位 → PolyError |
| uexgcd | univar.u_xgcd（K[T] 上） | |
| 迹 Tr(a·β^t) | 牛顿幂和 s_k（K 系数版 tr_power_sums）+ Σaᵢs_{i+t} | algnum.tr_eval 的域推广 |
| 范数 N(a) | Sylvester 行列式 Res_T(m,a)（K 上高斯消元；monic m ⟹ Res=N） | a=0 显式返 0 |
| 结式 | af_res(f,g)：通用 Sylvester det | doubleResultant 的底层件 |
| 出口回化 | to_term：Σ cᵢ·origin^i（系数鸭子 to_term） | 根式形态还原 |

### 分步执行计划（每步全绿提交）

1. **M7.0-a 核心**：algfield.py + tests/test_algfield.py——ℚ(√2)/ℚ(i)(Ga 对拍)/ℚ(∛2)/函数基 K=RatFunc(x)[α], α=√(x²+1) 四切片；(x+α)(x−α)=−1 类恒等式、范数/迹 parity、求逆/幂/回化。
2. **M7.0-b 收口迁移**：QxStruct 投影改写 AlgField 为唯一登记处（作用域对象持 {sym: AlgField}），ALG_MODULI/AN_RELATIONS/AN_INTERVALS 读端改为读它；alg_suspend 退役或降级为兼容垫片。行为零差（现有 AN 测试全绿为准绳）。
3. 之后进 arch §M7.1（z-常数中间层）/ M7.2（RT 残根落域）。

### 正确性锚点（测试即规格）

- N(a+b√2)=a²−2b²；(1+√2)⁻¹ = −1+√2；Tr(√2)=0, Tr(1)=2
- ℚ(i)：与 Ga 算术逐值对拍（norm ↔ Ga.norm 若有）
- ℚ(∛2)：N(α)=2（正根号约定下 Πβⱼ=2），Tr(α²)=s₂=0
- 函数域：(x+α)(x−α) ≡ −1 (α²=x²+1 over ℚ(x))；N(x+α)=Π(x±βⱼ)=…=1（首一验证）
- Res(T²−2, 3−T)=7 手算锚点
