# risch.md — 完整 Risch 所需地基的执行报告

本文件回答一个问题：**为了完成完整 Risch，pyCAS 必须实现哪些地基。**

「地基」的定义是**工具**：可独立实现、可独立测试、被 Risch 消费的可复用模块。Risch 主循环自身内联的逻辑**不算**工具（界分见 §0）。

本文件**不含计划、阶段划分、优先级与顺序裁定**——那些属于 `AGENTS.md` 的节奏纪律与 `progress.md` 的进度职责，不在此处。文件内容只有三样：界分、工具清单、可核对的参考源码路径。

使用时遵守 `reference.md` 的既有纪律：**抄语义不抄代码**；本系统裁定（`cas_v4_arch.md` + `AGENTS.md`）高于参考实现行为。三个参考库自身的缺口如实记录在 §16，不得当作「已实现」引用。

---

## §0 界分：什么算工具，什么不算

**不算工具（属于 Risch 本体，写在 `risch.py` / `math/calculus/integration/risch.py` 一类文件里）：**

- 逐层下降的循环（外层归约完再降到内层）
- 每层三步归约的衔接顺序（微分归约 → 留数 → 多项式部分 → 递降）
- 归约不完备时判定不可积的分支
- 每层该调用哪个求解器、结果如何拼回
- 对数项的合并去重、非初等残余的逐层累积
- 生成元的处理顺序（先用对数层还是先用指数层建塔）

**算工具（必须独立成模块）：** 下列 §1–§14 各项。

---

## §1 因式分解与 gcd

| 工具 | 功能 | 参考路径 |
|---|---|---|
| 一元精确因式分解 | 系数域 ℚ 的多项式拆成不可约因子幂次 | sympy `polys/factortools.py`（`ZZ_ZASSENHAUS`）；FriCAS `algebra/pfbr.spad`、`algebra/twofact.spad`、`algebra/ghensel.spad`；Maxima `factor.lisp` |
| 多元因式分解 | 多变量多项式完全分解 | sympy `polys/factortools.py`；FriCAS `algebra/multfact.spad`、`algebra/allfact.spad`、`algebra/mfinfact.spad`；Maxima `factor.lisp` |
| 多元 gcd | 多变量最大公因式 | sympy `polys/factortools.py`（`ZZ_HEU_GCD`）、`polys/modulargcd.py`、`polys/heuristicgcd.py`；FriCAS `algebra/listgcd.spad`、`algebra/gpgcd.spad`、`algebra/modgcd.spad`、`algebra/amodgcd.spad`；Maxima `spgcd.lisp` |
| 无平方分解 | 拆成两两互素且各自无重因子的部分 | sympy `polys/sqfreetools.py`；FriCAS `algebra/poly.spad`、`algebra/multsqfr.spad`；Maxima `ezgcd.lisp` |
| 部分分式分解 | 按分母互素因子分解成真分式之和 | sympy `polys/partfrac.py`；FriCAS `algebra/pfr.spad`、`algebra/fparfrac.spad`、`algebra/intden.spad`（PartialFractionUtilities）；Maxima `intpol.lisp` |
| 亚结果式链 | 两个一元多项式的结式余子式序列（Ducos 法） | sympy `polys/subresultants_qq_zz.py`、`polys/euclidtools.py`（`DUP_INNER_SUBRESULTANTS`）、`polys/densetools.py`；FriCAS `algebra/prs.spad`、`algebra/intrf.spad`（SubResultantPackage）；Maxima `ezgcd.lisp` |

## §2 结式与根

| 工具 | 功能 | 参考路径 |
|---|---|---|
| 一元结式 | 两个一元多项式的结式 | sympy `polys/euclidtools.py`（`DUP_SUBRESULTANTS`）；FriCAS `algebra/bezout.spad` |
| 多元结式 | 多元多项式结式 | sympy `polys/multivariate_resultants.py`；FriCAS `algebra/charpol.spad`（特征多项式 / 结式族）、`algebra/bezout.spad` |
| 双重结式 | 代数曲线上算留数用 | FriCAS `algebra/intalg.spad`（DoubleResultantPackage）。**sympy 无对应实现** |
| 有理根求解 | 有理系数一元多项式的全部有理根 | sympy `polys/polyroots.py`（`DUP_SQF_LIST` 分支、`ground_roots`）；FriCAS `algebra/rdeefx.spad`（PolynomialRationalRoots / FunctionSpaceRationalRoots） |
| 整数完全幂根 | 整数的平方根 / 完全 n 次幂根，含判定与近似 | FriCAS `algebra/intfact.spad`（IntegerRoots / IntegerPrimesPackage）。**sympy 未定位到独立实现** |
| 代数数根式表示 | 代数数的根式化与最简表示 | sympy `polys/numberfields/minpoly.py`、`polys/domains/algebraicfield.py`（`integral_basis`）；FriCAS `algebra/rsimp.spad`、`algebra/solverad.spad`、`algebra/algext.spad` |

## §3 模算术与提升

| 工具 | 功能 | 参考路径 |
|---|---|---|
| 有限域 | 素域上的域运算 | sympy `polys/galoistools.py`（`GF_GCD`、`GF_FROM_INT_POLY`）、`polys/fields.py`；FriCAS `algebra/ffcat.spad`、`algebra/ffdoms.spad`、`algebra/ffact.spad`、`algebra/fffg.spad` |
| 模 gcd | 模素数下算 gcd | sympy `polys/modulargcd.py`、`polys/factortools.py`；FriCAS `algebra/modgcd.spad`、`algebra/amodgcd.spad` |
| 模因式分解 | 模素数下做完全分解（Berlekamp / 幂等分解 / 周期法） | sympy `polys/factortools.py`；FriCAS `algebra/ffact.spad` |
| 模矩阵与向量 | 素数模下的矩阵与向量 | sympy `polys/matrices/domainmatrix.py`、`polys/matrices/ddm.py`；FriCAS `algebra/u32vec.spad`、`algebra/modring.spad` |
| Hensel 提升 | 从模 p 结果提升到 p^k 或模不同素数 | sympy `polys/factortools.py`；FriCAS `algebra/ghensel.spad`、`algebra/mlift.spad` |
| 向量重构 | 由模结果重建整数 / 有理系数 | sympy `polys/galoistools.py`；FriCAS `algebra/vecrec.spad` |
| 素数处局部化整数环 | 分母不含 p 的有理数构成的欧几里得环 | FriCAS `algebra/intlocp.spad`；Maxima `nummod.lisp` |
| 模 Hermite-Padé | 多元 gcd 的模算法内核 | FriCAS `algebra/modhpsol.spad`；Maxima `spgcd.lisp` |

## §4 数论

| 工具 | 功能 | 参考路径 |
|---|---|---|
| 素性判定 | 概率 / 确定性素性测试 | FriCAS `algebra/intfact.spad`、`algebra/numtheor.spad`；Maxima `numth.lisp`、`ifactor.lisp` |
| 素数枚举 | 前若干素数、下一 / 上一素数 | FriCAS `algebra/intfact.spad`；Maxima `ifactor.lisp` |
| 整数分解 | 分解为素数幂次 | FriCAS `algebra/intfact.spad`；Maxima `ifactor.lisp` |
| 代数数判别式 | 数域判别式（积分基的输入） | sympy `polys/numberfields/modules.py`、`polys/numberfields/basis.py`；FriCAS `algebra/intclos.spad`（NumberFieldIntegralBasis）；Maxima `cpoly.lisp` |

## §5 代数扩张

| 工具 | 功能 | 参考路径 |
|---|---|---|
| 代数数域 | 由最小多项式建立域，元素与坐标双向转换 | sympy `polys/numberfields/minpoly.py`、`polys/domains/algebraicfield.py`；FriCAS `algebra/algext.spad`、`algebra/algcat.spad`；Maxima `algfac.lisp`、`nalgfa.lisp`、`rat3a.lisp` |
| 代数数域上的因式分解 | 系数取在代数数域上的因式分解 | sympy `polys/factortools.py`；FriCAS `algebra/algfact.spad`、`algebra/ratfact.spad`、`algebra/fdalg.spad` |
| 积分基 | 数域与一元函数域的整环基、局部基 | sympy `polys/numberfields/modules.py`、`polys/numberfields/subfield.py`；FriCAS `algebra/intclos.spad`（NumberFieldIntegralBasis / FunctionFieldIntegralBasis / WildFunctionFieldIntegralBasis）；Maxima `cpoly.lisp` |
| 积分基支撑工具 | 模 Hermite 行归约、无分数三角逆、理想化子与理想化子矩阵、矩阵最大公因子 | sympy `polys/matrices/normalforms.py`、`polys/matrices/lll.py`；FriCAS `algebra/divisor.spad`、`algebra/intclos.spad`（TriangularMatrixOperations / IntegralBasisTools） |
| 亏格 0 有理化换元 | 三类亏格 0 曲线的有理化代换（`y²=二次`、`y²=有理`、关于主变量一次） | FriCAS `algebra/intaf.spad`（GenusZeroIntegration）。**sympy 无对应实现** |
| 代数函数域算术 | 曲线上的点、加乘、约化、极点判定 | sympy `polys/fields.py`；FriCAS `algebra/curve.spad`（AlgebraicFunctionField / RadicalFunctionField / ChangeOfVariable） |
| 代数核规范化 | 嵌套根归一为「单根 + 首一最小多项式」标准形 | sympy `polys/polytools.py`、`simplify/simplify.py`；FriCAS `algebra/manip.spad`（AlgebraicManipulations）；Maxima `sqrtdenest.lisp`、`rpart.lisp` |
| 代数根的基域拆分 | 在基域上拆分代数根（Risch 代数层的入口） | FriCAS `algebra/intpar.spad`（RootFSSplit）；Maxima `polyrz.lisp` |

## §6 线性代数

| 工具 | 功能 | 参考路径 |
|---|---|---|
| 有理矩阵求解 | 线性方程组、行阶梯、秩、核、行列式 | sympy `polys/matrices/rref.py`、`polys/matrices/domainmatrix.py`；FriCAS `algebra/matfuns.spad` |
| 整数 Hermite / Smith 正规形 | 整数矩阵的行 / 列等价标准形 | sympy `polys/matrices/normalforms.py`（`smith_normal_decomp`）、`polys/matrices/lll.py`；FriCAS `algebra/smith.spad`、`algebra/smith2.spad` |
| 无分数三角矩阵求逆 | 给定分母 d，返回 `d·B⁻¹` 而不进分式域 | FriCAS `algebra/intclos.spad`（TriangularMatrixOperations）。**sympy 无对应实现** |
| 常数域线性相关 | 判定一组元素在常数域上线性相关 | sympy `integrals/rde.py`、`integrals/risch.py`；FriCAS `algebra/rdeefx.spad`（ConstantLinearDependence）、`algebra/lindep.spad` |
| 线性相关提升 | 把常数域上的相关提升到一元多项式、有理函数、矩阵 | sympy `integrals/rde.py`；FriCAS `algebra/rdeefx.spad`（LiftLinearDependence） |
| 常数域线性方程组 | 特解、零空间、约化系统 | sympy `integrals/rde.py`；FriCAS `algebra/rdeefx.spad`（ConstantLinearDependence）；Maxima `cpoly.lisp` |
| 整数线性相关 | 整数列的线性相关与界 | FriCAS `algebra/lindep.spad`、`algebra/intden.spad` |

## §7 级数与渐近

| 工具 | 功能 | 参考路径 |
|---|---|---|
| 形式幂级数 | 环运算、截断、复合 | sympy `series/formal.py`、`series/series_class.py`；FriCAS `algebra/genser.spad` |
| 泰勒级数运算 | 展开、截断、系数提取 | sympy `series/series.py`、`series/series_class.py`；FriCAS `algebra/taylor.spad`、`algebra/sttaylor.spad` |
| Laurent 级数 | 负指数允许的级数 | sympy `series/formal.py`（Laurent 部分）、`polys/ring_series.py`；FriCAS `algebra/laurent.spad` |
| Puiseux 级数 | 分数指数级数 | sympy `series/formal.py`（`FPuiseuxSeries`）、`polys/puiseux.py`；FriCAS `algebra/puiseux.spad` |
| 级数上的初等函数 | exp / log / 三角 / 双曲在级数上运算，失败时明确返回不可算 | sympy `series/series_class.py`、`functions/elementary/exponential.py`；FriCAS `algebra/efullys.spad`（Laurent 域初等函数，26 个，含返回 `failed` 的 partial 版本）、`algebra/efupxs.spad` |
| 点处阶与无穷远阶 | 元素的消失阶 / 增长阶 | sympy `series/order.py`；FriCAS `algebra/expexpan.spad`（ExponentialOfUnivariatePuiseuxSeries 的序关系）、`algebra/limitps.spad` |
| 渐近展开 | 极限与渐近分析 | sympy `series/gruntz.py`、`series/limits.py`；FriCAS `algebra/limitps.spad`、`algebra/lodof.spad`；Maxima `tlimit.lisp`、`limit.lisp` |
| 留数（级数意义） | 函数在某点的留数提取 | sympy `series/residues.py`；FriCAS `algebra/intalg.spad` |

## §8 实代数

| 工具 | 功能 | 参考路径 |
|---|---|---|
| 实根隔离 | 隔离实根，给出根的个数与位置 | sympy `polys/rootisolation.py`、`polys/rootoftools.py`；FriCAS `algebra/realzero.spad`、`algebra/reclos.spad`、`algebra/cyldec.spad` |
| 实代数数算术 | 精确表示实代数数并判零 | sympy `polys/rootoftools.py`、`polys/domains/algebraicfield.py`；FriCAS `algebra/reclos.spad` |
| 区间上的符号判定 | 判定函数在区间内处处正 / 负 / 变号 | sympy `calculus/util.py`、`integrals/defintef.py` 的判定栈；FriCAS `algebra/limitps.spad`（ElementaryFunctionSign）、`algebra/sign.spad` |
| 区间算术 | 区间上的加乘与包含关系 | sympy `sets/sets.py`（Interval）、`plotting/intervalmath/interval_arithmetic.py`；FriCAS `algebra/interval.spad`、`algebra/ainterval.spad` |
| 实闭域 | 完备的实代数判定结构 | sympy `polys/domains/algebraicfield.py`（实代数数域）；FriCAS `algebra/reclos.spad` |

## §9 表达式改写

| 工具 | 功能 | 参考路径 |
|---|---|---|
| 三角 ↔ 指数 / 对数互转 | 正向与反向改写 | sympy `functions/elementary/trigonometric.py`（对 exp 的 rewrite）、`simplify/trigsimp.py`；FriCAS `algebra/efstruc.spad`（TrigonometricManipulations 系列）；Maxima `trmode.lisp`、`halfangle.lisp`、`trigo.lisp` |
| 实虚部拆分 | 复表达式拆成实部与虚部 | sympy `functions/elementary/complexes.py`；FriCAS `algebra/efstruc.spad`（ComplexTrigonometricManipulations）；Maxima `conjugate.lisp`、`rpart.lisp` |
| 指数 / 对数展开合并 | 恒等展开（同类项收集、幂展开、对数拆分） | sympy `simplify/powsimp.py`、`simplify/simplify.py`、`functions/elementary/exponential.py`；FriCAS `algebra/manip.spad`（TranscendentalManipulations，28 个）、`algebra/elemntry.spad`；Maxima `csimp.lisp`、`simp.lisp` |
| 三角恒等变形 | 半角、和差积、齐次化 | sympy `simplify/fu.py`（TR 系列）、`simplify/trigsimp.py`；FriCAS `algebra/efstruc.spad`（TangentExpansions）；Maxima `trmode.lisp` |
| 表达式 ↔ 塔表示 | 双向转换：原表达式与逐层生成元表示互转 | sympy `integrals/risch.py`（`DifferentialExtension` 的回代表）；FriCAS `algebra/polycat.spad`、`algebra/expr.spad` |
| 塔上求导 | 在塔表示上求导并给回分子 / 分母 | sympy `integrals/risch.py`（求导作用在有理函数上的公式）；FriCAS `algebra/dpolcat.spad`（微分多项式）、`algebra/curve.spad` |
| 常数提取 | 提取与积分变量无关的常数因子 | sympy `integrals/risch.py`（从指数中提出常数）；FriCAS `algebra/intaux.spad`（removeConstantTerm） |

## §10 生成元与结构分析

| 工具 | 功能 | 参考路径 |
|---|---|---|
| 塔构造与维护 | 逐层加入生成元、维护各层求导映射与回代表 | sympy `integrals/risch.py`（`DifferentialExtension`）；FriCAS `algebra/intaux.spad`（IntegrationTools：选核、按高度排序、取次核） |
| 生成元分类器 | 判定一个求导属于「有理 / 对数 / 指数 / 正切 / 其他」 | sympy `integrals/risch.py`（按求导的有理式形态分类）；FriCAS `algebra/intaux.spad` 的高度序 + `algebra/efstruc.spad` |
| 结构定理判定 | 判定一组初等函数在常数域上代数无关（实版与复版） | FriCAS `algebra/efstruc.spad`（ElementaryFunctionStructurePackage）。**sympy 无对应实现** |
| 指数合法性判定 | 指数代数性、与已有生成元的代数相关、隐藏常数检测、阶乘次序检测 | FriCAS `algebra/efstruc.spad`；sympy `integrals/risch.py`（仅部分：检查指数是否为有理函数、是否与已有 log 冲突） |
| 常数域识别 | 判定哪些生成元求导为零 | sympy `integrals/risch.py`、`integrals/rde.py`（常数判据写在求导闭包上）；FriCAS `algebra/rdeefx.spad`、`algebra/efstruc.spad` |
| 生成元的乘法依赖 | 判定生成元之间的乘法依赖 | FriCAS `algebra/muldep.spad`；Maxima `ezgcd.lisp` |

## §11 超越指数

| 工具 | 功能 | 参考路径 |
|---|---|---|
| 超越指数分解 | 把元素拆成 `θ(x)·e^{ω(x)}` 的和，判定 `ω` 是否有理 | sympy `series/aseries.py`（超越级数指数）、`integrals/risch.py` 的指数层入口；FriCAS `algebra/expexpan.spad`、`algebra/fs2expxp.spad`；Maxima `exintegral.lisp` |
| 超越指数积分 | 已知 `ω` 有理时求解 | sympy `integrals/risch.py`（超越指数多项式求解 + 超越指数积分）；FriCAS `algebra/expexpan.spad`、`algebra/rdeefx.spad`（指数积分部分） |
| 超越级数指数 | 形如 `Σ gᵢ·exp(fᵢ)` 的表示与运算 | sympy `series/aseries.py`；FriCAS `algebra/expexpan.spad`（UnivariatePuiseuxSeriesWithExponentialSingularity） |

## §12 微分归约

| 工具 | 功能 | 参考路径 |
|---|---|---|
| 分裂分解 | 拆成「与自身导数互素的部分（normal）」与「special 部分」，识别 special | sympy `integrals/risch.py`（分裂分解与分裂无平方分解）；FriCAS `algebra/intrf.spad`（MonomialExtensionTools：split / splitSquarefree / normalDenom / decompose） |
| 微分 Hermite 归约 | `f = g' + r`，`r` 只有简单极点（有理 / 单项式扩张 / 代数 / 混合各情形的参数化版本） | sympy `integrals/risch.py`（微分归约）、`integrals/rationaltools.py`（有理情形）；FriCAS `algebra/intrf.spad`（RationalIntegration / TranscendentalHermiteIntegration）、`algebra/intalg.spad`（AlgebraicHermiteIntegration） |
| 留数提取 | Trager / Lazard-Rioboo 结式归约，给出对数部分与「余项是否在基域」的判定 | sympy `integrals/risch.py`（留数归约）、`integrals/rationaltools.py`（对数部分、实虚部拆反正切）；FriCAS `algebra/intden.spad`（DenominatorIntegration：li_int / poly_int / solve_u）、`algebra/intrf.spad`（SubResultantPackage） |
| 对数部分最简化 | 合并重复对数、代数系数最简表示 | sympy `integrals/rationaltools.py`（log_to_atan / log_to_real）；FriCAS `algebra/intden.spad`、`algebra/rdeefx.spad`（有理根最简） |
| 导数识别 | 判定某元素是否为某元素的导数 | sympy `integrals/risch.py`（导数识别）；FriCAS `algebra/rdeefx.spad`（rationale roots / FunctionSpaceRationalRoots 配套）、`algebra/intden.spad`（solve_u） |
| 对数导数识别 | 判定某元素是否为 `Σ cᵢ·uᵢ'/uᵢ` | sympy `integrals/risch.py`（对数导数识别）、`integrals/rde.py`；FriCAS `algebra/rdeefx.spad`（liftLinearDependence）、`algebra/intpar.spad`（参数化对数导数） |
| 亏格与特殊点 | 识别曲线的亏格、有限阶点 | sympy `polys/rootoftools.py`（曲线亏格）；FriCAS `algebra/intalg.spad`（PointsOfFiniteOrder）、`algebra/curve.spad` |

## §13 求解器

| 工具 | 功能 | 参考路径 |
|---|---|---|
| 有理函数积分器 | 基例完整积分器 | sympy `integrals/rationaltools.py`、`integrals/intpoly.py`；FriCAS `algebra/intrf.spad`（RationalFunctionIntegration）；Maxima `intpol.lisp`、`irinte.lisp` |
| 微分方程求解器 | 解 `a·y' + b·y = c`，按指数 / 正切 / 对数三情形；无解时明确返回不可积 | sympy `integrals/rde.py`；FriCAS `algebra/rdeefx.spad`（ElementaryRischDEX2 / ElementaryRischDEX）、`algebra/intpar.spad`（ParametricRischDE） |
| 微分方程度数界 | 给出解的次数上界（参数化与非参数化共用同一套，只差右端是单个还是一组） | sympy `integrals/rde.py`（bound_degree，参数化与非参数化唯一差别在右端）；FriCAS `algebra/intpar.spad`（exp_lower_bound） |
| 特殊分母消去 | 分母次数偏大 / 偏小 / 与之相等三情形 | sympy `integrals/rde.py`（三组 no_cancel 与两组 cancel）；FriCAS `algebra/rdeefx.spad` |
| 参数化微分方程求解器 | 右端为未知常数的线性组合时求解 | sympy `integrals/prde.py`（param_poly_rischDE / param_rischDE）；FriCAS `algebra/intpar.spad`（ParametricRischDE / RDEaux） |
| 受限积分 | 解 `∫f' + c·g` 型方程 | sympy `integrals/prde.py`（limited_integrate）、`integrals/risch.py`（扩展积分入口）；FriCAS `algebra/intpar.spad`（extendedint / limitedlogs） |
| 参数化对数导数求值 | 对数导数在参数下的求值 | sympy `integrals/prde.py`（parametric_log_deriv）；FriCAS `algebra/intpar.spad`（logextint / monologextint） |
| 一阶线性 ODE（留数侧） | 代数积分中留数为线性 ODE 时的求解 | FriCAS `algebra/oderf.spad`（RationalLODE / ConstantLODE / PrimitiveRatDE）；sympy 无对应实现 |
| 椭圆积分识别 | 识别并生成椭圆积分结果 | sympy `integrals/meijerint.py`（广义路径）；FriCAS `algebra/intspec.spad`（GenerateEllipticIntegrals） |
| 模式匹配的文献积分 | 用模式表匹配文献中的特殊函数积分 | FriCAS `algebra/intpm.spad`（PatternMatchIntegration）；sympy `integrals/manualintegrate.py`；Maxima `hypergeometric.lisp` |
| 启发式兜底 | 猜原函数（非判定通道，不得冒充结论） | sympy `integrals/heurisch.py`；Maxima `sinint.lisp`、`grind.lisp` |

## §14 结果、证书与定积分

| 工具 | 功能 | 参考路径 |
|---|---|---|
| 三段式结果类型 | 初等部分 / 带代数系数的对数部分 / 非初等残余 | sympy `integrals/risch.py`（结果的三元返回与对数部分表示）；FriCAS `algebra/intaux.spad`（IntegrationResult：ratpart / logpart / notelem）；REDUCE `packages/camal/camal.rlg`（CAMAL 闭式数学语言：把积分结果放进独立表示体系） |
| 非初等残余容器 | 显式承载「已证不可积」的残余，并能逐层累积 | sympy `integrals/risch.py`（NonElementaryIntegral：保证非初等）；FriCAS `algebra/intef.spad`（unknownint 把不可积项放进 notelem） |
| 正向验证器 | 独立复核「原函数求导 = 被积函数」 | pyCAS 已有：`cas/math/calculus/integration/verify.py`；参考侧无对等物（参考实现把校验隐含在算法里） |
| 否定证书构造 | 为「不可积」产出可机械复核的见证 | **参考实现均无**：sympy 只保证「残余非初等」这一事实，不产出可复核证书；FriCAS 同 |
| 未决与拒答通道 | 能力缺失、参考未覆盖的情形显式未决 | sympy `integrals/risch.py`（多处 `NotImplementedError` 与 `NonElementaryIntegralException`）；FriCAS 相应处用 `error "..."` 或返回 `failed` |
| 定积分：零点与极点检测 | 区间内是否为零点 / 极点（潜在极点） | sympy `integrals/rationaltools.py`；FriCAS `algebra/defintef.spad`（checkFor0 / checkForPole / checkSMP） |
| 定积分：收敛性判定 | 判定被积函数在区间上可积 | sympy `integrals/transforms.py`；FriCAS `algebra/defintef.spad`、`algebra/defintrf.spad`（DefiniteIntegrationTools / RationalFunctionDefiniteIntegration）；Maxima `defint.lisp` |
| 定积分：数值核验 | 反常积分的收敛加速与数值校验 | sympy `integrals/quadrature.py`；Maxima `defint.lisp` |

---

## §15 参考源码位置

| 库 | 版本 / 位置 | 说明 |
|---|---|---|
| **sympy** | 1.14.0，`D:\Python\Python312\Lib\site-packages\sympy` | Python；Risch 三件套 `integrals/risch.py`（67,352 B）、`integrals/rde.py`（27,393 B）、`integrals/prde.py`（52,073 B），合计 146,818 B |
| **FriCAS** | `D:\code\python\CAS\fricas`，核心在 `src\algebra`（356 个 `.spad`） | Spad；Risch 家族 16 个文件 438,594 B、50 个包：`intef/intaux/integrat/defintef/defintrf/intrf/intden/intaf/intalg/intpar/rdeefx/intclos/intfact/intlocp/intpm/intspec.spad` |
| **Maxima** | `D:\code\python\CAS\maxima`，核心在 `src` | Common Lisp；`risch.lisp`（49,194 B）、`defint.lisp`（140,251 B）、`factor.lisp`、`spgcd.lisp`、`ezgcd.lisp`、`cpoly.lisp`、`algfac.lisp`、`nalgfa.lisp`、`ifactor.lisp`、`numth.lisp`、`nummod.lisp`、`series.lisp`、`tlimit.lisp`、`limit.lisp`、`exintegral.lisp`、`hypergeometric.lisp`、`sinint.lisp`、`trmode.lisp`、`trigo.lisp`、`halfangle.lisp`、`polyrz.lisp`、`rpart.lisp`、`intpol.lisp`、`irinte.lisp` |
| **REDUCE** | `D:\code\python\CAS\reduce-algebra`，包在 `packages/` | Common Lisp（REDUCE / PSL）；**不是 Risch 算法权威**，只在两处有参考价值：结果表示 `packages/camal/camal.rlg`（37,835 B，CAMAL 闭式数学语言）、行为语料 `packages/algint/algint.rlg`（84,224 B）+ `packages/int/int.rlg`（80,077 B）。另有 `packages/invbase`（不变量基）、`packages/atensor`（微分形式）与目标 1 相关 |

**体量对照（说明覆盖范围的差异）**：sympy 的 Risch 三件套覆盖 FriCAS 家族中的**超越部分**（对应对数塔、指数塔、留数、微分方程、参数化）；FriCAS 家族多出的约 106 KB 几乎全是**代数部分**（`intaf.spad` 38,464 B + `intalg.spad` 31,937 B + `intclos.spad` 35,836 B），sympy 无对应实现。

---

## §16 参考实现自身的缺口（如实记录，不得当作已实现）

### sympy 1.14.0

| 缺口 | 位置 |
|---|---|
| 代数扩张不支持（有理指数幂） | `integrals/risch.py` |
| 实三角不支持，须先改写为复指数 | `integrals/risch.py` |
| 找不到新的初等扩张时拒答 | `integrals/risch.py` |
| 指数层「无法在其上积分」时拒答 | `integrals/risch.py`（`_exp_part`） |
| 非线性 / 线性「其他」生成元：顶层分派只处理有理层、对数层、指数层三类，其余直接 `NotImplementedError("Only exponential and logarithmic extensions are currently supported.")` | `integrals/risch.py` |
| 参数化微分方程：等号情形未实现 | `integrals/prde.py` |
| 参数化微分方程：线性与 hypertangent 组合未实现 | `integrals/prde.py` |
| 参数化结构定理的**实版本**未实现 | `integrals/prde.py`（两处） |
| 参数化微分方程：非初等扩张不支持 | `integrals/prde.py`（两处） |
| 参数化微分方程：不能处理非有理生成元 | `integrals/prde.py`（两处） |
| 参数化微分方程：hypertangent 情形部分未实现 | `integrals/prde.py` |
| 域内导数判定函数缺失（代码中该处被注释） | `integrals/rde.py`（两处） |

### FriCAS

| 缺口 | 位置 |
|---|---|
| 代数函数积分未完成：常数留数、无理留数、留数多项式含多个非线性因子、含多项式部分、迹为零——五类均直接报错 | `algebra/intalg.spad`（5 处 `error "integrate: implementation incomplete"`） |
| 参数化 Risch 微分方程：仅实现最简单的代数情形，其余报错 | `algebra/intpar.spad` |
| 参数化代数积分：若干情形未实现 | `algebra/intpar.spad`（3 处 `unimplemented`） |
| Expression 上的因式分解未实现 | `algebra/intpar.spad`（`factorPolynomial unimplemented`） |
| LambertW 的扩展积分是 FIXME | `algebra/intef.spad` |
| 全库无超越指数积分层 | 大小写不敏感检索 `hyperexp` 于 `src/algebra` 与 `src/interp` 零命中 |
| 全库无超几何积分层 | `hypergeometricF` 仅为函数对象，非积分算法 |

### REDUCE

| 缺口 | 位置 |
|---|---|
| **`algint` 与 `int` 不是积分算法，是测试集** | 两个文件头均为「THE REDUCE INTEGRATION TEST PACKAGE」，内容是 Gradshteyn–Ryzhik 风格的初等积分行为语料；Reduce 的 Liouville 级积分在其核内，不在这两个包里。**不得把它们当作 Risch 实现引用** |
| Liouville 级积分在核内，源码不在 `packages/` | 查语义应转向 `src/`（REDUCE / PSL 核），而非 `packages/algint`、`packages/int` |
| 无超越指数、无超几何积分层 | 与 FriCAS 同；`packages/specfn` 只提供特殊函数表 |

### 共同空白

- **可机械复核的「不可积」证书**：四者都只保证「残余非初等」这一事实，不产出可由独立验证器复核的见证。pyCAS 按 `cas_v4_arch.md` §7.3「求解器与 checker 分家」需要自建 §14 的「否定证书构造」。
- **代数扩张层的完整 Risch**：sympy 完全不做；FriCAS 做了一半且在关键留数情形报错。

---

## §17 与本文件边界相邻的问题（尚未裁定，本文件不代为决定）

- 代数曲线上的留数（双重结式）与 §2 的留数难子情形，是否纳入「完整 Risch」的范围。
- 超越指数层：只做「识别与判定不可积」，还是也做「积分」。
- 定积分与反常积分是否属于目标 1 的范围，还是另立目标。
- 非线性 / 线性「其他」生成元（如 `x^x` 型）是否需要判定能力，还是明确拒答。

以上四项在裁定前，`progress.md` 不得把它们记为已实现，`cas_v4_arch.md` §十一 第六阶段不得把它们记为已规划。
