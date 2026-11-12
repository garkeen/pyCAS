# reference.md — 参考实现索引

本项目（pyCAS/）的算法与架构参考源码位于**同级目录** `D:\code\python\CAS\`：`maxima/`、`fricas/`、`expreduce/`、`mathics-core/`、`yacas/`、`reduce-algebra/`、`SAINT/` 均与 `pyCAS/` 平级。**主要权威参考：Maxima 与 FriCAS**。查算法语义、判定流程、边界行为时，先读这两个；其余五个为次要参照。

裁定优先级：**本系统裁定（`cas_v5_arch.md` + `AGENTS.md`）高于参考实现行为**。参考实现里与本系统裁定冲突的做法（如 L0 隐式折叠、数值采样判等），一律以本系统裁定为准。

2026-10-28 说明：以下原始参考路径与消化记录完整保留，其中“落地位置”“已消费”等属于早期实现快照，不表示当前 v5 状态；已完成记录看 `progress.log`，路线看 `roadmap.md`，当前进度与已知缺陷看 `AGENTS.md`。参考能力判断必须由实际源码及算法前提支持，不能用文件大小、关键词零命中或只读测试日志代替。完整目标/依赖见架构 §30，取证结论不用于缩减目标。

## 主要参考

### maxima/ — Maxima（Common Lisp，Macsyma 血统）

完整发行版源码树。核心算法集中在 `maxima/src/*.lisp`：

| 文件 | 内容 | 落地位置 |
|---|---|---|
| `src/risch.lisp` | Risch 指数-对数积分主循环 | 未建；目标 `math/calculus/integration/`（v4 §十一 第六阶段） |
| `src/sinint.lisp`, `src/sin.lisp` | 三角函数换元积分 | 未建；同上积分层 |
| `src/defint.lisp` | 定积分入口与分派 | `math/integrate.py`（多项式片段已建） |
| `src/limit.lisp` | 极限计算 | 未建（极限/级数） |
| `src/factor.lisp` | 多项式因子分解 | `math/domains/polytools.py`（结式、无平方已建；Zassenhaus 未建） |
| `src/csimp.lisp`, `csimp2.lisp` | 化简主循环 | `math/simplify.py`、`math/qarith.py` |
| `src/rat3a.lisp`（940 行起「ALGEBRAIC NUMBERS」节） | CRE 代数量：TELLRAT/$ALGEBRAIC 挂核；`rainv` 模极小多项式扩展欧几里得求逆（bprog）；`leadalgcoef`/`algnormal`/`algcontent` 规范化三件套 | `math/domains/qi.py`（ℚ(i) 成员通道已消费）；ℚ(α) 通用化预留 |

会话与求值骨架在 `src/suprv1.lisp`。

### fricas/ — FriCAS（Scratchpad II 血统，Spad 语言）

代数库按数学范畴分层，全部在 `fricas/src/algebra/*.spad`：

| 文件 | 内容 | 落地位置 |
|---|---|---|
| `algebra/poly.spad`, `polycat.spad`, `multpoly.spad` | 多项式范畴与域 | `math/domains/poly.py` |
| `algebra/gdpoly.spad` | ℚ 上 GCD/Hensel 型分解 | `math/domains/polytools.py`（多变量 GCD 未建） |
| `algebra/gaussian.spad` | ComplexCategory/Complex(R)：ℚ(i) = MonogenicAlgebra(R, x²+1)，Rep 为 (real, imag) 对 | `math/domains/qi.py`（已消费） |
| `algebra/algext.spad` | SimpleAlgebraicExtension：Rep := UP（元素即模极小多项式约简后的多项式），basis/coordinates 坐标转换 | 未建（ℚ(α) 通用化预留） |
| `algebra/gaussfac.spad` | ℤ[i] 高斯整数因式分解 | `math/domains/z.py`（ℤ[i] 欧几里得结构预留） |
| `algebra/intef.spad`, `defintef.spad` | 初等函数 Risch 积分（EF 体系） | 未建；目标积分层 |
| `algebra/rdeefx.spad`, `grdef.spad` | RDE 求解器族 | 未建（Risch 组件） |
| `algebra/intalg.spad` | 代数数/代数函数域上的积分 | 未建 |
| `algebra/expexpan.spad` | 指数塔展开 | 未建（微分塔） |
| `algebra/limitps.spad`, `mrv_limit.spad` | 极限（级数法/MRV） | 未建 |
| `algebra/sum.spad` | 级数求和 | 未建 |

FriCAS 的**域参数化体系**（Category → Domain → Package）是本系统数域投影设计（v4 §7.6 域系统）的直接原型。

## 使用纪律

1. **抄语义不抄代码**：对照判定顺序、结构能力和分支条件，不照搬历史数据结构；本系统的项身份按完整结构而非驻留地址。
2. **先本系统裁定后参考**：`cas_v5_arch.md` 与 `AGENTS.md` 的裁定优先；参考实现只是算法与行为证据来源。
3. **边界行为取证**：遇到「这个积分该不该出条件解」类问题时，检查实际算法、前提和相应行为；一次参考输出不能独立证明一般数学结论。

## 已消化经验（按主题，持续积累）

实现前先读源码，消化后的结论记在这里——写明出处与落地位置，防止重 derive。

### ℚ(i) 高斯域（落地：`cas/math/domains/qi.py`）

- **ℚ(i) 就是商环 ℚ[z]/(z²+1)**：FriCAS `gaussian.spad` 的 ComplexCategory 直接 Join MonogenicAlgebra(R, x²+1)——复数不是特例结构，是单生成代数在 minpoly=x²+1 的实例。本系统落地：成员通道 = 闭项中 i↦z → ℚ(z) 有理函数 → 模 z²+1 约化（复用既有 rf 机器，Maxima `rat3a.lisp` 的代数量模式）
- **元素表示双形态，语义同一**：FriCAS Complex(R) 用 Record(real, imag) 对偶标准形（乘法直接对偶运算，省函数调用）；通用 SimpleAlgebraicExtension 用 Rep := UP（模 minpoly 多项式）。两者都是标准形 ⟹ 判等即结构判等。本系统落地：ℚ(i) 取对偶形（d=2 最简），ℚ(α) 通用化时取多项式形
- **除法 = 共轭×范数**（FriCAS 同式）：a/b = a·conj(b)/norm(b)；Maxima 的 `rainv` 是模 minpoly 扩展欧几里得——d=2 时两者是同一件事的两个写法。分母不可逆 ⟺ 除零 ⟺ 非成员（x²+1 不可约 ⟹ 非零元恒可逆，这正是成域的原因）
- **能力按声明分派，前提由声明承担**：FriCAS `if R has Field then Field` 旁注明 "this is a lie; we must know that x^2+1 is irreducible in R"——不可约性是构造前提，不运行时验证。EuclideanDomain 仅当 R 有 IntegerNumberSystem（ℤ[i] 才欧几里得）。**全文件无 OrderedRing**——复数域无序是范畴级裁定。本系统落地：is_field=True / is_euclidean=False / is_ordered=False 三个能力字段全部照此
- **i 常数的身份注入**：常数声明在 `math/elementary/declarations.dsl`，域包纪律是只依赖 `cas.syntax.term`；本系统在装配期接线（`math/domains/module.py` 经 builder 取 i 原子构造 `QIDomain`），不做名字嗅探

## 次要参照（同目录下另有）

- **expreduce/** — Common Lisp 规则重写 CAS，规则组织方式可参照
- **mathics-core/** — Mathematica 语法的 Python 实现，语法兼容层参照
- **yacas/** — C++ 轻量 CAS，工程结构参照
- **reduce-algebra/** — REDUCE（Common Lisp）。**目标 3（CAD）的语义权威**：`packages/redlog/ofsf/ofsfcad.red`（CAD 主循环）、`ofsfqe.red`（量词消去）、`ofsfdpep.red`（区间隔离与符号判定）、`ofsfexfr.red`（代数扩张）、`ofsfgs.red` + `ofsftfc.red`（符号不变性），作者 Dolzmann / Seidl / Sturm / Kosta。另有 `packages/cgb/`（Comprehensive Gröbner Bases，参数化 GB）、`packages/f5/`、`packages/roots/`（Kameny 根求解）、`packages/wu/`（Wu 特征集法）、`packages/odesolve/zimmer.rlg`（Zimmermann / Rosenlicht 法 ODE）、`packages/crack/`（积分因子与精确方程）、`packages/sum/` + `zeilberg`（Zeilberger 创造性望远镜）、`packages/regressions/`（259 个真实缺陷的回归钉子）。注意：目录中的 `.rlg` 是测试日志，不代表该目录只有测试。本地 `packages/algint/algint.red:1` 是代数积分包入口，`abasic.red:1` 是基础算法模块；此前“algint/int 整个目录只是测试集”的断言错误，不能据此排除其算法参考价值。
- **SAINT/** — Macsyma 前身，历史价值

## 2026-10-28 数学边界与源码核对

- FriCAS 本地 `src/algebra/intalg.spad:134–147` 定义 AlgebraicIntegrate；163–168 行有明确未完成分支；178–181 行依赖除子、有限阶点和代数 Hermite，224–237 行实际消费整基。它并非没有代数分支，也不能因有入口就声称完整；这些依赖已进入架构的代数函数积分路线。
- `src/algebra/intef.spad` 的 primitive/exponential 积分调用是后续取证入口，不由 hyperexp 关键词是否出现推断整个库能力。
- Richardson 的函数恒等不可判定结果须保留具体表达式语言，不能直接外推为所有闭合超越常数判零不可判定。[原论文入口](https://www.jstor.org/stable/2271358)；[Constant Problem](https://mathworld.wolfram.com/ConstantProblem.html)。
- 实指数域的 Schanuel 条件结果不等于无条件可判定：[Wilkie 说明](https://link.springer.com/chapter/10.1007/978-94-015-8923-9_11)；[2026 年相关预印本引言](https://arxiv.org/html/2603.08365v1)仍说明开放性。
- 上述取证只支持准确的能力/理论边界，不作为删除代数积分、参数分类或完整交互目标的理由。

## 2026-11-05 W1 代数与积分参考

以下条目只记录参考依据与实现落点，不表示契约闭合；当前缺口见 `AGENTS.md` §5.3。

- **伪除法 / 结式 / 判别式**：Knuth, *The Art of Computer Programming*, vol. 2, §4.6.1（多项式除法与伪除法）；Geddes, Czapor, Labahn, *Algorithms for Computer Algebra*, §2.3（伪除法）与 §7（结式、子结式）。参考实现：Maxima `src/rat3c.lisp:268-287`（`psquorem1`/`prem`）、`src/result.lisp:95-144`（Brown 子结式 PRS resultant）；FriCAS `src/algebra/prs.spad`（`PseudoRemainderSequence`）。实现落点：`cas/algebra/polynomial.py` 的 `pseudo_divmod`、`resultant`、`discriminant`。
- **扩展欧几里得**：标准 Euclid/Bezout 递推；Geddes 等 §2.2。实现落点：`cas/algebra/protocols.py` 的 `Euclidean.xgcd` 与 `cas/algebra/polynomial.py` 的 monic 归一。
- **子结式 PRS 链**：Brown, "The Subresultant PRS Algorithm", TOMS 4(3), 1978；Cohen, *A Course in Computational Algebraic Number Theory*, Algorithm 3.3.7。参考实现：Maxima `src/result.lisp:95-144` 与 `src/rat3c.lisp:252-264`（`subresgcd`）；FriCAS `src/algebra/prs.spad:699-721`（`chainSubResultants`）。实现落点：`UnivariatePolynomialRing.subresultant_chain`，当前是特征零域上的 PRS 版本。
- **平方自由分解**：Yun (1976), "On square-free decomposition algorithms"；Geddes 等 §8.2。实现落点：`UnivariatePolynomialRing.squarefree_part`/`squarefree_decomposition`。正特征需要独立的 Frobenius 路线，当前诚实拒绝。
- **有理 Hermite 归约**：Bronstein, *Symbolic Integration I*, §4.4；Geddes 等 §11.2。参考实现：FriCAS `src/algebra/intrf.spad:208-276`（`TranscendentalHermiteIntegration` 的 `normalHermiteIntegrate`）。实现落点：`cas/algebra/hermite.py`，输出 `f = D(v) + r` 且 `r` 的分母平方自由；本项目采用逐因子重复归约，契约与 FriCAS 的并行归约相同。
- **域上线性代数**：Gauss–Jordan 消元 / RREF；Cohen, *A Course in Computational Algebraic Number Theory*, §2.2。实现落点：`cas/algebra/linear.py`，一次消元同时提供秩、特解、零空间和不相容行组合见证。
- **整数矩阵与分式自由消元**：Bareiss, "Sylvester's identity and multistep integer-preserving Gaussian elimination", *Math. Comp.* 22 (1968)；Cohen, §2.2.6（Bareiss 行列式）与 §2.4.2/§2.4.3（Hermite/Smith 标准形）。参考实现：FriCAS `src/algebra/smith.spad`、`src/algebra/smith2.spad`（`SmithNormalForm`/`IntegerSmithNormalForm`）。实现落点：`cas/algebra/integer_matrix.py`，返回 `U*A=H` 与 `U*A*V=D` 的实际幺模变换。
- **参数化基域**：架构 §8.0 的 `K[A]`/`K(A)` 构造；实现落点：`runtime/bootstrap.py` 的 `bootstrap_parameterized_over`，基域、`embed_rational`、`render_base` 均为显式参数。
- **函数值与工作流状态**：架构 §10.1–§10.2（固有定义域、表示区域、`EqualOn`/`SamePartialFunction`）与 §17–§18（Task/Candidate/ObjectVersion、执行尝试/取消、revision DAG、多动作事务）。实现落点：`cas/language/functions.py` 的保守函数值运算，`cas/math/functions/` 的独立函数等式 checker 与比较/延拓操作，`cas/workflow/records.py` 的 Task/Candidate/ExecutionAttempt/Revision 记录，`cas/workflow/workspace.py` 的 branch/merge/transaction、手动问题、改写/换元与 case split。
- **结构化与集合结果**：架构 §17.5 的结果语言与 §8.7 的参数线性方程结果；当前实现 `ResultLanguage.DECOMPOSITION`、`ResultLanguage.PROPOSITION`、`ResultLanguage.SET`、`StructuredResult`、`Set`/`SetSort` 与 `Coverage.SOUND_SET`/`COMPLETE_SET`。Hermite 发行 `polynomial_part`/`remainder`；`solve_linear` 发行有限解集，由 `LinearSolutionChecker` 独立核验。
- **多项式 gcd 与结式核验**：gcd 的 Bezout 判据见 Geddes 等 §2.2 与 Cohen §2.2；结式的 Sylvester 行列式定义见 Geddes 等 §7；整数分式自由行列式见 Bareiss (1968) 与 Cohen §2.2.6。实现落点：`cas/math/algebra/gcd_checker.py`（整除性 + Bezout）与 `cas/math/algebra/resultant_checker.py`（清分母 + `IntegerMatrixSpace.determinant`）；操作分别为 `polynomial_gcd` 与 `resultant`。
- **手动出现位置与改写**：架构 §19.4–§19.5 的方程变换方向与代换动作；实现落点：`cas/syntax/occurrences.py` 的结构路径/捕获规避替换，`cas/workflow/workspace.py` 的 `occurrences`/`rewrite`/`substitute`。改写方向是记录，不自动成为 kernel 判断。
- **两情形分裂、历史合并与 case-analysis**：架构 §18.1 的 Task 状态与 §19 的手动研究分支；实现落点：`cas/workflow/workspace.py` 的 `case_split`/`merge_cases`/`merge_case_conclusion` 与 `cas/kernel/case_merge.py` 的 `CaseMergeChecker`。checker 要求两个纯互补假设的直接子 frame、同一结论、分支判断无未决义务，并拒绝结论本身作为分支假设；带局部声明/定义、未决义务或超过两情形的合并仍未实现。

## 2026-11-10 R0 实根计数参考

- **Sturm 定理与开区间端点**：Sturm (1829) 的实根计数定理；系统表述与端点/符号变差约定见 Basu, Pollack, Roy, *Algorithms in Real Algebraic Geometry*, 2nd ed., Chapter 2。链为 `p0=p`、`p1=p'`、`p_{i+1}=-rem(p_{i-1},p_i)`，终止于非零常数；`V(x)` 为跳过零项的符号变差数。对平方自由 `p` 与 `a<b`，`(a,b)` 内相异实根数为 `V(a)-V(b)-[p(b)=0]`：`V` 在单根处与右极限一致，故差值先计数 `(a,b]`，再排除上端点根。实现落点：`cas/algebra/real_roots.py`；checker 共享独立递推验证 `cas/math/algebra/sturm_certificate.py`，`RootCountChecker`/`RootIsolationChecker` 消费同一验证与计数公式，均不导入搜索模块。参考实现检索入口：Maxima `src/polyrz.lisp:29-111`（`sturmseq`/`sturm1`/`sturm` 与符号变差）与 REDUCE `packages/redlog/ofsf/ofsfdpep.red`（区间隔离与符号判定）。
- **Cauchy 根界与开区间隔离**：Cauchy, *Exercices de mathématiques* (1829) 的根界 `1 + max_{i<n}|a_i/a_n|`；每个实根满足严格 `|r| < bound`。隔离算法在严格界外用 Sturm 计数二分，根值中点以确定性二进偏移避开，输出非根端点开区间。实现落点：`cas/algebra/real_roots.py` 的 `cauchy_bound`/`isolate_real_roots_open`；独立 checker `cas/math/algebra/root_isolation_checker.py` 重算该界并核对区间集合。本批不实现 `RootOf`、实代数数、重数输出或 CAD。

## 2026-11-11 G0 Gröbner 参考

- **Buchberger 算法、S-多项式判据与约化基唯一性**：B. Buchberger, doctoral thesis (1965) 与 "Ein algorithmisches Kriterium für die Lösbarkeit eines algebraischen Gleichungssystems", *Aequationes Mathematicae* 4 (1970), 374–383；D. Cox, J. Little, D. O'Shea, *Ideals, Varieties, and Algorithms*, 4th ed., Chapter 2（多元除法、S-多项式、Buchberger 算法、既约基的唯一性）。实现落点：`cas/algebra/multivariate.py`（精确多元除法、首项、S-多项式与结构化片段异常）、`cas/algebra/groebner.py`（Buchberger 搜索、sealed 约化基记录与 cofactor）、`cas/math/algebra/groebner_checker.py`（不导入搜索模块的独立 S-对/cofactor 核验）、`cas/math/algebra/groebner_operation.py`（固定默认装配 `Q[x,y]`/LEX 的 operation）。参考实现：FriCAS `src/algebra/gb.spad`（`GroebnerPackage`）与 `src/algebra/gbintern.spad`（内部正规形归约）；Maxima `share/algebra/grob1.lisp`。参考实现只用于算法结构对照，不作为正确性证明；本切片不包含 F4/F5、sugar、模方法、消元、理想交/商代数或解集语义。

## 2026-11-11 A2a1 有限域、Berlekamp 与整数多项式参考

- **确定性 64 位 Miller–Rabin**：强 probable-prime 检验与确定性基界见 G. Jaeschke, "On strong pseudoprimes to several bases", *Mathematics of Computation* 61 (1993), 915–926，以及 J. Sorenson and J. Webster, "Strong pseudoprimes to twelve prime bases", *Mathematics of Computation* 86 (2017), 985–1003。本实现使用的七基集合 `(2, 325, 9375, 28178, 450775, 9780504, 1795265022)` 是项目指定的 64 位确定性集合（Sinclair 基集）；范围 `n < 2**64` 是证书的一部分，越界以 `ValueError` 拒绝而不是返回“合数”。实现落点：`cas/algebra/finite_field.py` 的 `is_prime64` 与 `PrimeField`；`PrimeField` 不实现 `Ordered`、`IntegerEmbedding`、`RationalEmbedding` 或 `DescribedRing`。
- **有限域分解与不可约性**：E. R. Berlekamp, "Factoring polynomials over finite fields", *Bell System Technical Journal* 46 (1967), 1853–1859，以及 "Factoring polynomials over large finite fields", *Mathematics of Computation* 24 (1970), 713–735；M. O. Rabin, "Probabilistic algorithms in finite fields", *SIAM Journal on Computing* 9 (1980), 273–280。Rabin 判据为 `x**(p**n) == x (mod f)` 且对 `n` 的每个素因子 `q` 有 `gcd(f, x**(p**(n/q)) - x) == 1`；Berlekamp 用 `Q - I` 的零空间维数得到因子数，并对基多项式的每个常数 `c` 取 `gcd(f, b - c)` 递归分解。实现落点：`cas/algebra/modular_polynomial.py`（`pow_mod`、`reduce_mod_prime`、`is_squarefree_mod_prime`、`is_irreducible_mod_prime`）与 `cas/algebra/modular_factorization.py`（确定性 Berlekamp、`ModularBudget`）。二者只接受 `UnivariatePolynomialRing[int]` 上的 `PrimeField`，没有随机采样或第二种多项式表示。
- **整数多项式原语与系数界**：E. Landau, "Sur quelques théorèmes de M. Petrovitch", *Bulletin de la Société Mathématique de France* 33 (1905)，与 M. Mignotte, "An inequality about factors of polynomials", *Mathematics of Computation* 28 (1974), 1153–1157，及 Mignotte, *Mathematics for Computer Algebra* (Springer, 1992)。教材处理见 Geddes–Czapor–Labahn, *Algorithms for Computer Algebra*, Chapters 8–9；Cohen, *A Course in Computational Algebraic Number Theory*, Chapter 3，有限域分解与 Hensel/Zassenhaus 管线。实现落点：`cas/algebra/integer_polynomial.py` 的 `IntegerPolynomialForm`、`integer_primitive_form`、`rational_polynomial_form`、`monic_rational_form`、`coefficient_bound`、`symmetric_residue`、`positive_primitive_part`、`integer_divisors` 与 `congruent_mod`。系数界固定使用 `B = (1 << n) * (isqrt(sum(a_i^2)) + 1)`；证明由 Landau 不等式、因子根集包含与 Vieta 系数估计组成，不采用未证明的 `comb(n, n//2)` 紧界。
- **参考实现**：Maxima `src/factor.lisp`（`cpberl`、`cpber1`、`cpbg`、`pexptmod` 等有限域 Berlekamp 入口）与 FriCAS `src/algebra/gdpoly.spad`/`gaussfac.spad`（多项式表示、整数因子分解约定）。参考实现只用于算法结构对照，不作为正确性证明；本切片是低层 A2a1 API，不包含 Hensel 提升、Zassenhaus 重组、`Z[x]`/`Q[x]` 因式分解、`HasFactorization` 规格/checker、operation、bootstrap、workflow 或 REPL。

## 2026-11-11 A2a2a Hensel 提升与 Zassenhaus 管线参考

- **Hensel 提升与 Zassenhaus 重组**：Hensel 引理与线性提升递推见 Geddes–Czapor–Labahn, *Algorithms for Computer Algebra*, §8.4；Cohen, *A Course in Computational Algebraic Number Theory*, Chapter 3（Hensel 提升、Zassenhaus 管线与因子重组）；J. von zur Gathen and J. Gerhard, *Modern Computer Algebra*, 3rd ed., Chapter 15（一元与多元 Hensel 提升、树形提升）。Zassenhaus 的固定次数/高度界与精确乘回要求使用 `cas/algebra/integer_polynomial.py` 的 Landau/Mignotte 系数界；Mignotte 出处已在上一节记录。实现落点：`cas/algebra/factorization.py` 的 `hensel_lift_factorization`（二叉树线性提升、逐步同余核验、`HenselLift` 记录）与 `hensel_witness_for_radical`（升序素数、独立 Berlekamp 重算、`p^k > 2·coefficient_bound` 的最小精度）。参考实现：FriCAS `src/algebra/ghensel.spad`（`GeneralHenselPackage` 的 `HenselLift`/`completeHensel`）与 `src/algebra/galfact.spad`（`henselFact`）；Maxima `src/factor.lisp`（整数因式分解入口）。参考实现只用于算法结构对照，不作为正确性证明。

## 2026-11-11 A2a2b Zassenhaus 子集重组与 Q[x] 因式分解参考

- **Zassenhaus 子集重组与因子上界**：H. Zassenhaus, "On Hensel factorization I", *Journal of Number Theory* 1 (1969), 291–311；M. Mignotte, "An inequality about factors of polynomials", *Mathematics of Computation* 28 (1974), 1153–1157 与 *Mathematics for Computer Algebra* (Springer, 1992)；Landau (1905) 的系数界已在上节记录。教材处理见 Geddes–Czapor–Labahn, *Algorithms for Computer Algebra*, Chapter 8（Hensel 提升、Zassenhaus 重组与因子上界）；Cohen, *A Course in Computational Algebraic Number Theory*, Algorithm 3.5.7（Zassenhaus 分解）；von zur Gathen–Gerhard, *Modern Computer Algebra*, Chapter 15。实现落点：`cas/algebra/factorization.py` 的 `factor_primitive_integer`（升序素数、完整 Berlekamp、`p^k > 2·coefficient_bound`、`n//2` 子集与首项正因子枚举、对称剩余 + 正本原部分、精确除法递归）、`factor_polynomial_over_q`（Yun 平方自由分解 + 整数分解 + monic 有理因子与 unit）与 `Factorization`/`factorization_key`。参考实现：FriCAS `src/algebra/galfact.spad`（`henselFact`）与 `src/algebra/ghensel.spad`（`completeHensel` 的边提升边重组）；Maxima `src/factor.lisp`（整数因式分解入口）。参考实现只用于算法结构对照，不作为正确性证明。

## 2026-11-11 A2b `HasFactorization` 规格与独立 checker 参考

- **独立验证的边界**：checker 不导入 `cas.algebra.factorization` 或 `cas.algebra.modular_factorization`。它复用的只是低层数学事实：`integer_primitive_form`/`coefficient_bound`/`symmetric_residue`/`positive_primitive_part`/`integer_divisors`（Landau/Mignotte 系数界与 Zassenhaus 候选构造）、`is_prime64`（确定性 64 位素数证书）、`reduce_mod_prime`/`is_squarefree_mod_prime`/`is_irreducible_mod_prime`（Rabin 判据）以及 `congruent_mod`。Hensel 提升的唯一性、Mignotte 界给出的对称剩余唯一性、完整子集/首项因子枚举的完备性见 A2a2a/A2a2b 两节与 `cas/algebra/factorization.py` 的模块说明；checker 从候选 radical 重算这些前提，不读取搜索记录。实现落点：`cas/math/algebra/factorization_specification.py` 的 factor-set 编码与证书 schema，`cas/math/algebra/factorization_checker.py` 的独立验证顺序（候选乘积 → 问题绑定 → 源/单位/基/radical → witness → 完整重组枚举）。参考实现只用于算法结构对照，不作为正确性证明；该切片不注册 operation、bootstrap、workflow/REPL，也不声称 A2 完成。
