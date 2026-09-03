# Maple 符号计算内部实现整理

## ——Maplesoft 官方 Help 算法对应表

---

# 一、基本系统特性

| 功能                   | Maple 实现                                    |
| -------------------- | ------------------------------------------- |
| 表达式表示                | **DAG（Directed Acyclic Graph）**             |
| 内部算术表达式              | 针对多项式运算优化的内部表示                              |
| 表达式遍历                | `op` / `nops` / `map` / `subsop` / `indets` |
| 类型系统                 | `type` / `typematch`                        |
| 代数模式匹配               | `algsubs` / `patmatch`                      |
| 表达式规范化               | canonical internal representation           |
| Rational-domain 算法适配 | `frontend`：冻结复杂子表达式为临时名字                    |
| 内部结构查看               | `dismantle`                                 |
| 惰性表达式                | inert forms                                 |
| 记忆缓存                 | `remember` tables                           |
| 数学对象专用算术             | 根据对象类型 dispatch 到相应域算法                      |

Maple 官方明确说明 inert representation 紧密对应内部 DAG，而且内部表示针对快速 polynomial arithmetic 进行了优化；`dismantle` 可直接显示内部结构。

[Maple Help：ToInert / 内部 DAG](https://www.maplesoft.com/support/help/maple/view.aspx?path=ToInert&utm_source=chatgpt.com)
[Maple Help：dismantle](https://www.maplesoft.com/support/help/view.aspx?path=dismantle&utm_source=chatgpt.com)

---

# 二、代数与多项式

## 2.1 基本多项式

| 功能                        | Maple                  | 算法                                            |
| ------------------------- | ---------------------- | --------------------------------------------- |
| 多项式除法                     | `quo`, `rem`, `divide` | Euclidean division / pseudo-division          |
| GCD                       | `gcd`                  | polynomial GCD algorithms                     |
| Extended GCD              | `gcdex`                | Extended Euclidean algorithm                  |
| Resultant                 | `resultant`            | modular / subresultant / determinant methods  |
| Discriminant              | `discrim`              | resultant                                     |
| Content                   | `content`              | coefficient GCD                               |
| Primitive part            | `primpart`             | content removal                               |
| Square-free factorization | `sqrfree`              | derivative + GCD decomposition                |
| 多项式根                      | `roots`                | factorization + algebraic-root representation |

Resultant 的 Help 明确给出：高次数有理系数问题使用 **modular methods**，低次数使用 **subresultant algorithm**，其它情况使用 Bézout determinant / minor expansion。

[Maple Help：Resultant](https://www.maplesoft.com/support/help/errors/view.aspx?path=resultant&utm_source=chatgpt.com)
[Maple Help：PolynomialTools](https://www.maplesoft.com/support/help/maple/view.aspx?path=PolynomialTools)

---

## 2.2 因式分解

| 功能         | Maple           | 算法                                                        |
| ---------- | --------------- | --------------------------------------------------------- |
| GF(p) 一元分解 | `factor`        | **Cantor–Zassenhaus distinct-degree factorization**       |
| GF(p) 备用算法 | `Berlekamp`     | **Berlekamp algorithm**                                   |
| 代数数域分解     | `evala(Factor)` | **Trager / Lenstra / Linear**                             |
| 多重代数扩域     | `Domains`       | algebraic-extension factorization                         |
| 整数分解       | `ifactor`       | **MPQS / Morrison–Brillhart continued-fraction / SQUFOF** |

Maple `Factor` 的官方 Help 直接写出这些算法。 `Berlekamp` 页面明确说明它是 Cantor–Zassenhaus 的替代算法。 `ifactor` 页面明确列出 MPQS、Morrison–Brillhart、SQUFOF。

[Maple Help：Factor](https://www.maplesoft.com/support/help/Maple/view.aspx?path=Factor&utm_source=chatgpt.com)
[Maple Help：Berlekamp](https://www.maplesoft.com/support/help/view.aspx?path=Berlekamp&utm_source=chatgpt.com)
[Maple Help：ifactor](https://www.maplesoft.com/support/help/view.aspx?path=ifactor&utm_source=chatgpt.com)

---

# 三、代数数与代数函数

| 功能                       | Maple                                | 算法/表示                               |
| ------------------------ | ------------------------------------ | ----------------------------------- |
| 代数数                      | `RootOf`                             | 定义多项式 + root selector               |
| 代数函数                     | `RootOf`                             | algebraic-function representation   |
| Algebraic normal form    | `evala[Normal]`                      | algebraic-extension normalization   |
| Algebraic simplification | `evala[Simplify]`                    | symmetry / elimination / minpoly    |
| Radical normalization    | `radnormal`                          | algebraic-number normalization      |
| Algebraic GCD            | `Algebraic[GreatestCommonDivisor]`   | GCD over algebraic extensions       |
| Algebraic resultant      | `Algebraic[Resultant]`               | resultant over algebraic extensions |
| Algebraic square-free    | `Algebraic[Squarefree]`              | square-free decomposition           |
| Minimal polynomial       | `PolynomialTools[MinimalPolynomial]` | algebraic elimination               |

`RootOf` 是 Maple 的标准代数数、代数函数和有限域表示；`evala(Simplify)` 明确提供 `symmetry`、`eliminate`、`minpoly` 等算法选项。

[Maple Help：RootOf](https://www.maplesoft.com/support/help/errors/view.aspx?path=RootOf&utm_source=chatgpt.com)
[Maple Help：evala(Simplify)](https://www.maplesoft.com/support/help/view.aspx?path=evala%2FSimplify&utm_source=chatgpt.com)
[Maple Help：radnormal](https://www.maplesoft.com/support/help/maple/view.aspx?path=radnormal&utm_source=chatgpt.com)

---

# 四、Gröbner 基与代数消元

| 功能               | Maple               | 算法                                                           |
| ---------------- | ------------------- | ------------------------------------------------------------ |
| Gröbner Basis    | `Groebner[Basis]`   | **F4 / Buchberger / FGLM / Gröbner Walk**                    |
| F4               | `method=fgb`        | compiled C **F4**                                            |
| F4               | `method=maplef4`    | Maple **F4**                                                 |
| Buchberger       | `method=buchberger` | **Buchberger + Gebauer–Möller**                              |
| Order conversion | `method=fglm`       | **FGLM**                                                     |
| Order conversion | `method=walk`       | **Gröbner Walk**                                             |
| 方程组求解            | `Groebner[Solve]`   | factorization + factoring Buchberger + reduced Gröbner bases |

Maple 当前 Help 明确列出这五套核心算法及 `direct / convert / default` 策略；`default` 按 monomial order 选择直接 F4 或 FGLM/Gröbner Walk。

`Groebner[Solve]` 明确采用“先按因式分解划分，再对各 component 使用会分解中间结果的 Buchberger 变体”的方法。

[Maple Help：Groebner Basis Algorithms](https://www.maplesoft.com/support/help/maple/view.aspx?path=Groebner%2FBasis_algorithms&utm_source=chatgpt.com)
[Maple Help：Groebner Walk](https://www.maplesoft.com/support/help/maple/view.aspx?path=Groebner%2FWalk&utm_source=chatgpt.com)
[Maple Help：Groebner Solve](https://www.maplesoft.com/support/help/Maple/view.aspx?path=Groebner%2FSolve&utm_source=chatgpt.com)

---

# 五、Regular Chains / 三角分解

| 功能               | Maple                          | 算法                                            |
| ---------------- | ------------------------------ | --------------------------------------------- |
| 三角分解             | `RegularChains[Triangularize]` | **Regular Chains**                            |
| 增量求解             | `Triangularize`                | incremental decomposition                     |
| Regular GCD      | `RegularGcd`                   | regular GCD + subresultant machinery          |
| Regularization   | `Regularize`                   | regular-chain regularization                  |
| 实代数系统            | `RealTriangularize`            | real triangular decomposition                 |
| 半代数系统            | `RealTriangularize`            | real regular-chain methods                    |
| 参数系统             | `ComprehensiveTriangularize`   | comprehensive triangular decomposition        |
| 快速 GCD/resultant | `FastArithmeticTools`          | specialization/interpolation + FFT arithmetic |

Maple 官方说明 `Triangularize` 逐步通过 `Intersect` 将方程加入 regular chain；`RegularGcd` 是该体系的重要运算。

[Maple Help：RegularChains/Triangularize](https://www.maplesoft.com/support/help/errors/view.aspx?path=RegularChains%2FTriangularize&utm_source=chatgpt.com)
[Maple Help：RegularChains/Examples](https://www.maplesoft.com/support/help/errors/view.aspx?path=examples%2FRegularChains&utm_source=chatgpt.com)
[Maple Help：ComprehensiveTriangularize](https://www.maplesoft.com/support/help/errors/view.aspx?path=RegularChains%2FParametricSystemTools%2FComprehensiveTriangularize&utm_source=chatgpt.com)

---

# 六、实代数几何 / 量词消去

| 功能                        | Maple                                  | 算法                               |
| ------------------------- | -------------------------------------- | -------------------------------- |
| 实数域量词消去                   | `QuantifierEliminate`                  | **VTS + CAD polyalgorithm**      |
| Virtual Term Substitution | `QuantifierEliminate`                  | **VTS**                          |
| CAD                       | `CylindricalAlgebraicDecompose`        | **projection + lifting CAD**     |
| CAD projection            | CAD engine                             | **Lazard projection**            |
| Partial CAD               | `PartialCylindricalAlgebraicDecompose` | Partial CAD                      |
| CAD cells                 | `CADData`                              | CAD decomposition data structure |
| 实三角分解                     | `RealTriangularize`                    | real regular-chain decomposition |

Maple 当前 Help 的示例输出直接显示 `QuantifierEliminate` 根据问题进行 **poly-algorithmic QE**，其中使用 VTS；CAD 页面定义 `CylindricalAlgebraicDecompose` 为 F-invariant CAD，Help 示例还直接出现 **Lazard projection CAD**。

[Maple Help：QuantifierElimination 示例](https://www.maplesoft.com/support/help/errors/view.aspx?path=examples%2FQuantifierElimination&utm_source=chatgpt.com)
[Maple Help：CylindricalAlgebraicDecompose](https://www.maplesoft.com/support/help/errors/view.aspx?path=RegularChains%2FSemiAlgebraicSetTools%2FCylindricalAlgebraicDecompose&utm_source=chatgpt.com)
[Maple Help：RealTriangularize](https://www.maplesoft.com/support/help/errors/view.aspx?path=RegularChains%2FRealTriangularize&utm_source=chatgpt.com)

---

# 七、符号线性代数

| 功能                     | Maple                      | 算法                                    |
| ---------------------- | -------------------------- | ------------------------------------- |
| `LinearSolve`          | `LinearSolve`              | Gaussian / LU / modular algorithms    |
| `RowReduce`            | `RREF`                     | Gaussian elimination                  |
| `NullSpace`            | `NullSpace`                | elimination                           |
| `Rank`                 | `Rank`                     | elimination                           |
| `Inverse`              | `MatrixInverse`            | Gaussian / LU                         |
| `Det`                  | `Determinant`              | minor / fraction-free / modular       |
| 特征多项式                  | `CharacteristicPolynomial` | determinant/Berkowitz                 |
| Generic determinant    | `Generic[Determinant]`     | Bareiss / Berkowitz                   |
| Bareiss                | `BareissAlgorithm`         | **Bareiss fraction-free algorithm**   |
| Berkowitz              | `BerkowitzAlgorithm`       | **division-free Berkowitz algorithm** |
| Hermite form           | `HermiteForm`              | exact elimination                     |
| Smith form             | `SmithForm`                | exact row/column reduction + GCD      |
| Modular linear algebra | `LinearAlgebra[Modular]`   | modular elimination                   |

`Determinant` 当前根据矩阵数据类型自动选择方法，也可显式指定 `fracfree`、`modular[p]`、`minor`、`univar` 等。 Generic Help 明确提供 Bareiss 和 Berkowitz。

[Maple Help：LinearAlgebra/Determinant](https://www.maplesoft.com/support/help/Maple/view.aspx?path=LinearAlgebra%2FDeterminant&utm_source=chatgpt.com)
[Maple Help：LinearAlgebra/Generic](https://www.maplesoft.com/support/help/maple/view.aspx?path=LinearAlgebra%2FGeneric&utm_source=chatgpt.com)
[Maple Help：LinearAlgebra/NullSpace](https://www.maplesoft.com/support/help/maple/view.aspx?path=LinearAlgebra%2FNullSpace&utm_source=chatgpt.com)

---

# 八、方程求解

| 功能     | Maple                        | 算法                                     |
| ------ | ---------------------------- | -------------------------------------- |
| 线性方程组  | `solve` / `LinearSolve`      | Gaussian elimination                   |
| 一元多项式  | `solve`                      | algebraic solving / RootOf             |
| 高次多项式  | `solve`                      | `RootOf`                               |
| 多项式系统  | `Groebner[Solve]`            | factoring Buchberger                   |
| 三角分解求解 | `RegularChains`              | Regular Chains                         |
| 实多项式系统 | `RealTriangularize`          | real triangular decomposition          |
| 参数系统   | `ComprehensiveTriangularize` | comprehensive triangular decomposition |
| 整数方程   | `isolve`                     | Diophantine algorithms                 |
| 代数根    | `RootOf`                     | polynomial + selector representation   |

`solve` 是统一入口，而具体的代数系统求解器由 `Groebner[Solve]` 和 `RegularChains` 等组成。

[Maple Help：solve](https://www.maplesoft.com/support/help/view.aspx?path=solve&utm_source=chatgpt.com)
[Maple Help：Groebner/Solve](https://www.maplesoft.com/support/help/Maple/view.aspx?path=Groebner%2FSolve&utm_source=chatgpt.com)
[Maple Help：RootOf](https://www.maplesoft.com/support/help/errors/view.aspx?path=RootOf&utm_source=chatgpt.com)

---

# 九、符号化简

| 功能                       | Maple                   | 算法                                        |
| ------------------------ | ----------------------- | ----------------------------------------- |
| 通用化简                     | `simplify`              | expression scan + specialized simplifiers |
| 三角化简                     | `simplify(...,trig)`    | trigonometric identities / normalization  |
| Radical 化简               | `simplify(...,radical)` | radical normalization                     |
| Square-root 化简           | `simplify(...,sqrt)`    | square extraction + radical normalization |
| Gamma/factorial/binomial | `simplify(...,GAMMA)`   | Gamma identities                          |
| Algebraic simplify       | `evala(Simplify)`       | symmetry / elimination / minpoly          |
| Rational normal form     | `normal`                | numerator/denominator normalization       |
| Algebraic substitution   | `algsubs`               | algebraic pattern substitution            |
| 函数合并                     | `combine`               | function-specific identities              |

`simplify` 会扫描 function calls、square roots、radicals、powers，然后调用相应 simplification procedure。 Radical simplifier 明确分为三阶段：单个 radical 化简、radical 间消去、整体 rational normalization。

[Maple Help：simplify](https://www.maplesoft.com/support/help/errors/view.aspx?path=simplify&utm_source=chatgpt.com)
[Maple Help：simplify/radical](https://maplesoft.com/support/help/view.aspx?path=simplify%2Fradical&utm_source=chatgpt.com)
[Maple Help：simplify/GAMMA](https://www.maplesoft.com/support/help/maple/view.aspx?path=simplify%2FGAMMA&utm_source=chatgpt.com)
[Maple Help：algsubs](https://www.maplesoft.com/support/help/maple/view.aspx?path=algsubs&utm_source=chatgpt.com)
[Maple Help：normal](https://www.maplesoft.com/support/help/Maple/view.aspx?path=normal&utm_source=chatgpt.com)

---

# 十、微分

| 功能       | Maple                      | 算法                                   |
| -------- | -------------------------- | ------------------------------------ |
| 一阶微分     | `diff`                     | structural recursive differentiation |
| 高阶微分     | `diff`                     | recursive differentiation            |
| 偏导       | `diff`                     | recursive differentiation            |
| 隐式微分     | `implicitdiff`             | implicit differentiation             |
| 分数阶微分    | `fracdiff`                 | fractional symbolic differentiation  |
| Jacobian | `VectorCalculus[Jacobian]` | partial derivatives                  |
| Hessian  | `VectorCalculus[Hessian]`  | second partial derivatives           |
| Gradient | `VectorCalculus[Gradient]` | symbolic differentiation             |

[Maple Help：diff](https://de.maplesoft.com/support/help/Maple/view.aspx?path=diff&utm_source=chatgpt.com)
[Maple Help：VectorCalculus/Jacobian](https://de.maplesoft.com/support/help/maple/view.aspx?path=VectorCalculus%2FJacobian&utm_source=chatgpt.com)
[Maple Help：VectorCalculus 总览](https://www.maplesoft.com/support/help/Maple/view.aspx?path=VectorCalculus&utm_source=chatgpt.com)

---

# 十一、符号积分

| 功能               | Maple            | 算法                                     |
| ---------------- | ---------------- | -------------------------------------- |
| 不定积分             | `int`            | **polyalgorithm**                      |
| 代换               | `DDivides`       | derivative-divisibility + substitution |
| 分部积分             | `Parts`          | integration by parts                   |
| 初等函数积分           | `Risch`          | **partial Risch algorithm**            |
| Risch-Norman     | `Norman`         | **Risch-Norman**                       |
| 代数函数积分           | `Trager`         | **Risch–Trager**                       |
| Parallel Risch   | `ParallelRisch`  | parallel Risch                         |
| Hyperexponential | `Gosper`         | **Gosper method**                      |
| Elliptic         | `Elliptic`       | elliptic-integral reduction            |
| Pseudoelliptic   | `Pseudoelliptic` | algebraic substitution search          |
| Meijer G         | `MeijerG`        | Meijer-G representation                |
| 查表               | `LookUp`         | lookup table                           |
| 多项式              | `Polynomial`     | direct algebraic integration           |
| 有理函数             | `Ratpoly`        | rational-function integration          |

这是 Maple Help 中公开算法最完整的一部分；`int/methods` 直接列出所有这些 integrators。

[Maple Help：Integration Methods](https://www.maplesoft.com/support/help/Maple/view.aspx?path=int%2Fmethods)

---

# 十二、定积分与积分变换

| 功能                | Maple               | 算法                                                                        |
| ----------------- | ------------------- | ------------------------------------------------------------------------- |
| Fourier transform | `inttrans[fourier]` | lookup → piecewise/products/powers/sums/rational-polynomial → integration |
| Laplace transform | `inttrans[laplace]` | transform rules + structural processing                                   |
| Inverse Laplace   | `invlaplace`        | inverse-transform rules                                                   |
| Mellin transform  | `mellin`            | Mellin transform identities                                               |
| Inverse Mellin    | `invmellin`         | contour/transform machinery                                               |
| Hankel transform  | `hankel`            | transform identities                                                      |
| Hilbert transform | `hilbert`           | symbolic transform machinery                                              |

Fourier Help 直接公开其算法顺序，从 lookup-table classification 开始，再处理 piecewise、products、powers、sums、rational polynomials，最后退回 integration。

[Maple Help：Fourier Transform](https://cn.maplesoft.com/support/help/maple/view.aspx?path=inttrans%2Ffourier&utm_source=chatgpt.com)
[Maple Help：Laplace Transform](https://www.maplesoft.com/support/help/errors/view.aspx?path=inttrans%2Flaplace&utm_source=chatgpt.com)
[Maple Help：Inverse Mellin Transform](https://www.maplesoft.com/support/help/maple/view.aspx?path=inttrans%2Finvmellin&utm_source=chatgpt.com)

---

# 十三、极限与级数

| 功能             | Maple                           | 算法                                  |
| -------------- | ------------------------------- | ----------------------------------- |
| `limit`        | `limit`                         | **主要通过 series / leading-term**      |
| Taylor         | `taylor`                        | formal Taylor expansion             |
| Series         | `series`                        | formal series machinery             |
| Leading term   | `leadterm`                      | leading-order extraction            |
| 多元 Taylor      | `mtaylor`                       | multivariate Taylor expansion       |
| 渐近展开           | `asympt`                        | asymptotic expansion                |
| 广义渐近级数         | `MultiSeries`                   | generalized asymptotic scales       |
| 特殊函数级数         | `MathematicalFunctions[Series]` | **Sum-form based unified approach** |
| 多元幂级数          | `MultivariatePowerSeries`       | formal power-series arithmetic      |
| Puiseux series | `PuiseuxSeries`                 | Puiseux-series algorithms           |

Maple 明确写出 **most limits are resolved by computing series**。 特殊函数 Series 使用以原点 Sum form 为基础的统一方法。

[Maple Help：limit](https://www.maplesoft.com/support/help/errors/view.aspx?path=limit&utm_source=chatgpt.com)
[Maple Help：taylor](https://www.maplesoft.com/support/help/maple/view.aspx?path=taylor&utm_source=chatgpt.com)
[Maple Help：MathematicalFunctions/Series](https://www.maplesoft.com/support/help/maple/view.aspx?path=MathematicalFunctions%2FSeries&utm_source=chatgpt.com)
[Maple Help：MultivariatePowerSeries](https://www.maplesoft.com/support/help/Maple/view.aspx?path=MultivariatePowerSeries&utm_source=chatgpt.com)

---

# 十四、多元形式级数

| 功能                           | Maple                                        | 算法                         |
| ---------------------------- | -------------------------------------------- | -------------------------- |
| Power series                 | `PowerSeries`                                | formal multivariate series |
| Series arithmetic            | `Add`, `Multiply`, `Inverse`, `Exponentiate` | formal-series arithmetic   |
| Puiseux series               | `PuiseuxSeries`                              | rational-exponent series   |
| Weierstrass preparation      | `WeierstrassPreparation`                     | Weierstrass preparation    |
| Hensel factorization         | `HenselFactorize`                            | Hensel lifting             |
| Lazy coefficient computation | PowerSeries object                           | lazy precision update      |
| Series over series           | polynomial-over-power-series representation  | nested formal algebra      |

Maple 的 `MultivariatePowerSeries` 是独立的符号代数系统，直接支持加法、乘法、求逆、求幂和 factorization。

[Maple Help：MultivariatePowerSeries 总览](https://www.maplesoft.com/support/help/Maple/view.aspx?path=MultivariatePowerSeries&utm_source=chatgpt.com)
[Maple Help：PowerSeries](https://www.maplesoft.com/support/help/Maple/view.aspx?path=MultivariatePowerSeries%2FPowerSeries&utm_source=chatgpt.com)
[Maple Help：PuiseuxSeries](https://www.maplesoft.com/support/help/Maple/view.aspx?path=MultivariatePowerSeries%2FPuiseuxSeries&utm_source=chatgpt.com)

---

# 十五、常微分方程

| 功能                           | Maple                       | 算法                                                                               |
| ---------------------------- | --------------------------- | -------------------------------------------------------------------------------- |
| ODE 总求解                      | `dsolve`                    | classification + polyalgorithm                                                   |
| 可分离方程                        | `dsolve`                    | separation                                                                       |
| 一阶线性                         | `dsolve`                    | integrating factor                                                               |
| Bernoulli                    | `dsolve`                    | Bernoulli transformation                                                         |
| Riccati                      | `dsolve`                    | Riccati methods                                                                  |
| Abel                         | `dsolve`                    | Abel transformations/invariants                                                  |
| Exact ODE                    | `dsolve`                    | exactness + potential                                                            |
| Lie symmetry                 | `dsolve`                    | Lie-symmetry methods                                                             |
| Equivalence methods          | `dsolve`                    | classical invariant theory                                                       |
| Liouvillian / hypergeometric | `dsolve`                    | special-function recognition                                                     |
| 二阶线性                         | `dsolve`                    | **Kovacic algorithm** 等                                                          |
| ODE series                   | `dsolve(...,series)`        | **Newton iteration → direct substitution → Frobenius → LinearFunctionalSystems** |
| Formal series                | `dsolve(...,formal_series)` | formal-series algorithms                                                         |

Maple 当前 `dsolve` Help 明确把 classification、integrating factor、symmetry、equivalence/classical invariant theory 和 Kovacic decision procedures 组合起来。

其 series solver 明确顺序为 **Newton iteration → direct substitution → Frobenius → LinearFunctionalSystems[SeriesSolution]**。

[Maple Help：dsolve Details](https://www.maplesoft.com/support/help/errors/view.aspx?path=dsolve%2Fdetails&utm_source=chatgpt.com)
[Maple Help：dsolve Series](https://www.maplesoft.com/support/help/maple/view.aspx?path=dsolve%2Fseries&utm_source=chatgpt.com)
[Maple Help：dsolve References](https://www.maplesoft.com/support/help/Maple/view.aspx?path=dsolve%2Freferences)

---

# 十六、PDE

| 功能                       | Maple                               | 算法                                        |
| ------------------------ | ----------------------------------- | ----------------------------------------- |
| PDE 求解                   | `pdsolve`                           | symbolic PDE solver framework             |
| Lie symmetry             | `PDEtools[Infinitesimals]`          | determining equations + Lie symmetry      |
| Invariant solutions      | `PDEtools[InvariantSolutions]`      | symmetry reduction                        |
| Invariant transformation | `PDEtools[InvariantTransformation]` | symmetry transformation                   |
| Integrating factors      | `PDEtools[IntegratingFactors]`      | integrating-factor computation            |
| Polynomial PDE solutions | `PDEtools[PolynomialSolutions]`     | polynomial ansatz + coefficient equations |
| PDE reduction            | `PDEtools[ReducedForm]`             | differential reduction                    |
| Differential invariants  | `PDEtools[Invariants]`              | invariant construction                    |

[Maple Help：pdsolve](https://www.maplesoft.com/support/help/maple/view.aspx?path=pdsolve&utm_source=chatgpt.com)
[Maple Help：PDEtools/Infinitesimals](https://www.maplesoft.com/support/help/Maple/view.aspx?path=PDEtools%2FInfinitesimals)
[Maple Help：PDEtools/InvariantSolutions](https://www.maplesoft.com/support/help/Maple/view.aspx?path=PDEtools%2FInvariantSolutions)

---

# 十七、微分代数

| 功能                             | Maple                       | 算法                                     |
| ------------------------------ | --------------------------- | -------------------------------------- |
| Differential polynomial ring   | `DifferentialRing`          | differential-polynomial ring + ranking |
| Differential reduction         | `NormalForm`, `ReducedForm` | differential reduction                 |
| Differential ideal membership  | `BelongsTo`                 | differential ideal algorithms          |
| Differential elimination       | `RosenfeldGroebner`         | **Rosenfeld–Gröbner algorithm**        |
| Differential decomposition     | `RosenfeldGroebner`         | differential triangular decomposition  |
| Formal power-series solution   | `PowerSeriesSolution`       | differential elimination + series      |
| Differential triangularization | `DifferentialThomas`        | **Thomas decomposition**               |
| Differential system reduction  | `ReducedForm`               | differential Thomas reduction          |

Maple 官方明确把 `DifferentialAlgebra` 定义为 algebraic/differential elimination package，并把 `RosenfeldGroebner` 作为核心。

`DifferentialThomas` 直接实现 Thomas decomposition，并用于微分系统三角化、正规形和形式级数解。

[Maple Help：DifferentialAlgebra](https://www.maplesoft.com/support/help/errors/view.aspx?path=DifferentialAlgebra&utm_source=chatgpt.com)
[Maple Help：RosenfeldGroebner](https://www.maplesoft.com/support/help/maple/view.aspx?path=DifferentialAlgebra%2FRosenfeldGroebner&utm_source=chatgpt.com)
[Maple Help：DifferentialThomas](https://de.maplesoft.com/support/help/view.aspx?path=DifferentialThomas&utm_source=chatgpt.com)

---

# 十八、递推 / 差分方程

| 功能                      | Maple                  | 算法                                   |
| ----------------------- | ---------------------- | ------------------------------------ |
| Linear recurrence       | `LREtools`             | recurrence algorithms                |
| 常系数递推                   | `constcoeffsol`        | characteristic-polynomial method     |
| Polynomial solution     | `polysols`             | polynomial-solution algorithms       |
| Rational solution       | `ratpolysols`          | rational-solution algorithms         |
| Hypergeometric solution | `hypergeomsols`        | hypergeometric recurrence algorithms |
| m-Hypergeometric        | `mhypergeomsols`       | m-hypergeometric algorithms          |
| GCRD                    | `GCRD`                 | operator GCRD                        |
| LCLM                    | `LCLM`                 | operator LCLM                        |
| Right factorization     | `RightFactors`         | recurrence-operator factorization    |
| Minimal recurrence      | `MinimalRecurrence`    | recurrence minimization              |
| Recurrence guessing     | `GuessRecurrence`      | recurrence guessing                  |
| Recurrence → operator   | `RecurrenceToOperator` | Ore/operator conversion              |
| Operator → recurrence   | `OperatorToRecurrence` | reverse conversion                   |

Maple 的 `LREtools` 官方总览直接列出这些核心命令。

[Maple Help：LREtools](https://www.maplesoft.com/support/help/maple/view.aspx?path=LREtools)

---

# 十九、q-差分方程

| 功能                        | Maple                     | 算法                              |
| ------------------------- | ------------------------- | ------------------------------- |
| Polynomial solution       | `PolynomialSolution`      | polynomial q-difference solving |
| Rational solution         | `RationalSolution`        | universal-denominator method    |
| q-Hypergeometric solution | `QHypergeometricSolution` | q-hypergeometric algorithms     |
| Series solution           | `SeriesSolution`          | formal q-series                 |
| Universal denominator     | `UniversalDenominator`    | q-dispersion based              |
| q-dispersion              | `QDispersion`             | q-difference dispersion         |
| q-recurrence              | `QDifferenceEquations`    | q-shift/Ore algebra             |

Maple Help 明确说明：寻找 rational solution 时先构造 universal denominator，而 universal denominator 又依赖 q-dispersion。

[Maple Help：QDifferenceEquations 总览](https://www.maplesoft.com/support/help/Maple/view.aspx?path=QDifferenceEquations&utm_source=chatgpt.com)
[Maple Help：UniversalDenominator](https://www.maplesoft.com/support/help/Maple/view.aspx?path=QDifferenceEquations%2FUniversalDenominator&utm_source=chatgpt.com)
[Maple Help：QHypergeometricSolution](https://www.maplesoft.com/support/help/Maple/view.aspx?path=QDifferenceEquations%2FQHypergeometricSolution&utm_source=chatgpt.com)

---

# 二十、Ore Algebra

| 功能                       | Maple                             | 算法                                    |
| ------------------------ | --------------------------------- | ------------------------------------- |
| Differential Ore ring    | `SetOreRing(...,'differential')`  | differential Ore algebra              |
| Shift Ore ring           | `SetOreRing(...,'shift')`         | shift Ore algebra                     |
| q-Shift Ore ring         | `SetOreRing(...,'qshift')`        | q-Ore algebra                         |
| Ore polynomial           | `OrePoly`                         | noncommutative polynomial             |
| Right division           | `RightDivision`                   | Ore Euclidean division                |
| Right quotient/remainder | `RightQuotient`, `RightRemainder` | Ore division                          |
| GCRD                     | `GCRD`                            | generalized common right divisor      |
| LCLM                     | `LCLM`                            | least common left multiple            |
| Modular GCRD             | `Modular[GCRD]`                   | modular Ore-GCD                       |
| Modular LCLM             | `Modular[LCLM]`                   | modular Ore-LCLM                      |
| Fraction-free Euclidean  | `FractionFree`                    | fraction-free Ore Euclidean algorithm |

`SetOreRing` 直接支持 differential、shift、qshift 三种 Ore algebra；OreTools 直接提供 GCD/GCRD/LCLM/Euclidean/Modular 子系统。

[Maple Help：OreTools 总览](https://www.maplesoft.com/support/help/Maple/view.aspx?path=OreTools)
[Maple Help：SetOreRing](https://www.maplesoft.com/support/help/maple/view.aspx?path=OreTools%2FSetOreRing&utm_source=chatgpt.com)
[Maple Help：Modular GCRD/LCLM](https://fr.maplesoft.com/support/help/maple/view.aspx?path=OreTools%2FModular%2FGCRD&utm_source=chatgpt.com)

---

# 二十一、符号求和

| 功能                            | Maple                                     | 算法                                     |
| ----------------------------- | ----------------------------------------- | -------------------------------------- |
| Symbolic summation            | `sum`                                     | symbolic summation polyalgorithm       |
| Rational indefinite sum       | `SumTools[IndefiniteSum][Rational]`       | **Abramov algorithm**                  |
| Hypergeometric indefinite sum | `SumTools[IndefiniteSum][Hypergeometric]` | **Gosper + Koepf + Abramov–Petkovšek** |
| Gosper                        | `SumTools[Hypergeometric][Gosper]`        | **Gosper algorithm**                   |
| Zeilberger                    | `SumTools[Hypergeometric][Zeilberger]`    | **Zeilberger / creative telescoping**  |
| WZ                            | `WZMethod`                                | **Wilf–Zeilberger**                    |
| Hyperrecursion                | `sumtools[hyperrecursion]`                | **Koepf extension of Zeilberger**      |

官方 Hypergeometric Help 直接列出 Gosper、Koepf、Abramov–Petkovšek 三个算法。 Rational summation 明确使用 Abramov。 `WZMethod` 和 `Zeilberger` 分别直接实现 WZ / Zeilberger。

[Maple Help：Hypergeometric Summation](https://www.maplesoft.com/support/help/Maple/view.aspx?path=SumTools%2FIndefiniteSum%2FHypergeometric)
[Maple Help：Rational Summation](https://www.maplesoft.com/support/help/maple/view.aspx?path=SumTools%2FIndefiniteSum%2FRational)
[Maple Help：WZMethod](https://jp.maplesoft.com/support/help/maple/view.aspx?path=SumTools%2FHypergeometric%2FWZMethod&utm_source=chatgpt.com)
[Maple Help：Zeilberger](https://jp.maplesoft.com/support/help/errors/view.aspx?path=SumTools%2FHypergeometric%2FZeilberger&utm_source=chatgpt.com)

---

# 二十二、乘积

| 功能                      | Maple                  | 算法                               |
| ----------------------- | ---------------------- | -------------------------------- |
| Symbolic product        | `product`              | symbolic product algorithms      |
| Hypergeometric product  | `product`              | hypergeometric transformations   |
| Factorial/Gamma product | `product`              | Gamma/factorial identities       |
| q-product               | `product`              | q-product transformations        |
| Product simplification  | `simplify` / `combine` | function-specific symbolic rules |

---

# 二十三、特殊函数

| 功能                        | Maple                                | 实现                                   |
| ------------------------- | ------------------------------------ | ------------------------------------ |
| 特殊函数知识库                   | `MathematicalFunctions`              | mathematical-function knowledge base |
| 函数分类                      | `FunctionAdvisor` / `SearchFunction` | function classification              |
| 微分规则                      | `FunctionAdvisor`                    | stored differentiation rules         |
| 积分表示                      | `FunctionAdvisor`                    | integral representations             |
| Sum form                  | `FunctionAdvisor`                    | summation representations            |
| Series                    | `MathematicalFunctions[Series]`      | **Sum-form based unified method**    |
| 渐近展开                      | `FunctionAdvisor`                    | stored asymptotic forms              |
| 恒等式                       | `FunctionAdvisor`                    | transformation-rule database         |
| Hypergeometric conversion | `convert(...,hypergeom)`             | hypergeometric transformations       |
| MeijerG conversion        | `convert(...,MeijerG)`               | Meijer-G transformations             |

`MathematicalFunctions` 官方页面直接列出 `FunctionAdvisor`、`SearchFunction`、`Series` 等；Series 方法明确以函数的 Sum form 为统一基础。

[Maple Help：MathematicalFunctions](https://www.maplesoft.com/support/help/maple/view.aspx?path=MathematicalFunctions)
[Maple Help：MathematicalFunctions/Series](https://www.maplesoft.com/support/help/maple/view.aspx?path=MathematicalFunctions%2FSeries&utm_source=chatgpt.com)

---

# 二十四、生成函数 / Holonomic

| 功能                                 | Maple               | 算法                                    |
| ---------------------------------- | ------------------- | ------------------------------------- |
| Generating-function manipulation   | `gfun`              | generating-function algorithms        |
| Sequence → recurrence              | `listtorec`         | linear recurrence reconstruction      |
| Series → recurrence                | `seriestorec`       | coefficient recurrence extraction     |
| GF → differential equation         | `seriestodiffeq`    | differential-equation conversion      |
| Differential equation → recurrence | `diffeqtorec`       | coefficient/recurrence transformation |
| Algebraic GF → ODE                 | `algeqtodiffeq`     | algebraic elimination                 |
| Algebraic GF → series              | `algeqtoseries`     | algebraic-series expansion            |
| Guess recurrence                   | `guesseqn`          | recurrence guessing                   |
| Guess GF                           | `guessgf`           | generating-function guessing          |
| Series → hypergeom                 | `seriestohypergeom` | hypergeometric recognition            |

`gfun` 官方总览明确定位为 generating functions 的确定与操作工具，并支持 differential-equation / recurrence / generating-function 之间的转换。 `listtorec` / `seriestorec` 明确计算满足数据的多项式系数线性递推。

[Maple Help：gfun](https://www.maplesoft.com/support/help/Maple/view.aspx?path=gfun)
[Maple Help：gfun/listtorec](https://www.maplesoft.com/support/help/maple/view.aspx?path=gfun%2Flisttorec&utm_source=chatgpt.com)

---

# 二十五、代数曲线 / 代数函数域

| 功能                | Maple                | 算法                                           |
| ----------------- | -------------------- | -------------------------------------------- |
| Algebraic curves  | `algcurves`          | algebraic-curve algorithms                   |
| Puiseux expansion | `algcurves[puiseux]` | Puiseux algorithm                            |
| Integral basis    | `integral_basis`     | **van Hoeij algorithm + Puiseux expansions** |
| Parametrization   | `parametrization`    | integral-basis/algebraic-curve methods       |
| Weierstrass form  | `Weierstrassform`    | algebraic-curve transformation               |
| Singularities     | `singularities`      | discriminant + Puiseux analysis              |
| Genus             | `genus`              | algebraic-curve genus calculation            |
| Differentials     | `differentials`      | algebraic-function differential basis        |
| Intersection      | `intersectcurves`    | elimination                                  |
| Monodromy         | `monodromy`          | algebraic-function monodromy                 |

`algcurves` 官方总览直接列出这套命令；`integral_basis` 明确说明其算法基于 Puiseux expansions 和 **van Hoeij 1994 algorithm**。

[Maple Help：algcurves 总览](https://www.maplesoft.com/support/help/maple/view.aspx?path=algcurves&utm_source=chatgpt.com)
[Maple Help：integral_basis](https://www.maplesoft.com/support/help/maple/view.aspx?path=algcurves%2Fintegral_basis&utm_source=chatgpt.com)
[Maple Help：Puiseux](https://www.maplesoft.com/support/help/Maple/view.aspx?path=algcurves%2Fpuiseux)

---

# 二十六、积分方程

| 功能                       | Maple                         | 算法                                     |
| ------------------------ | ----------------------------- | -------------------------------------- |
| Linear integral equation | `intsolve`                    | symbolic integral-equation solver      |
| 默认精确方法                   | `method=differentialequation` | integral equation → ODE-IVP → `dsolve` |
| 备用                       | `method=eigenfunction`        | eigenfunction method                   |
| Laplace 型                | `method=Laplace`              | Laplace transform                      |
| Neumann                  | `method=Neumann`              | Neumann-series method                  |
| Fourier-Sine/Cosine      | 自动识别                          | integral-transform recognition         |

Maple Help 明确写出默认路线：转换成等价 ODE-IVP 后调用 `dsolve`；失败后使用 eigenfunction；另有 Laplace、Neumann 方法。

[Maple Help：intsolve](https://www.maplesoft.com/support/help/maple/view.aspx?path=intsolve&utm_source=chatgpt.com)

---

# 二十七、数论

| 功能                     | Maple               | 算法                                      |
| ---------------------- | ------------------- | --------------------------------------- |
| Integer GCD            | `igcd`              | Euclidean algorithm                     |
| Extended GCD           | `igcdex`            | Extended Euclidean                      |
| Modular exponentiation | `powmod`            | repeated squaring                       |
| Chinese remainder      | `chrem`             | Chinese Remainder Theorem               |
| Integer factorization  | `ifactor`           | **MPQS / Morrison–Brillhart / SQUFOF**  |
| Prime test             | `isprime`           | primality-testing algorithms            |
| Continued fraction     | `ContinuedFraction` | Euclidean algorithm                     |
| Primitive root         | `PrimitiveRoot`     | modular-group algorithms                |
| Totient                | `Totient`           | arithmetic-function algorithms          |
| Divisors               | `Divisors`          | factorization/divisor generation        |
| Quadratic residue      | `QuadraticResidue`  | modular number theory                   |
| Thue equation          | `ThueSolve`         | algebraic-number Diophantine algorithms |
| Integral basis         | `IntegralBasis`     | algebraic-number algorithms             |

`NumberTheory` 是 Maple 的专门数论 package；`ifactor` 进一步明确暴露 MPQS、Morrison–Brillhart continued-fraction、SQUFOF。

[Maple Help：NumberTheory](https://www.maplesoft.com/support/help/Maple/view.aspx?path=NumberTheory)
[Maple Help：ifactor](https://www.maplesoft.com/support/help/view.aspx?path=ifactor&utm_source=chatgpt.com)

---

# 二十八、向量分析

| 功能                     | Maple             | 算法                                     |
| ---------------------- | ----------------- | -------------------------------------- |
| Gradient               | `Gradient`        | symbolic differentiation               |
| Divergence             | `Divergence`      | coordinate differential operator       |
| Curl                   | `Curl`            | coordinate differential operator       |
| Laplacian              | `Laplacian`       | differential-operator composition      |
| Jacobian               | `Jacobian`        | first partial derivatives              |
| Hessian                | `Hessian`         | second partial derivatives             |
| Directional derivative | `DirectionalDiff` | symbolic directional differentiation   |
| Line integral          | `LineInt`         | parametrization + symbolic integration |
| Surface integral       | `SurfaceInt`      | parametrization + Jacobian             |
| Flux                   | `Flux`            | parametrization + normal/Jacobian      |
| Scalar potential       | `ScalarPotential` | exactness + symbolic integration       |

[Maple Help：VectorCalculus](https://www.maplesoft.com/support/help/Maple/view.aspx?path=VectorCalculus&utm_source=chatgpt.com)
[Maple Help：Jacobian](https://de.maplesoft.com/support/help/maple/view.aspx?path=VectorCalculus%2FJacobian&utm_source=chatgpt.com)

---

# 二十九、微分几何 / Tensor / Lie

| 功能                  | Maple                  | 实现                                |
| ------------------- | ---------------------- | --------------------------------- |
| Differential forms  | `DifferentialGeometry` | exterior algebra                  |
| Exterior derivative | `ExteriorDerivative`   | exterior differential             |
| Tensor product      | `&tensor`              | tensor algebra                    |
| Tensor contraction  | `Hook`, `Tensor`       | tensor contraction                |
| Lie bracket         | `LieBracket`           | vector-field commutator           |
| Lie derivative      | `LieDerivative`        | derivation                        |
| Pullback            | `Pullback`             | pullback transformation           |
| Pushforward         | `Pushforward`          | Jacobian transformation           |
| Jet spaces          | `JetCalculus`          | jet-space differential algebra    |
| Lie algebras        | `LieAlgebras`          | Lie-algebra structure algorithms  |
| Group actions       | `GroupActions`         | symbolic group-action computation |
| de Rham homotopy    | `DeRhamHomotopy`       | homotopy operators                |

Maple 官方把 DifferentialGeometry 描述为一套完整的 manifold calculus、differential forms、tensor analysis、jet-space、Lie algebra/group 计算系统。

[Maple Help：DifferentialGeometry](https://www.maplesoft.com/support/help/maple/view.aspx?path=DifferentialGeometry&utm_source=chatgpt.com)
[Maple Help：ExteriorDerivative](https://www.maplesoft.com/support/help/maple/view.aspx?path=DifferentialGeometry%2FExteriorDerivative&utm_source=chatgpt.com)
[Maple Help：LieBracket](https://www.maplesoft.com/support/help/maple/view.aspx?path=DifferentialGeometry%2FLieBracket&utm_source=chatgpt.com)
[Maple Help：LieDerivative](https://www.maplesoft.com/support/help/errors/view.aspx?path=DifferentialGeometry%2FLieDerivative&utm_source=chatgpt.com)

---

# 三十、变分法

| 功能                    | Maple                 | 算法                                   |
| --------------------- | --------------------- | ------------------------------------ |
| Euler–Lagrange        | `EulerLagrange`       | Euler–Lagrange operator              |
| First variation       | `VariationalCalculus` | symbolic variational differentiation |
| Jacobi equation       | `Jacobi`              | second variation / Jacobi equation   |
| Conjugate equation    | `ConjugateEquation`   | conjugate-point calculus             |
| Weierstrass condition | `Weierstrass`         | Weierstrass excess-function analysis |
| Convexity             | `Convex`              | symbolic derivative/Hessian analysis |

[Maple Help：VariationalCalculus](https://www.maplesoft.com/support/help/Maple/view.aspx?path=VariationalCalculus)

---

# 三十一、符号优化

| 功能                   | Maple                  | 算法                              |
| -------------------- | ---------------------- | ------------------------------- |
| 线性规划                 | `simplex[minimize]`    | **Simplex algorithm**           |
| LP feasibility       | `simplex[feasible]`    | simplex feasibility             |
| Pivot selection      | `simplex[pivotvar]`    | simplex pivot selection         |
| Pivot operation      | `simplex[pivot]`       | standard simplex pivot          |
| 标准化                  | `simplex[standardize]` | LP constraint normalization     |
| Basis construction   | `simplex[basis]`       | simplex basis construction      |
| 通用 minimize/maximize | `minimize`, `maximize` | symbolic optimization framework |

Maple 的 `simplex` package 官方明确说它实现整个 **simplex algorithm**，并把 setup、basis、pivot、feasible、minimize/maximize 等步骤分别开放。

[Maple Help：simplex 总览](https://www.maplesoft.com/support/help/Maple/view.aspx?path=simplex&utm_source=chatgpt.com)
[Maple Help：simplex/minimize](https://www.maplesoft.com/support/help/maple/view.aspx?path=simplex%2Fminimize&utm_source=chatgpt.com)
[Maple Help：simplex/pivot](https://www.maplesoft.com/support/help/Maple/view.aspx?path=simplex%2Fpivot&utm_source=chatgpt.com)

---

# 三十二、Maple 符号计算的主要算法骨架

```text
表达式
├── DAG
├── canonical representation
├── type / pattern matching
└── substitution

多项式
├── Euclidean / pseudo-division
├── GCD
├── resultant
├── subresultant
├── square-free
├── modular arithmetic
├── Cantor-Zassenhaus
├── Berlekamp
├── Trager
└── Lenstra

代数系统
├── RootOf
├── algebraic extensions
├── Gröbner
│   ├── Buchberger
│   ├── F4
│   ├── FGLM
│   └── Gröbner Walk
└── Regular Chains
    ├── RegularGCD
    ├── Triangularize
    └── RealTriangularize

实代数
├── VTS
└── CAD
    └── Lazard projection

线性代数
├── Gaussian elimination
├── Bareiss
├── Berkowitz
├── LU
├── modular algorithms
├── Hermite
└── Smith

微积分
├── diff
├── series
├── limit
├── asymptotic series
└── int
    ├── Risch
    ├── Risch-Norman
    ├── Trager
    ├── Parallel Risch
    ├── Gosper
    ├── Elliptic
    └── MeijerG

ODE/PDE
├── classification
├── integrating factors
├── symmetry
├── Kovacic
├── Frobenius
├── formal series
├── Rosenfeld-Groebner
└── Thomas decomposition

离散符号计算
├── Gosper
├── Abramov
├── Abramov-Petkovšek
├── Koepf
├── Zeilberger
├── WZ
├── Ore algebra
└── q-difference

高级代数
├── algebraic curves
├── Puiseux
├── integral basis
├── multivariate power series
├── Hensel
└── Weierstrass preparation
```

以上各块均对应上面实际访问的 Maplesoft Online Help 页面。最关键的几个算法页是 `int/methods`、`Groebner/Basis_algorithms`、`RegularChains/Triangularize`、`QuantifierElimination`、`DifferentialAlgebra/RosenfeldGroebner`、`LREtools`、`QDifferenceEquations`、`OreTools`。
