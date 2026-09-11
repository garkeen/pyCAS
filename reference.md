# reference.md — 参考实现索引

本项目（CAS/）的算法与架构参考源码位于上级目录 `D:\code\python\pyCAS\`。**主要权威参考：Maxima 与 FriCAS**。查算法语义、判定流程、边界行为时，先读这两个；其余四个为次要参照。

裁定优先级：**本系统裁定（`cas_v4_arch.md` + `AGENTS.md`）高于参考实现行为**。参考实现里与本系统裁定冲突的做法（如 L0 隐式折叠、数值采样判等），一律以本系统裁定为准。

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

1. **抄语义不抄代码**：参考实现在 Lisp/Spad 上，本系统是 Python + 驻留项层。对照它们的判定顺序和分支条件，不搬数据结构。
2. **先本系统裁定后参考**：`cas_v4_arch.md` 与 `AGENTS.md` 的裁定优先；参考实现只是语义证据来源。
3. **边界行为取证**：遇到「这个积分该不该出条件解」类问题时，去参考实现里找同名输入的实际行为作为证据。

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
- **SAINT/** — Macsyma 前身，历史价值
