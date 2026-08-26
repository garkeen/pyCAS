# reference.md — 参考实现索引

本项目（CAS/）的算法与架构参考源码位于上级目录 `D:\code\python\pyCAS\`。**主要权威参考：Maxima 与 FriCAS**。查算法语义、判定流程、边界行为时，先读这两个；其余四个为次要参照。

## 主要参考

### maxima/ — Maxima（Common Lisp，Macsyma 血统）

完整发行版源码树。核心算法集中在 `maxima/src/*.lisp`：

| 文件 | 内容 | 对应 v3 层 |
|---|---|---|
| `src/risch.lisp` | Risch 指数-对数积分主循环 | 六.2 不定积分 |
| `src/sinint.lisp`, `src/sin.lisp` | 三角函数换元积分 | 五 函数结构 |
| `src/defint.lisp` | 定积分入口与分派 | 六.3 定积分协议 |
| `src/limit.lisp` | 极限计算 | 六.5 极限 |
| `src/factor.lisp` | 多项式因子分解 | 四 多项式机器 |
| `src/csimp.lisp`, `csimp2.lisp` | 化简主循环 | 七 判定与验证 |

会话与求值骨架在 `src/suprv1.lisp`。

### fricas/ — FriCAS（Scratchpad II 血统，Spad 语言）

代数库按数学范畴分层，全部在 `fricas/src/algebra/*.spad`：

| 文件 | 内容 | 对应 v3 层 |
|---|---|---|
| `algebra/poly.spad`, `polycat.spad`, `multpoly.spad` | 多项式范畴与域 | 三 数域系统 / 四 |
| `algebra/gdpoly.spad` | ℚ 上 GCD/Hensel 型分解 | 四 公共算法机器 |
| `algebra/intef.spad`, `defintef.spad` | 初等函数 Risch 积分（EF 体系） | 六.2 |
| `algebra/rdeefx.spad`, `grdef.spad` | RDE 求解器族 | 六.2 RDE 核心 |
| `algebra/intalg.spad` | 代数数/代数函数域上的积分 | 三 数域系统 |
| `algebra/expexpan.spad` | 指数塔展开 | 五 函数结构 |
| `algebra/limitps.spad`, `mrv_limit.spad` | 极限（级数法/MRV） | 六.5 |
| `algebra/sum.spad` | 级数求和 | 六.6 求和 |

FriCAS 的**域参数化体系**（Category → Domain → Package）是 v3 数域投影设计（三 数域系统：ℚ→i(α) 塔、CANONICAL/FORMAL/BRANCHED 状态声明）的直接原型。

## 使用纪律

1. **抄语义不抄代码**：参考实现在 Lisp/Spad 上，v3 是 Python + 驻留项层。对照它们的判定顺序和分支条件，不搬数据结构。
2. **先 v3 后参考**：`docs/cas_v3_arch.md` 的裁定优先。参考实现里与本裁定冲突的行为（如 L0 隐式折叠、数值采样判等），一律以 v3 为准。
3. **边界行为取证**：遇到"这个积分该不该出条件解"类问题时，去参考实现里找同名输入的实际行为作为证据。

## 次要参照（同目录下另有）

- **expreduce/** — Common Lisp 规则重写 CAS，规则组织方式可参照
- **mathics-core/** — Mathematica 语法的 Python 实现，语法兼容层参照
- **yacas/** — C++ 轻量 CAS，工程结构参照
- **SAINT/** — Macsyma 前身，历史价值
