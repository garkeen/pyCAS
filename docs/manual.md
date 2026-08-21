# pyCAS 用户手册

pyCAS 是一个**从零实现的自包含纯符号计算机代数系统**（Python，运行时零依赖）。
定位：**交互式、通用、诚实**——可判定的片段内给精确结果，片段外明确拒答，
绝不静默给出未经验证的答案。

```
cd CAS
python -m cas          # 启动 REPL
python -m pytest tests/  # 运行全部测试（300+ 用例）
```

---

## 1. 核心哲学（读结果前先懂这三条）

1. **精确**：任意大整数、精确有理数，无浮点。`1/3 + 1/6 = 1/2` 精确成立。
2. **诚实三态**：一切判定/验证返回 `YES / NO / UNKNOWN`（或对应的
   `VERIFIED / PROBABLE / UNVERIFIED`）。判不动就说判不动，不猜。
3. **步骤即数据**：每次规则应用与内核算法调用都记入 step log（`:steps` 查看）；
   整个会话可保存为文本脚本并逐条回放（§6）。

结果尾部的状态标记含义：

| 标记 | 含义 |
|---|---|
| `[VERIFIED]` | 结果经符号回验（如积分回微分）确证 |
| `[PROBABLE]` | 数值采样支持但符号未证（探测器，不是证明） |
| `[UNVERIFIED]` | 未能验证（结果仍给出，诚实标注） |
| `UNKNOWN` / `unsupported` / `honest refusal` | 拒答（附原因） |
| `DIVERGES` | 发散（反常积分判敛结论） |

---

## 2. 表达式语法

```
变量      x, y, a1, ...（单小写字母保持原样，多名首字母大写为函数头）
常数      pi  e  i  true  false
运算符    +  -  *  /  ^（右结合：2^3^2 = 512；-x^2 = -(x^2)）
比较      = 或 ==  !=  <  <=  >  >=
逻辑      &&  ||  not
函数      sin cos tan atan arcsin arccos exp log abs sinh cosh tanh
          sqrt(x) = x^(1/2)；piecewise(v1, c1, v2, c2, ...)
绑定词    integrate(f, x)   —— 惰性积分（名词形式，可被 :parts/:value 操作）
引用      'expr             —— 真 hold（跳过 mk 规范化，保留反化简形与域约束）
历史      %  %N             —— 最近/第 N 个历史产出（嵌入乘法自动补括号）
```

构造即规范化：输入在构造时即归一（合并同类项、同底幂合并、特殊点折叠如
`sin(0)=0`、`i^2=-1`、`e^a` 与 `exp(a)` 同一）。因此 `x/x = 1` 在构造时成立
（generic 语义，定义域条件可用规则义务化处理）。**例外：`'expr`（quote）跳过
mk 规范化**——保留反化简形（`'cos(x)/cos(x)^2` 不被合并）、借用形与域约束
（`'ln(x-k)/ln(x-k)` 保 `x-k>0`，不被消成 1 丢域）；`:value` 脱壳 release。

---

## 3. REPL 快速上手

输入分三层，语法即语义：

| 语法 | 层 | 语义 |
|---|---|---|
| 无前缀 | **表达式** | 输入数学表达式成为当前式 |
| `:` | **手动操作** | 逐步可控，每步入账 step log，可 `:u` 撤销，可 `:steps` 解释 |
| `!` | **自动求解** | 算法黑盒直出，verify 背书，step log 只记算法名+验证态 |

```
>> x + sin(-x)
x - sin(x)                     # 表达式 → 当前式
>> :a sin_neg                  # 手动：建议并应用规则
>> !limit sin(x)/x x 0         # 自动：算法直出 → 1
>> :steps                      # 查看推导步骤（: 手动每步可解释）
>> :u                          # 手动：撤销上一步（可 :u 3）
```

### 3.1 化简与规则

| 命令 | 作用 |
|---|---|
| `:s [path]` | 建议当前式（或指定位置）可用的规则 |
| `:a <rule-id> [path]` | 应用规则（不给 path 自动全式搜索） |
| `:auto` | 自动重写循环（防振荡，每步入账） |
| `:rule id = lhs -> rhs [guard g] [as dir] [prio n] [auto]` | 会话内联定义定理 |
| `:unrule id` | 删除会话规则（文件规则不可删） |
| `:rules` | 列出全部规则（origin/prio/guard/方向） |
| `:refine` | 账本驱动化简（如假设 x>0 时 abs(x)+sqrt(x^2)+exp(log(x)) → 3x） |
| `:value` | 名词→动词：脱壳 release（`'expr` 走规范形）/ 惰性积分实算 / D 名词微分 |

### 3.2 假设与推理

| 命令 | 作用 |
|---|---|
| `:assume x>0` | 事实入账本（带域闸门与矛盾检测） |
| `:declare n integer` | 声明属性（integer/positive/negative/even/odd/real） |
| `:ctx` | 查看账本 |
| `:obls` / `:ans <oid> <fact>` | 义务队列（条件不足时不阻塞，事后作答重放） |

矛盾即锁：`:assume a>0` 后 `:assume a<0` → 会话冻结并报告矛盾链；
撤销引发矛盾的步可解锁。

### 3.3 自动求解（! 前缀，算法黑盒直出 + verify 背书）

**代数**
```
!factor x^4-1                # Zassenhaus 因式分解
!solve x^2 - 5*x + 6 = 0 x   # 方程（低次/有理根/参数低次/主支逆）
!solveset x^2 = 1 x          # 解集一等结构：x in {-1, 1}；不等式给区间并
!solveineq x^2-1 > 0 x       # 一元多项式不等式（Sturm）
```

**微积分**
```
!integrate 1/(x^2-1)         # 不定积分（报所用方法 + 验证态）；多变量须给变量: !integrate f x
!defint sin(x) x 0 pi        # 定积分（自动正向换元 + 奇点拆分 + 判敛 + 分段）
!defint 1/x^2 x 1 inf        # 无穷限反常积分（收敛/发散判定）
!limit sin(x)/x x 0          # 极限（point 可为 inf/-inf）
!series exp(x) x 0 4         # Taylor 展开 + O 项
!verify F x f                # 微分回验：D(F) == f ?
```

**求和/差分**
```
!sum k^2 k                   # 不定求和（Faulhaber 幂和，差分回验）
!sum k^2 k 1 10              # 定界求和（S(hi) - S(lo-1)，数值/符号上界均可）
!sum 1/(k*(k+1)) k           # Gosper 裂项求和（有理函数超几何项）
!sum 1/(k*(k+2)) k 1 10      # 完整 normal form 裂项（z 有理函数）
```

**线性代数**
```
!mat [[1,2],[3,4]]           # 显示矩阵
!mdet / !mrank / !minv / !msolve [[a,b],[c,d]] [e,f]
!charpoly / !eigenvalues / !eigenvectors
```

**ODE**
```
!dsolve D(y,x) + y = exp(x) y x      # 一阶线性（积分因子）
!dsolve D(y,x) = x*y y x             # 可分离/线性自动分类
!dsolve D(D(y,x),x) + y = 0 y x      # 二阶常系数齐次（特征方程，复根三角实形式）
```
导数写作 `D(y,x)`、`D(D(y,x),x)`；解含积分常数 `C1`、`C2`；
每个解都回代微分回验（`[VERIFIED, kind: ...]` 标注题型与验证态）。

### 3.4 手动结构操作（: 前缀，逐步可控）

**子项手术（path 寻址一等公民）**
```
:tree                            # 带路径的子项树（选择器；Eq 两侧 = path 0 / 1）
:set 0.1 x                       # 直接子项手术：ln(e^x) -> x（equivalent 三态闸门：
                                 #   VERIFIED/PROBABLE 提交，UNKNOWN/NO 拒绝；
                                 #   换入项新引入的定义域约束记 proviso）
:rsub ln(e^x)=x                  # 全式结构替换（old 未出现报 not found）
```

**等式双侧操作（Maxima eqnflag / Mathematica 等式算术的显式命令化）**
```
:add_both <t> / :sub_both <t>    # 两边加/减；t 的定义域照常闸门：
                                 #   加 ln(x-k) 记 proviso x-k>0（解集收窄绝不静默），
                                 #   与账本矛盾即拒绝；借用形用 quote: :add_both 'ln(x-k)-ln(x-k)
:mul_both <t> / :div_both <t>    # 两边乘/除（除法域闸门含 t!=0）
:neg_both / :swap                # 两边取负 / 交换两侧
:zero_form                       # L = R -> L - R = 0（喂 !solveineq 前的规范形）
:apply_both <fn>                 # 两边应用一元函数：域 proviso + 单射性诚实分级
                                 #   （spec.injective 声明：非单射提示"仅正向蕴含"）
```

**变形工具箱（反向化简/凑形；目标为等式时自动作用两侧）**
```
:expand [path]                   # 展开乘积/幂
:extract <f> [path]              # 提公因子 ab+ac -> a(b+c)（整除检查 + 回验背书）
:separate [path]                 # (a+b)/c -> a/c + b/c（:together 的对偶）
:complete_square <var> [path]    # 配方 a x^2+bx+c -> a(x+h)^2+k
:subst x=h(t)                    # 正向替换（term 层）
:mulfrac cos(x) / :divfrac x^2   # 分子分母同乘/同除（凑形，域 proviso）
:apart 1 (x^2-1)                 # 部分分式
:together / :collect <var> / :numerator / :denominator / :coefficient <var> [k]
```

**微积分战术**
```
:usub t=cos(x)                   # 正向换元（惰性积分）：精确微分分解优先，
                                 #   主支逆退化（两级策略，note 标注所走路线）；
                                 #   经典条件 g'!=0 由后续 !verify 微分回验背书
:bsub x=sin(t) sqrt(1-x^2) x 0 1 # 反向换元（三角代换，新限主支逆解）
:parts sin(x)                    # 分部积分（人选 u，输出 u/dv/du/v 明细）
:solveq integrate(exp(x)*sin(x), x)  # 复合未知项线性求解（循环分部）
:lhop x 0                        # 手动洛必达一步（须 0/0 或 ±∞/±∞，否则拒绝并报告
                                 #   两端极限；G'!=0 经典条件由最终求值背书）
:isteps 2*x*exp(x^2)             # 积分策略步树（只分类不计算）
:intro_eq I                      # 等式链提取：Eq(命名项, 当前式)（循环分部收尾，
                                 #   配合 :solveq I 按名解出；[loop] 提示自动announce）
:fold                            # 线性折叠：∫c·g -> c·∫g（倍数/负号起点的循环归一，
                                 #   I := ∫-f 时循环再现的是 -I，先 :fold 再 :intro_eq）
:add_sub ln(x-k)                 # 加零凑形 A -> A + t - t（quote 借用形保结构；
                                 #   t 的定义域创建义务，等式提取前须结算）
```

**等式链与守卫（立场）**：计算即等式链——step log 每步 before->after 都是一条
等式，`:intro_eq <lhs|%N>` 把链上任意节点与当前式连成方程。**派生等式的守卫 =
链上所有步骤条件的合取**：域条件在操作时创建义务（`:obls`），守卫未决时
`:intro_eq` 硬闸门拒绝（机器知道的守卫不允许蒸发），`:ans` 结算入账后建立——
此后守卫以账本事实 + 等式项自身 dom_condition 双重载体随行，消费时随账本走。
账本等式在守卫下对称使用安全（decide 相对整个账本判定）；有方向的是非等价
变换（平方/乘零因子）——它们以 step+proviso 存在，从不进账本当 Eq。

### 3.5 输出

```
:latex                       # 当前式的 LaTeX
:hist                        # 历史产出列表（%N 引用）
:log                         # 原始 step log
:steps                       # 可解释步骤
```

---

## 4. 工作流示例

### 4.1 循环分部积分 ∫eˣsin x dx（人机协作全程）

```
>> I := integrate(exp(x)*sin(x), x)     # 定义惰性积分为 I
>> I                                     # ∫[exp(x)*sin(x)] dx（名词）
>> :parts sin(x)                         # 人选 u=sin x，机器算 dv/v/du
>> :parts cos(x)                         # 再次分部；[loop] 提示 I 循环再现
>> :intro_eq I                           # 等式链提取：I = 当前式（机器写方程）
>> :solveq I                             # 解出 I = .../2
>> !verify % x exp(x)*sin(x)             # VERIFIED
```

计算即等式链：step log 每步的 before -> after 都是一条等式，`:intro_eq` 把
"链首命名项 = 当前式"提取为一等方程。循环检测由驻留指针完成（`:parts` 把
常数符号拉出绑定体，保证循环再现的积分名词与链首驻留同一）。
也可手写方程（`I = e^x*sin(x) - e^x*cos(x) - I`）——断言自由但结论仍由 verify 把关。

### 4.2 定积分画廊

```
>> !defint (e^x+x)*(e^x+1) x 0 1    # 正向换元 u=e^x+x（新限正向求值，不求逆）
1/2*(exp(1) + 1)^2 - 1/2   [VERIFIED, method: u-substitution u=x + exp(x)]
>> :bsub x=sin(t) sqrt(1-x^2) x 0 1 # 反向换元（√(cos²t) 经符号窗口脱壳）
1/4*π   [VERIFIED, method: backward substitution x=sin(t): ...]
>> !defint 1/x x 1 inf               # 判敛
DIVERGES: improper integral diverges at infinity
>> !defint piecewise(x-1, x >= 1, 1-x, true) x 0 2   # 分段积分
1   [VERIFIED, method: piecewise: branch split + midpoint selection]
```

### 4.3 会话定理 + 假设化简

```
>> :rule cube_sum = ?x^3 + ?y^3 -> (?x+?y)*(?x^2-?x*?y+?y^2)
>> a^3 + b^3
>> :a cube_sum            # (a + b)*(a^2 + b^2 - a*b)
>> :assume a > 0
>> abs(a) + sqrt(a^2) + exp(log(a))
>> :refine                # 3*a
>> !solveset x^2 = 4 x    # x in {-2, 2}
>> :latex                 # LaTeX 输出
```

### 4.4 手动解方程全程（配方路线，每步入账可撤销）

```
>> x^2 + 4*x = -3
>> :add_both 3                    # x^2 + 4*x + 3 == 0
>> :complete_square x             # (x + 2)^2 - 1 == 0   （等式线程：LHS 配方）
>> :add_both 1                    # (x + 2)^2 == 1
>> :apply_both sqrt               # 主支开方（sqrt 单射性未声明，诚实提示）
>> :sub_both 2                    # x = -1（主支；负支可 :neg_both 后重试）
>> :tree                          # 全程路径可见，:u 可逐步回退
```

---

## 5. 规则 DSL（定理库）

规则文件位于 `rules/*.rules`，会话启动自动加载；`:load` 热重载。
语法（与 `:rule` 内联语法一致）：

```
rule <id> = <lhs> -> <rhs> [guard <条件>] [as <方向>] [channels a,b] [prio N] [auto]
```

- 洞：`?x` 单参、`??r` 序列、`?x::num` 类型洞（num/int/rat/sym/const/expr）；
- `guard` 走三值判定：YES 应用 / NO 跳过 / UNKNOWN 记义务不阻塞；
- `as expand|combine` 方向标签成对呈现；`prio` 小者先试；
- `auto` 标记的规则进 `:auto` 通道（仅限无条件安全的定理）。

**三分边界**（什么进哪里）：表示归并（如 x+x→2x）在构造器，不进规则库；
定理（恒等式、带条件推导）进规则文件；过程性算法（因式分解、消元、积分）
在内核代码，正确性由 verify 通道背书。

新增函数的正确姿势 = 在 `cas/spec.py` 注册 FunctionSpec（导数/打印名/奇偶/
特殊点/定义域/原函数/逆函数/数值层一次配齐）+ 必要时写规则文件。
**禁止**在 diff/pprint/decide/domain 等消费者模块为新函数加 if 分支。

---

## 6. 转录 DSL：可保存、可回放的推导

每条变更命令自动记入会话转录。`:save path.pycas` 保存、`:replay path.pycas`
在新会话逐条重建——回放与交互走**同一代码路径**，头部规则指纹不匹配即拒绝
回放（永不静默错），驻留项保证回放产物与原产物指针同一。

`examples/` 目录有六个成品案例（均由测试回放断言）：

| 文件 | 内容 |
|---|---|
| `01_cyclic_parts.pycas` | ∫eˣsin x 循环分部完整推导（verify 收尾） |
| `02_defint_gallery.pycas` | 定积分四形态（正向换元/嵌套换元/判敛/分段） |
| `03_rules_refine_sets.pycas` | 会话定理 + refine + 解集 + LaTeX |
| `04_ode_bsub.pycas` | ODE 分类求解 + 反向换元 |
| `05_trig_half_angle.pycas` | ∫1/(a+b·cos x) tan 半角代换 + 参数 proviso |
| `06_sec_manual_substitution.pycas` | ∫sec x 手动 sin-代换全程（:set 绑定体内手术 + :usub 精确微分 + 账本背书回代） |

`#` 开头的行是注释，回放时跳过——案例文件本身就是可读的推导文档。

---

## 7. 能力边界（诚实清单）

**能做**：多项式全套（gcd/因式分解/结式/判别式）、ℚ(params) 全参数化系数域
（参数积分判式分类 + proviso）、有理函数积分（Hermite+RT，完备）、三角/双曲
有理式积分、极限（含 ±∞）、Taylor 级数、定积分（含换元/分段/反常判敛/
对称性预检：任意区间中点反射奇偶 + spec.period 周期折叠）、
ODE 四题型、方程求解（低次/参数低次/主支逆）、矩阵与谱、Sturm 不等式、
代数数 ℚ(α)、求和（Faulhaber 幂和 + Gosper 有理函数不定/定界求和）。

**明确不做/拒答**：数值模拟与浮点计算（数值层只做验证抽查）；超越函数零等价
的不可判定情形（Richardson 定理）；无初等原函数的定积分特殊方法
（Dirichlet/Gaussian 类需参数微分/围道等符号技巧，远期；系统无数值通道，
无原函数即拒答——绝不以数值近似冒充验证）；无初等原函数的不定积分
（如 ∫e^{-x²}，需要特殊函数，远期）；周期族通解（主支解带标注）；无理根端点的精确区间集。

**远期路线**：M4 求和/差分（Gosper）→ M5 Risch 分期 → ODE 扩展
（非齐次/常系数系统）；结构债：RootOf 复根隔离、Gröbner 基（多元方程组）。
架构设计见 `docs/cas_v2_arch.md`；修订裁定与调研教训见 `docs/notes.md`。
