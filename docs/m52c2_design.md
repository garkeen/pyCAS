# M5.2c-ii 设计文档：塔域 Risch DE 完备判定求解器

**状态**: 设计稿 v1（实现前评审版）
**参考**: FriCAS `intpar.spad` ParametricRischDE（唯一权威参考，不参考 sympy）
**前置**: M5.2c-i（`_rde_tower_solve` K-线性待定系数，仅可积侧）将被本设计替换

---

## 0. 目标与非目标

**目标**: 求解 `D(y) + f·y = g`，y,g ∈ K_j = ℚ(x, t₁..t_{j-1})，三态完备：
- 有有理解 → 返回 y（上游精确验证后 VERIFIED）
- 无有理解 → **proved**（机器可检证据：算法的否定分支）
- 超出理论 → **undecided**（诚实，绝不猜）

**非目标**（明确不做，后续里程碑）:
- 参数化 RDE（FriCAS 求解的是齐次基+特解；我们只需特解——单右端特例）
- 代数核/微分核 case（我们的塔只有 primitive/exp）
- ℚ 之外的常数域

---

## 1. FriCAS 源码地图（file:line，实现时逐条对照）

| 步骤 | FriCAS 位置 | 语义 |
|---|---|---|
| 入口/递归核心 | intpar.spad:1215 `param_rde2` | 视图变量 k = 最高核；一元化；wn→多项式化→分派 |
| **weak normalization** | intpar.spad:920 `normalize` + 1229-1239 调用 | 结式找整数 m 与因子 π：f −= m·D(π)/π，p = Ππ^m；**右端 ×p**；解 ÷p |
| **normal denominator** | intpar.spad:910 `get_denom` + 1406-1410 | d = normalDenom(f)；h 公式见 §3.2；变换 **u = h·y**，方程 ×(d·h) |
| primitive 分派 | intpar.spad:1054 `do_SPDE_prim` | 次数界 n + 修正项 + param_SPDE |
| primitive 逐度下降 | intpar.spad:1009 `do_SPDE_prim0` | b1=b/a 常数时：从高次到低次，**耦合项 (j+1)·dk·s_{j+1}**，低层 RDE |
| exp 分派 | intpar.spad:1175 `do_SPDE_exp` | Laurent order 分析 + 移位 + 界 + param_SPDE |
| exp 逐度（对角） | intpar.spad:1106 `do_SPDE_exp0` | 每度独立解低层 RDE，系数 **b/a + j·η**（exp 专用！） |
| spde 引擎 | intpar.spad:779 `multi_SPDE` / 804 `SPDE1`（intpar RDEaux 包） | a 非常数降次；b 大时贪心消项，**余量≠0 ⟹ 无解** |
| 主循环 | intpar.spad:955 `param_SPDE` | a 常数→b 大/小分支；a 非常数→multi_SPDE |
| normal/special 分解 | intrf.spad:141 `split` | gcd(p,D(p)) vs gcd(p,d/dt p) 的商迭代 |
| 常数线性依赖 | rdeefx.spad:40 `ConstantLinearDependence` | 常数问题的 FriCAS 处理（见 §5） |

---

## 2. 数学总纲

视图：K_j = K_{j-1}(k)，k = t_{j-1}，case = cases[j-1]。
导子 der1: K_{j-1}[k] → K_{j-1}[k]，D(P(k)) = Σ D_K(cᵢ)·kⁱ + P'(k)·dk，
其中 dk = D(k) ∈ K_{j-1}（log: D(arg)/arg；exp: k·D(η)，**表示为 k 乘系数**）。

**关键结构事实**（决定两个 case 的形状差异）:
- primitive 视角: D(k^j) = j·k^{j-1}·dk ⟹ **次数下移，三角耦合**——高次解 s_{j+1} 通过 (j+1)·dk·s_{j+1} 进入低次方程
- exp 视角: D(k^j) = j·η·k^j（η = D(k)/k）⟹ **次数不混合，对角系统**——每度独立

我上次失败的根因：把 exp 的 `f₀ + j·η` 公式用在了 primitive 视角（应只用于 exp0:1138），
且完全遗漏 primitive 的耦合项 (j+1)·dk·s_{j+1}（prim0:1035）。

---

## 3. 算法规格（非参数化特化版）

### 3.0 基例（j==1，K₁ = ℚ(x)）
现有 `_rde_exp_solve`（极点分析，完备判定）直接复用。f 须为 ℚ[x] 多项式
（level-1 频率保证），否则 undecided。

### 3.1 Step 1 — weak normalization（对照 normalize:920）
```
输入 f（RatFunc on K_j）
d  := normalPart(den(f))                    # split(den f, der1).normal
g0 := gcd(d, der1(d)); d0 := d/g0
dd := gcd(d0, g0);       d1 := d0/dd
d2 := den(f)/d1
(a, b) := xgcd(d2, d1) 使 numer(f) = a·d2 + b·d1
r  := Res_z(a − z·der1(d1), d1)             # z 新符号
整数根 m > 0 的每个根: π_m := gcd(a − m·der1(d1), d1)
f_new := f − Σ m·der1(π_m)/π_m
p     := Π π_m^m
g_new := p·g                                 # ★ 右端缩放（sympy 缺失，FriCAS:1237）
```
- 结式/整数根计算若超能力 → undecided（诚实）
- ℚ 常数域上整数根检测精确（已有 _rad_qx 同类逻辑可参考 M5.2c-i 之前的实现）

### 3.2 Step 2 — normal denominator → 多项式方程（对照 get_denom:910 + 1406-1410）
```
d  := normalPart(den(f_new))
en := normalPart(den(g_new))
h  := gcd(en, der1(en)) / gcd(gcd(d,en), der1(gcd(d,en)))    # 多项式商，不整除→undecided
a  := d·h
b  := a·f_new − d·der1(h)
c  := a·h·g_new
```
求解 `a·der1(u) + b·u = c`，u ∈ K_{j-1}[k] 多项式；回代 **y = u/(h·p)**。
（推导验证过：u=h·y 代入原方程恒等成立——FriCAS 1406-1410 的组合）

### 3.3 Step 3 — 分派

#### 3.3a primitive case（对照 do_SPDE_prim:1054 + param_SPDE:955）
```
dk = der1 的 k 系数（= D(k) 在 K_{j-1} 中）；base_case := (j−1 == 0)
da, db, dc := deg(a), deg(b), deg(c)

[分支 A] da == 0 且 db == 0 且非 base:
    b1 := b/a（K_{j-1} 元素）
    b1 == 0 → undecided（纯 ∫c dk；我们的频率方程场景 k·η'≠0 不可达，诚实标注）
    否则 → 逐度下降（对照 prim0:1009）:
        cba := 0（K_{j-1}）; ans := 0
        for jd = deg(c) .. 0:
            rhs := c[jd] − (jd+1)·dk·cba          # ★ 耦合项
            s, st := _rde_solve(b1, rhs, de, j−1)  # 低层递归！
            st == proved → return proved
            st == undecided → return undecided
            ans += s·k^jd; cba := s
        return ok(ans)

[分支 B] 一般情形 → 次数界 + 消项循环（对照 1078-1104 + param_SPDE:955）:
    n := db > da ? max(0, dc−db) : max(0, dc−da+1)
    # da=db+1 与 da=db 的界修正（FriCAS 1081-1100）【简化：跳过】
    #   理由：修正只收紧界（效率），松界仍是有效上界，正确性不受影响。
    #   标注：SIMPLIFICATION-1
    若 deg(c) > n + deg(a) 相关上限不可行 → proved
    循环（对照 param_SPDE + multi_SPDE）:
        deg(a) == 0:
            b ≠ 0 且 (base 或 deg(b) > max(0, deg(dk)−1)):
                SPDE1 贪心消项（对照 SPDE1:804）:
                    while c ≠ 0:
                        m := deg(c) − deg(b); m < 0 → 余量 r := c
                        qq := lc(c)/lc(b)·k^m; c −= b·qq + der1(qq); u += qq
                    r ≠ 0 → return proved        # ★ 余量即否定证据
            否则（b 小）: → undecided【简化：SIMPLIFICATION-2，见 §4】
        deg(a) > 0:
            multi_SPDE 一步（对照 779-802）:
                (s,t,ggen) := xgcd(a, b) 使 s·a + t·b = ggen
                ggen ≠ 1 → 公因子情形：c/ggen 整除性检查，失败→proved；
                            a/=ggen 相关归约后递归【对照 DSOL 分支】
                否则: c_new := s·c + b·(c div t·a 的商) − der1(余)…
                      （严格照 787-794 公式抄）
                b += der1(a)；继续循环（a 不变，次数守恒，终止由界 n 保证）
```

#### 3.3b exp case（对照 do_SPDE_exp:1175 + exp0:1106）
```
η := D(k)/k ∈ K_{j-1}（k 乘系数形态）
[分支 A] deg(a)=deg(b)=0 且 b 无 k 负幂（ord(b)=0）:
    f0 := b/a
    for jd = deg(c) .. 0:                       # 对角！每度独立
        s, st := _rde_solve(f0 + jd·η, c[jd]/a, de, j−1)   # ★ exp 专用公式
        st ≠ ok → return st
        ans += s·k^jd
    return ok(ans)

[分支 B] 一般情形（b 含 k 幂/Laurent）:
    nb0 := ord(b)（最低 k 次数，Laurent）
    n0 下界判定（对照 exp_lower_bound:1147）:
        c0 := b 的 k⁰ 系数 / a 的 k⁰ 系数（相应 order 处）
        ν := c0/η；ν ∈ ℚ 常数？（ℚ 域精确判定）→ n0 修正
        【ℚ 之外/非常数 → 用保守界，不报错——FriCAS 同款姿态】
    n0 < 0 → b += n0·η·a（移位，对照 1188）
    Laurent 多项式化（负幂乘 k^(−nb0)，对照 1189-1192）
    n1 上界（对照 exp_upper_bound:1160，同款 ν 判定）
    deg(c) > n1 → return proved                 # ★ 界否定
    对 [max(0,?) .. n1] 每度独立解（同分支 A 对角循环）
```

### 3.4 回代与验证
```
y = u / (h·p)     # 除回 wn 乘子与 h
精确验证: D(y) + f_orig·y − g_orig ≡ 0（塔上导数 + 分子 is_zero，现有通道）
验证失败 → 内部错误断言（不应到达；到达则报 bug 而非静默）
```

---

## 4. 简化清单（诚实标注，每条附安全论证）

| # | 简化 | 安全性论证 |
|---|---|---|
| S-1 | 跳过 da=db+1 / da=db 的界收紧修正（FriCAS 1081-1100） | 修正只减小 n；松界仍是正确上界 ⟹ 只影响效率（线性系统更大），不影响判定正确性 |
| S-2 | primitive b 小分支（param_SPDE 的 do_degrad 路径）→ undecided | FriCAS 该路径递归低层积分右端；我们频率方程场景 b=k·η' 在 primitive 视角 da=db=0 恒走分支 A，分支 B 的 b 小仅当 deg(b) ≤ max(0,deg(dk)−1)——可能到达（如 f 常数、dk 非常数）。诚实 undecided 不误判 |
| S-3 | 不实现参数化（多右端/齐次基） | 我们只需特解；单右端时 FriCAS 的 nullSpace 组合退化为直接检查 |
| S-4 | exp 分支 B 的 ν 判定仅限 ν ∈ ℚ | 常数域就是 ℚ；超出的情形用保守界 ⟹ 可能 unsupported 但绝不误判 |
| S-5 | b1==0（primitive 分支 A）→ undecided | 频率方程 f=k·η'≠0 ⟹ 不可达；其他调用方未来需要时再实现 |

**无简化**的部分（完整实现）: weak normalization 全链、normal denominator 全链、
primitive 逐度下降（含耦合项）、exp 对角求解（含 Laurent 移位）、
SPDE1 贪心+余量否定、multi_SPDE 公因子情形、所有 proved 分支。

---

## 5. 常数问题（Richardson）的忠实处理

出现位置与策略（ℚ 常数域内全部精确可判）:
1. wn 的结式整数根 → ℚ 上精确
2. exp 界的 ν = c0/η 判定 → ν ∈ ℚ 精确；否则保守界（S-4）
3. 线性系统求解 → ℚ 上高斯消元精确

**未来引入符号常数时**: 位置 2 会变成"无法判定 ν 是否常数/整数"——
届时输出 `RischUnsupported("undecidable: cannot decide whether constant C/η ∈ ℤ")`。
本里程碑在代码中预留该分支的异常类型与消息模板。

---

## 6. 测试矩阵（实现完成的验收标准）

| 输入 | 期望 | 判定路径 |
|---|---|---|
| `exp(x)*log(x)` | **NOT ELEMENTARY (proved)** | prim 视角下降：round1 s₁=1；round0 D(s)+s=−1/x 无有理解（Ei）⟹ proved |
| `exp(x)*(1/x + log(x))` | = eˣ·log x [VERIFIED] | 同路径 round0 rhs=0 → s₀=0，u=ℓ ✓ |
| `exp(-x^2)` | NOT ELEMENTARY (proved) | 不退化（现有路径） |
| `exp(x)` | VERIFIED | 不退化 |
| `exp(x)*x^2` | VERIFIED | 不退化 |
| `log(log(x))/x` | = log·log(log)−log [VERIFIED] | M5.2b 验收不退化 |
| 445 全量测试 | 全绿 | 无回归 |
| eˣ·sin x 相关 | 本里程碑不做（M5.3） | — |

**手工推演已验证**前两行（见对话记录）：算法在两个场景给出正确且相反的判定，
且判定差异来自 round0 方程 D(s)+s=−1/x 的可解性——这正是 Ei 成分的代数化。

---

## 7. 实现顺序（每步跑测试）

1. der1 导子在 ℚ(K_{j-1})[k] 上的实现 + split normal/special（对照 intrf.spad:141）
2. Step 1 wn + Step 2 多项式化（单元测试：eˣ·log x 场景中间量对照手推值）
3. primitive 分支 A（逐度下降）→ 测试矩阵前两行
4. exp 分支 A（对角）+ 分支 B 简版
5. 分支 B 的 SPDE1/multi_SPDE + proved 分支
6. 接线 `_exp_freq_part`（新签名 (y, status)）+ 全量回归
7. notes.md 记录 + 提交
