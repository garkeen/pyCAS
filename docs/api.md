# pyCAS API 参考（数据结构 + 全部 API）

> 对应架构：`docs/cas_v2_arch.md`；使用教程：`docs/manual.md`。
> 本文档只讲"有什么、怎么用"。状态与代码同步（M3 收尾）。

---

## 0. 模块分层总览

```
L7  策略      integrate.py(策略入口) · istrategy.py(步树) · bsub.py(反向换元) · ode.py
L6  会话      session.py · parser.py · pprint.py · latex.py
L5  化简      simplify.py（显式栈重建 + cost）· refine.py（账本驱动）
L4  上下文    context.py · decide.py · domain.py
L3  领域      spec.py(注册表) · poly/factor/apart/ratfunc/algnum/sturm ·
              solve/matrix/ineq/sets/ops · trig · diff · series/limits · integrate
L2  规则      rules.py · loader.py · rules/*.rules
L1  匹配      match.py
L0  项        term.py · errors.py
横切          evalnum.py（数值求值，仅验证/抽查通道）
```

---

## 1. 核心数据结构

### 1.1 Term 类族（term.py，L0）

不可变、**构造即规范化**（mk 是唯一构造入口：AC flatten + 全序 + 常量折叠 +
环规范化 + 特殊点折叠），等项 = 指针同一（驻留，内容寻址）。

| 类 | 含义 |
|----|------|
| `Sym(name)` | 符号，构造器 `S(name)` |
| `Const(name)` | 常量（pi/e/i/gamma），构造器 `C(name)` |
| `Int(v)` / `Rat(f)` | 大整数 / 精确有理数，构造器 `N(v)` |
| `Special(name)` | TRUE/FALSE/UND/INFINITY/EMPTY_SET |
| `BVal(val)` | 布尔值（true/false，Piecewise 条件用） |
| `DB(i)` | de Bruijn 哑变量索引（Bound 内部） |
| `PatVar(name, pred)` | 单参洞 `?x`（可带类型洞 `::pred`），构造器 `PV` |
| `PatSeq(name)` | 序列洞 `??x`，构造器 `PS` |
| `Expr(head, args)` | 函数应用；构造器 `mk(head, args)` / `fn(name)` |
| `Bound(hint, body)` | 绑定词节点（∫/Σ/Π/lim 哑变量，de Bruijn 体，α 等价） |

**构造器/工具速查**：
`S/C/N/PV/PS/mk/fn/plus/times/pw/neg/div/sqrt/exp/sin/cos/tan/eq/lt/le/gt/ge/ne/
quote/mk_bound/open_bound/subst/instantiate/term_at/replace_at/all_paths/
free_vars/is_num/num_val/sort_key`。

关键语义：
- `mk`：规范化构造（环层：同类项合并/同底整数幂合并/幂归约；`e^a`→Exp(a)；
  i 幂 mod 4 折叠；Conjugate/Piecewise 走 `register_norm` 注册表）。
- `subst(t, mapping)`：显式栈替换，**复合项键可命中**（如 {x²: z}），α 躲避。
- `open_bound(b)`：Bound → (hint 符号, 体)（DB 还原，mk_bound 的逆）。
- 常量：`ZERO/ONE/MONE/TWO/PI/E/IU/UND/INFINITY/EMPTY_SET/TRUE/FALSE`。

### 1.2 T3 三值（decide.py）

`T3` 枚举：YES / NO / UNKNOWN / **PROBABLE**（数值采样支持，不进 YES 通道）。
Kleene 组合 `and3/or3/not3`。

### 1.3 Context（context.py，L4）

有序账本 `Entry(fact, kind, origin)`；`check_and_assume(fact, origin, kind)` 为
统一入账闸门（域检死 → 矛盾锁 → 入账）→ `(T3, why)`；`clone/branch/mark/
rollback/drop_origin`。

### 1.4 规则引擎（rules.py，L2）

| 类型 | 字段 |
|------|------|
| `Rule` | id, pattern, template, guard, direction, channels, auto, origin, priority |
| `Step` | sid, rule_id, path, before, after, guard, dcost, note（step log 一等数据；算法步 note 记 algorithm=...） |
| `ApplyResult` | ok, guard, term, subst |

`RuleSet`：`add/remove/for_term(t)`（per-head 索引 + priority 排序）。
`apply_rule(rule, expr, path, guard_eval=None, budget)`：匹配 → 守卫 3VL → 实例化。

### 1.5 FunctionSpec（spec.py，L3 地基）

```python
FunctionSpec(name, arity, print_name, parity, deriv, bound, dom,
             special, numeric, anti, inv)
```
消费者：mk（special 折叠）/ diff（deriv）/ decide（bound 公理）/ domain（dom）/
pprint·latex（print_name）/ evalnum（numeric）/ integrate（anti，含线性复合）/
solve·bsub（inv 主支逆）/ loader（gen_rules 奇偶规则 origin='spec'）。
已注册：Sin/Cos/Tan/Atan/Arcsin/Arccos/Exp/Log/Abs/Sinh/Cosh/Tanh。
`SPECS` 字典 + `get(name)`；纪律：新函数只写 spec + 规则文件。

### 1.6 Session（session.py，L6）

状态 = current + log(Step[]) + obligations + ctx + rules + history + transcript +
defs + kernel(KernelCmd 注册表)。入口：`handle(line)`（REPL 与回放同路径）；
`run()` 启动 REPL。转录：`save_transcript/replay_file/rules_fingerprint`
（会话规则不计指纹，由转录自重建）。

---

## 2. 全部模块 API

### 匹配与规则（L1–L2）
- `match.matches(pat, tgt, sub=None, budget)`：结构 + AC 归并 + 类型洞 + OneIdentity。
- `loader.parse_rule_line/parse_rules/load_dir`；DSL：
  `rule id = lhs -> rhs [guard c] [as dir] [channels a,b] [prio N] [auto]`。

### 上下文与判定（L4）
- `decide(fact, ctx)`：管线 semantic → ledger → interval → derive → axiom → UNKNOWN。
- `equivalent(a, b, ctx=None, budget)`：统一判等（指针 → 归零 → 三角层 →
  账本/多项式片段 → 采样 PROBABLE → UNKNOWN）。
- `eval_guard(guard, sub, ctx)` / `contradicted(fact, ctx)` / `satisfiable(cons, ctx)` /
  `domain_ok(fact, ctx)` / `dom_condition(t)`（domain.py）。
- `@derive(name, applies)` / `@axiom`：注册式扩展（decide.py）。

### 化简（L5）
- `simplify(t, budget)`：显式栈重建（记忆化 _MEMO；exp 加法定律合并：
  exp(a)·exp(b)→exp(a+b)、Exp(a)ⁿ→Exp(n·a)，化简层无条件恒等）。
- `cost(t)` / `expand(t)`（均显式栈）。
- `refine.refine(t, ctx)` → (新项, changed)：只重写 decide=YES 的结构
  （|x|、√(x²)、exp(log x)、Piecewise 分支裁剪/选定）。

### 展示（L6）
- `parse(s)`；`pprint.to_str(t, prec=0)`（显式栈；O(..)/piecewise/集合头/绑定词渲染）；
  `latex.to_latex(t)`（\frac/\sqrt/幂/三角/积分/分段/集合）。

### 多项式与代数数（L3）
- `Poly`：`from_term/to_term/+-*/scalar/deriv/degree/lc/content/primitive/udivmod/is_monic`。
- 顶层：`ugcd`（单变量）/ **`mgcd`（多元，原始伪除 PRS + 递归 content）** /
  **`div_exact`**（精确除法）/ `uresultant` / `udiscriminant`。
- `factor.factor(p)` → (content, [(因子, 重数)])（Zassenhaus）；`squarefree_decomp`。
- `apart.apart(f, g, x)` → (q, [(num, den, k)])。
- `RatFunc`：互素规范形（构造时约分，多变量走 mgcd）。
- `algnum`：`RootOf(m, idx)`、ℚ(α) 算术（qa_*）、`tr_power_sums/tr_eval`（迹）、
  `real_isolation(m)`（Sturm 实根隔离区间）。
- `sturm`：`sturm_sequence/real_root_count/isolate_real_roots/squarefree_part`。

### 求解与线性代数（L3）
- `solve(f, var)` → `SolveResult(solutions, provisos, status, note)`：
  线性/二次（含复根）/有理根/参数低次（proviso）/**主支逆**（spec.inv 驱动，
  sin/cos/tan/exp/log）。`check_solution(f, sol, var)` 回验。
- `Matrix`：`parse/add/scale/mul/transpose/trace/det/rank/inv/solve` +
  谱理论 `charpoly/eigenvalues/eigenvectors`。`LinResult(unique, particular, null_basis)`。
- `ineq.solve_poly_ineq(term, op, x)` → (区间列表, 字符串)（Sturm 符号表）。
- `sets`：`finite_set/interval/union_of` + `solve_set(f, var)` / `ineq_set(f, op, var)`
  （FiniteSet/Interval/Union 头 + EMPTY_SET；隔离根端点诚实拒答）。
- `ops`：`together/cancel/collect/coefficient/coefficient_list/numerator/denominator`。

### 函数域（L3）
- `trig.trig_reduce(t, x)` / `trig_equivalent(a, b, x)`：多角度基规范形。
- `diff.d(t, x)`（读 spec.deriv；D 名词保持）；`diff.verify(F, x, f)` →
  VERIFIED/FAILED/PROBABLE/UNVERIFIED。

### 分析（L3）
- `series.series(t, x, a, n)` → (k0, coeffs)（截断幂级数，支持负阶 Laurent）；
  `series.leading_term(t, x, a, n)` → (阶, 系数, 尾部)；
  `series.series_term(t, x, a, n)` → 项形态（截断多项式 + O 项头）。
- `limits.limit(t, x, a, side=None)`：a 可为数值/±π 类/±Infinity；
  通道 = 代入 → 消去 → 首阶分析 → log 极点 → exp/atan 支配（Gruntz 一期）→ 洛必达。
- `ode.dsolve(f, y, x)` → `OdeResult(sol, kind, status, note)`：
  题型 direct / separable / linear1 / constcoef2（复根三角实形式）；
  解回代微分回验三态。

### 积分（L3/L7）
- `integrate(t, x)` → **(term, verified, method)**：顺序 = spec anti 表（含线性复合）
  → 自动正向换元 `_try_usub`（候选按大小升序、新鲜哑元+回代往返双重验证、
  每候选微分回验）→ Hermite+RT（有理函数）→ tan(x/2)（三角有理式）。
- `integrate_rational(P, Q, x)`（M1 算法本体，含 atan 实形式）。
- `defint(t, x, lo, hi)` → (值|None, 状态, 说明)：Newton-Leibniz + 奇点拆分 +
  端点单侧极限 + 梯形法交叉核对（矛盾即扣留）；**±∞ 限反常积分判敛**
  （_defint_improper，双端在 0 拆分）；**Piecewise 分段积分**（_defint_piecewise，
  条件线性根定分支点 + 中点 decide 选支）。
- `defint_auto(t, x, lo, hi)`：定积分正向换元自动探测（新限 g(lo)/g(hi) 正向求值，
  全程不求逆；嵌套深度限 3）。
- `istrategy.explain(t, x)` → IntStep 树（kind: table/linear/usub/rational/
  tan-half/failed）；`format_steps(step)`（manualintegrate 同款）。
- `bsub.bsub_defint(t, x, lo, hi, h, tvar, rules=None)`：反向换元
  （主支逆解新限 + 受限 auto 重写（毕达哥拉斯移项形）+ 三角非负窗口脱 √/|·|）。

### 数值与错误（横切/L0）
- `evalnum.eval_exact(t, env)`（环层精确有理）/ `eval_approx`（spec.numeric）/
  `sample_agrees`（只产一致/未知，绝不产否证）。仅验证/抽查通道。
- `errors`：`BudgetExceeded` / `ParseError` / `PolyError`；matrix 另有 `MatrixError`；
  evalnum 有 `EvalNumError`；series 有 `SeriesError`。

### rules/*.rules（L2 定理库）
- `basic.rules`：pow_sum_same（其余表示归并已进构造器）。
- `log.rules`：log_prod/log_sum（成对方向 + 域守卫）、log_pow、exp_log。
- `trig.rules`：sin2_cos2、pyth_sin2/pyth_cos2（auto，反向换元脱根号依赖）、
  sin_add/cos_diff/tan_def；奇偶规则由 spec 生成（origin='spec'）。
- `hyp.rules`：cosh2_sinh2、sinh_def/cosh_def/tanh_def（expand 方向）。
- `power.rules`：sqrt_sq（√(x²)=|x|，auto）、pow_mul/pow_add（正性守卫）。
- `piecewise.rules`：abs_def（abs 的分段定义）。

---

## 3. REPL 命令（session.py `commands()` + kernel 注册表）

**交互/规则**：`:s [path]` 建议 · `:a <id> [path]` 应用 · `:u [n]` 撤销 ·
`:auto` 自动重写 · `:rule/:unrule/:rules` 会话定理 · `:value` 名词→动词 ·
`:refine` 账本化简 · `:steps/:log` 步骤 · `:hist` 历史（%N）。

**假设**：`:assume <fact>` · `:declare <var> <prop>` · `:ctx` · `:obls` ·
`:ans <oid> <fact>` · `:defs/:undef` 用户定义（`f(x):=` / `a:=`）。

**转录**：`:save <path>` / `:replay <path>`（指纹校验；examples/*.pycas 为成品）。

**内核**（KernelCmd 注册表，`:help` 查看全部）：
`:verify` · `:solve` · `:solveset` · `:solveineq` · `:factor` · `:apart` ·
`:integrate` · `:isteps` · `:dsolve` · `:limit`（±inf）· `:series` ·
`:defint`（含 ∞ 限/分段/正向换元）· `:bsub x=h(t) <expr> <var> <lo> <hi>` ·
`:mat/:mdet/:mrank/:minv/:msolve/:charpoly/:eigenvalues/:eigenvectors` ·
`:together/:collect/:numerator/:denominator/:coefficient` · `:latex` · `:load`。

---

## 4. 跨模块调用链速查

- **不定积分**：`session.integrate` → `integrate.integrate` →（anti 表 | `_try_usub`
  递归 | `_rat_pair`(mgcd/ugcd) → apart(factor) → Hermite → `_log_terms`(algnum)
  | `_trig_tan_half`）→ diff.verify 回验。
- **定积分**：`:defint` → `defint_auto`（正向换元探测）→ `defint`（Piecewise 分支 /
  ∞ 限分支 / Newton-Leibniz 主管线：`_sing_points`(dom_condition/factor/sturm) +
  limits.limit 端点极限 + `_numeric_cross`(evalnum)）。`:bsub` → `bsub_defint`
  （solve 主支逆 → `_auto_rewrite`(rules) → `_resolve_sqrt_trig` → defint）。
- **ODE**：`:dsolve` → `ode.dsolve`（`_coef` 分类 → direct/separable/`_solve_linear1`
  (integrate 积分因子)/`_solve_constcoef2`(solve 特征根)）→ `_verify_sol`（diff +
  equivalent 三态）。
- **判等**：`equivalent` → 指针 → simplify 归零 → trig_equivalent → decide 片段 →
  sample_agrees(PROBABLE) → UNKNOWN。
- **判定**：`check_and_assume` → domain_ok(dom_condition/satisfiable) →
  decide(semantic → ledger → interval → derive → axiom)。
- **回放**：`:replay` → `handle` 逐条（与 REPL 同路径）→ `rules_fingerprint` 校验。
