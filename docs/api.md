# pyCAS API 参考（数据结构 + 全部 API）

> 对应架构：`docs/cas_v2_arch.md`。本文档只讲"有什么、怎么用"，设计理由看架构文档。
> 状态图例：
> - **live**：有静态调用者（生产代码或测试）
> - **registered**：动态注册（装饰器入表，管线分发；静态引用为 0 是正常现象）
> - **facade**：公共 API 面 / 兼容入口（供外部导入）
> - **future**：为后续里程碑（M3+）预留，尚无消费者

---

## 0. 模块分层总览

```
L7  策略      session.py（积分/求解/化简策略入口）、integrate.py
L6  会话      session.py · parser.py · pprint.py
L5  化简      simplify.py（per-head 注册表 + cost）
L4  上下文    context.py · decide.py · domain.py
L3  领域      poly.py · factor.py · apart.py · ratfunc.py · algnum.py · matrix.py · solve.py · trig.py · diff.py
L2  规则      rules.py · loader.py · rules/*.rules
L1  匹配      match.py
L0  项        term.py · errors.py
```

---

## 1. 核心数据结构

### 1.1 Term 类族（term.py，L0）

不可变、构造即规范化（AC 头 flatten + 全序 + 常量折叠在构造器内完成），`__eq__` 走内容哈希。

| 类 | 含义 |
|----|------|
| `Sym(name)` | 符号变量（x, y…），构造器 `S(name)` |
| `Const(name)` | 数学常量名（π 等），构造器 `C(name)` |
| `DB(i)` / `BVal(val)` | 绑定词内部：哑变量编号 / 绑定时的代入值 |
| `Int(v)` | 任意大整数，构造器 `N(v)` |
| `Rat(f)` | 精确有理数（Fraction），`N()` 遇小数自动归一 |
| `Special(name)` | 特殊原子（TRUE/FALSE/UND/INFINITY 等） |
| `PatVar(name)` | 单参洞 `?x`，构造器 `PV(name)` |
| `PatSeq(name)` | 序列洞 `??x`，构造器 `PS(name)` |
| `Expr(head, args)` | 函数应用：head 为 Sym，args 为 Term 元组；构造器 `mk(head, args)` / `fn(name)` |
| `Bound(hint, body)` | 绑定词节点（∫/Σ/Π/lim/D 的哑变量载体）；构造时 α-规范化改名 |

**驻留**：`Expr/Bound` 构造时经全局驻留表（`_next_h` 分配句柄，`_intern_expr` 内容寻址），等项 = 同句柄。

**构造器速查**：`S/C/N/SP/PV/PS/mk/fn/plus/times/pw/neg/div/sqrt/eq/lt/le/gt/ge/ne/and_/or_/not_/quote/mk_bound/subst/instantiate/term_at/replace_at/all_paths/size/free_vars`。

关键语义函数：
- `quote(t)`：引用（求值免触）
- `subst(t, mapping)`：替换（α 躲避）
- `instantiate(t, sub)`：洞模式实例化（按匹配子代入）
- `term_at(t, path)` / `replace_at(t, path, v)` / `all_paths(t)`：path 寻址（根到子的索引序列，全系统唯一寻址方案）
- `is_num/num_val/sign_num/sort_key`：数值工具

### 1.2 Poly（poly.py，L3）

稀疏字典多项式：`monos: {(e0, e1, …): Fraction}`，指数按 `vars_` 顺序。单变量指数元组 `(e,)`。

| 构造 | 说明 |
|------|------|
| `Poly(vars_, monos)` | 直接构造 |
| `Poly.zero/one/const/mono(vars_, …)` | 常量构造器 |
| `Poly.from_term(t, vars_)` | term → Poly（含变量重排检查） |
| `Poly._build(t, vars_)` | 内部构造（含除法检测） |

| 方法 | 说明 |
|------|------|
| `to_term()` | Poly → term（含负指数/分数指数拒绝） |
| `is_zero/is_const/const_val` | 判定 |
| `__add__/__neg__/__sub__/__mul__/__pow__/scalar(f)` | 算术（精确 Fraction） |
| `deriv(var)` | 偏导 |
| `degree(var)` / `lc(var)` | 次数 / 首项系数 |
| `content()` / `primitive()` | 内容 / 本原分解 |
| `udivmod(o)` | 带余除（Q 上，伪除）→ (q, r) |
| `is_monic(var)` | 首一判定 |

| 顶层函数 | 说明 |
|----------|------|
| `ugcd(a, b)` | 首一 gcd（primitive part + Gauss 引理） |
| `uresultant(a, b)` | Sylvester 结式 |
| `udiscriminant(a)` | 判别式 |

### 1.3 RatFunc（ratfunc.py，L3，future）

有理函数互素规范形 `(p, q)`（Poly 对，构造时约分）。

- `from_poly(p)` / `from_const(vars_, f)` / `from_term(t, vars_)`
- `__add__/__neg__/__sub__/__mul__/__truediv__/__pow__/to_term()`
- 消费者：M5 Risch 塔（当前仅测试引用）

### 1.4 RootOf（algnum.py，L3）

代数数：`RootOf(m, idx)`——不可约 monic 多项式 m 的第 idx 个根（共轭类编号）。
`to_term()` → `RootOf(m_term, idx)` term。

### 1.5 T3 三值（decide.py，L4）

`T3` 枚举（YES/NO/UNKNOWN）+ `and3/or3/not3` Kleene 组合、`negate(f)`（含 UNKNOWN→UNKNOWN）。

### 1.6 Context（context.py，L4）

有序账本：条目 `Entry(fact, kind, origin)`；回滚点栈；分支 `Branch(cond, ctx, status)`。

| 方法 | 说明 |
|------|------|
| `assume(fact, origin, kind)` | 直入账（不走域闸门；内部用） |
| `check_and_assume(fact, …)` | **统一入账闸门**：域检死 → 矛盾锁 → 入账，返回 (T3, why) |
| `clone()` / `branch(*conds)` | 分支原语（clone 共享 entries，marks 不复刻） |
| `mark()` / `rollback(mi)` / `drop_origin(origin)` | 回滚 / 按来源删除 |
| `facts()` | 账本条目列表 |
| `decide(fact)` / `contradicted(fact)` | 查询入口 |

### 1.7 规则引擎（rules.py，L2）

| 类型 | 字段 |
|------|------|
| `Rule` | id, pattern, template, guard, direction, channels, auto, origin |
| `Step` | sid, rule_id, path, before, after, guard, dcost（step log 一等数据） |
| `ApplyResult` | ok, guard, term, subst |

`RuleSet`：`add/remove/for_term(t)/ids`，per-head 索引（`root_key`）。
`apply_rule(rule, expr, path, guard_eval=None, budget=10000)`：匹配 → 守卫 3VL（YES 应用 / NO 跳过 / UNKNOWN 回报）→ 实例化替换。

### 1.8 Session（session.py，L6）

状态 = current + step log + 义务队列 + 账本 + 规则库（+预算）。方法见 §3。

`Obligation(oid, question, affects, note, pending)`：义务队列（提问工作流）。

### 1.9 Matrix / LinResult（matrix.py，L3）

`Matrix(rows)`（rows = term 列表的列表）：`parse(spec)` / `add/scal/mul/transpose/trace` / `det`（精确分数消元）/ `rank` / `inv` / `solve(b)` → `LinResult(unique, particular, null_basis)` / `show()`。

### 1.10 SolveResult（solve.py，L3）

`solve(f, var, budget)` → SolveResult：status ∈ {solved, identity, contradiction, unsupported} + solutions + provisos。

### 1.11 其他

- `errors.py`：`BudgetExceeded(spent, message)` / `PolyError` / `ParseError` / `SolveError`；matrix.py 另有 `MatrixError`
- `domain.py`：`Domain` 基类 + `RealDomain/RationalDomain/IntegerDomain/ComplexDomain` 单例（`R/Q/Z/C`）；`dom_condition(t)` 递归提取定义域约束；`domain_of(name)`

---

## 2. 全部模块 API

### term.py（L0）
构造器与语义函数见 §1.1。内部：`_fold_ac/_fold_num_only/_fold_bool_ac/_fold_power/_intern_expr/_has_special`（构造即规范化管线）、`_shift/_abstract/_mk_bound_canon`（绑定词 α 机制）、`sort_key`（全序）。

### errors.py（L0）
见 §1.11。

### match.py（L1）
- `matches(pat, tgt, sub=None, budget=10000)`（公开入口；AC 归并 + 有界回溯）
- 内部：`_match/_match_seq/_match_orderless/_has_holes/_sub_key`

### rules.py / loader.py（L2）
见 §1.7。DSL：
- `parse_rule_line(line, origin='dsl')` / `parse_rules(text, origin='dsl')`
- `load_dir(path, ruleset)`：读 `rules/*.rules`（热重载）

DSL 语法：`rule <id> = <pattern> -> <template> [guard <c>] [as <direction>] [channels <a,b>] [auto]`

### context.py / decide.py / domain.py（L4）
- 公共：`Context`（§1.6）、`decide(fact, ctx, _depth=0)`、`eval_guard(guard, sub, ctx)`、`negate`、`contradicted`、`satisfiable(constraints, ctx)`、`domain_ok(fact, ctx)`、`equivalent(a, b, ctx=None, budget=100000)`（统一等价入口）
- **registered**：`@derive(name, applies)` 注册推导族（`_rule_*`，`_derive_layer` 分发）；`@axiom` 注册公理族（`_axiom_*`，`_AXIOM_CHECKS` 分发）
- **facade**：`decided(fact, ctx)`（decide 的薄包装）
- 内部：`_facts_lookup/_chain_query/_poly_eq_check/_same/_cmp_numeric/_family_cmp/_contains/_eq_subst`（管线层）

### simplify.py（L5）
- `simplify(t, budget=100000)` / `cost(t)`（加权节点计数）/ `expand(t)`
- `register(name, fn)`：per-head 化简注册表
- 内部：`_norm_plus_args/_norm_times_args/_norm_power_args/_mul_expand/_sqrt_fac_fold/_split_coeff`

### parser.py / pprint.py（L6）
- `parse(s)` → Term；`to_str(t, prec=0, hint=None)` → 字符串
- Parser 类（tokenize/expr/unary/postfix，优先级爬升）

### session.py（L6）
见 §3 REPL。方法：`feed/suggest/apply/auto/assume/answer/undo/replay/verify/solve/mat/mdet/mrank/minv/msolve/factor/apart/integrate/show/commands`。`run()` 启动 REPL。

### poly.py / factor.py / apart.py（L3）
- Poly：§1.2
- `factor(f, rng=None)` → `(content, [(monic_factor, mult)])`；`squarefree_decomp(f)`；`factor_str(f, rng=None)` → 人类可读串（session.factor 消费）
- `apart(f, g, x=None)` → `(q, [(num, den, k)])`，Σ num·(g/denᵏ) + q·g == f
- factor.py 内部 mod-p 工具族：`_mod_sub/_mod_add/_mod_mul/_mod_divmod/_monic/_mod_gcd/_mod_xgcd/_mod_pow`（模算术）、`_ddf/_cz_split/_choose_prime`（DDF + Cantor-Zassenhaus + 素数选择）、`_add_int/_add_mod/_sub_mod/_sym_mod/_int_poly/_trunc/_to_int`（整数/对称化算术）、`_hensel/_hensel_step`（Hensel 提升）、`_l1_norm/_test_pl/_subsets/_is_prime`（组合/界）、`_coeffs/_poly_from_coeffs`（表示转换）

### ratfunc.py（L3，future）
见 §1.3。

### algnum.py（L3）
- `uexgcd(a, b)` → (s, t, g)，s·a + t·b = g
- `inv_mod(a, m)`；`qa_mod/qa_mul/qa_inv/qa_div(a/b, m)`（ℚ(α) 域，mod 不可约 monic）
- `tr_power_sums(m, upto)`：根幂和 s₁..s_upto（牛顿恒等式）
- `tr_eval(m, c, t=0)`：**t-偏移迹** Tr(c·βᵗ)，t=0 为普通迹；u=0 项按 v·deg（根数）计入
- `coefs(p, x)`：降幂系数 [lc, …, const]（含零位）
- `RootOf`：§1.4

### matrix.py（L3）
见 §1.9。

### solve.py（L3）
`solve(f, var, budget=100000)` / `check_solution(f, sol, var, budget=100000)`（tests 消费）。内部：`_linear_split/_quadratic/_poly_solve/_root_term/_sqrt_fr/_sort_sols/_freet/_peval/_sub`。

### trig.py（L3）
- `trig_reduce(t, x)`：sin/cos 幂积多项式 → ∑(aₙsin nx + bₙcos nx) 规范形；不支持返回 None
- `trig_equivalent(a, b, x)`：恒等式判定 True/False/None
- 内部：`_expand/_sin_pow/_cos_pow/_i_pow_inv`（复数 Laurent 系数）、`_cadd/_cmul/_cscale`（复数算术）、`_ladd/_lmul`（Laurent 字典）

### diff.py（L4）
- `diff(t, x)`（规则式微分器）
- `verify(F, x, f, budget=100000)`：**积分验证通道**（D(F) 化简与 f 比较，三值）

### integrate.py（L3/L7）
- `integrate(t, x)` → (result, verified)：有理函数走 Hermite+RootOf；sin x/cos x 有理式走 t=tan(x/2)；否则 PolyError
- `integrate_rational(P, Q, x)`（M1 算法本体）
- 内部：`_frac`（递归通分）`/_rat_pair`（约分）`/_hermitte_power`（单因子幂递推）`/_log_terms`（线性闭式 + 高次 RootOf）`/_integrate_poly` `/_assemble` `/_verify`（符号精确验证：poly 导数 + 有理项 + 线性 log 组 + RootOf 组迹公式）`/_qa_to_term` `/_trig_check/_trig_sub/_trig_tan_half`

### rules/*.rules（L2）
- `basic.rules`：`pow_one/pow_sum_same/zero_plus/one_times`
- `log.rules`：`log_prod/log_sum`（成对方向，guard ?x>0 && ?y>0）、`log_pow`、`exp_log`
- `trig.rules`：`sin2_cos2/sin_neg/cos_neg/sin_add/cos_diff/tan_def`

---

## 3. REPL 命令（session.py `commands()`）

| 命令 | 说明 |
|------|------|
| `:s [path]` | 建议：列出该位置可套的规则（3VL 守卫） |
| `:a <rule-id> [path]` | 手动应用规则（UNKNOWN 守卫 → 建义务 #id） |
| `:u [n]` | 撤销 n 步 |
| `:auto` | 核心化简（simplify + auto 规则，cost 单调不增） |
| `:assume <fact>` | 入账（域闸门 + 矛盾锁） |
| `:ans <oid> <fact>` | 回答义务 → 重放受影响步骤 |
| `:obls` / `:log` / `:ctx` | 义务 / step log / 账本 |
| `:verify <F> <x> <f>` | 积分验证 |
| `:solve <expr> [var]` | 方程求解 |
| `:factor <expr>` | Zassenhaus 因式分解（走 factor_str） |
| `:apart <num> <den>` | 部分分式 |
| `:integrate <expr>` | 不定积分（[VERIFIED]/[UNVERIFIED]） |
| `:mat/:mdet/:mrank/:minv/:msolve` | 线性代数 |
| `:load` | 热重载规则库 |

---

## 4. 跨模块调用链速查（谁消费谁）

- 积分主链：`session.integrate` → `integrate.integrate` → `_frac/_rat_pair`(poly/ugcd) → `apart`(factor/squarefree_decomp) → `_hermitte_power`(algnum: qa_mul/qa_inv) → `_log_terms`(algnum: qa_div) → `_verify`(algnum: tr_eval/coefs/tr_power_sums) → 三角分支 `_trig_tan_half`(trig 代换) → diff.verify（外部验证）
- 因式分解链：`factor` → `squarefree_decomp`(ugcd) → `_zassenhaus`(_choose_prime/_ddf/_cz_split/_hensel/_sym_mod 族)
- 判定链：`Context.check_and_assume` → `domain_ok`(dom_condition/satisfiable) → `decide`(semantic → ledger(_facts_lookup/_chain_query) → derive(_RULES) → axiom(_AXIOM_CHECKS))
- 化简链：`simplify` → per-head `register` 表 → `cost`；规则链：`RuleSet.for_term` → `apply_rule`(matches → guard eval_guard) → `instantiate`
- 规则面：`Session.__init__`/`:load` → `loader.load_dir` → `parse_rules` → `RuleSet.add`（rules/*.rules）