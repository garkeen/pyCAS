# 架构债务修复：域感知规范化（pyCAS 精神方案 v2）

状态：设计稿 v2，取代 v1（v1 的 DomainEnv 对象是 FriCAS 类型系统
移植思维，引入新抽象层违背本项目"规则=定理库、反硬编码、账本闸门"
的既有精神）。触发事件：分数幂合并尝试引发回归回滚。

## 1. FriCAS 实测证据（保留自 v1）

- Expression(R) Rep = Fraction(SparseMultivariatePolynomial(R, Kernel))
  （expr.spad）——规范形由表示保证；
- iiilog 型收缩是 EF 包的构造行为，实性门控 localReal?（elemntry.spad
  632-660）；
- 代数关系经类型参数进入：SAE(R,UP,M) 的 reduce=monicDivide 余项
  （algext.spad）。

结论：FriCAS 用**类型参数化**让"域决定规范形"。pyCAS 不移植类型
系统，而是回答同一个问题：**我们的对应机制已经存在，只是没被用作
域载体**——规则 DSL（守卫经 decide 查账本）、spec 注册表、上下文。

## 2. 核心命题：域 = 规则集启用状态 ⊕ 账本假设 ⊕ spec 策略位

不需要新的 DomainEnv 抽象。三个已有机制组合即完整答案：

| 域语义需求 | pyCAS 已有载体 |
|---|---|
| "主支复语义下 e^{k·log u}=u^k" | **一条带守卫的规则**（explog.rules） |
| "x>0 才允许 √x·√x⁻¹→1" | 规则守卫 `decide(x>0)` 查账本 |
| "分支策略开关" | 账本事实 `PrincipalBranch()`（:declare 入账） |
| 函数知识（deriv/anti/收缩） | spec 注册表（loader 由 parity 自动生成规则已是先例——spec 驱动规则生成是家规！） |
| 代数关系约简 | ALG_MODULI（M5.4b 已落地） |
| 可解释性 | 规则应用天然进 step log（哪条定理、哪个方向） |

## 3. 分数幂裁定的最终解法（示范案例）

term.py 全局裁定**永久不动**（L0 = 全域安全交集，这是驻留判等的
地基）。域行为全部上移到规则层：

    # rules/explog.rules（新增）
    rule ef_powint  = exp(?k*log(?u)) -> ?u^?k
         guard isIntK(k)                                          as contract
    rule ef_ratpow_merge = ?x^?a * ?x^?b -> ?x^(?a+?b)
         guard isRatPair(a,b) && (principalBranch? || decide(x>0)==YES)
                                                                      as expand

- 主支承诺未声明时：合并不发生，∫√x 显示 UNVERIFIED（现状，诚实）
- `:declare principal-branch` 入账后：同一输入 VERIFIED 且 step log
  记录所用定理与前提
- 回归灾难不再可能：规则经显式工作列表 + 预算应用，不在构造器里
  递归

## 4. 迁移（纯增量，无核心手术）

1. P1 `_ef_contract/_ef_expand_trans` 改写为 explog.rules 条目 +
   integrate 入口的规则应用调用（今日行为不变，出处变为可解释）
2. P2 `principalBranch?` 谓词接入 decide/:declare
3. P3 分数幂合并规则落地（§3），UNVERIFIED→按需 VERIFIED
4. P4 ALG_MODULI/spec/trig 商环在文档矩阵中改述为"域=启用规则集"
   的实例清单（arch §系数域支持矩阵同步）

每步独立合入；P1-P3 不改变任何默认输出。
