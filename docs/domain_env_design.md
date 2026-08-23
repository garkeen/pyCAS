# 架构债务修复：域阶段管线（v3，取代前两版）

## 0. 前两版为什么不对（自我批判）

- v1（DomainEnv 对象）：FriCAS 类型系统移植。在动态语言里给每个值
  背域标签 = 重写整个 L0；驻留判等的全局唯一性直接破产。
- v2（规则+账本+spec）：覆盖了**可条件化的恒等式重写**，但漏掉了
  问题另一半——**规范形与等词语义**。规则是事后重写，改不了表示：
  L0 不合并 x^{3/2}·x^{-1}，任何规则都改变不了"两个数学上相等的项
  指针不同"这一事实。规则只能补恒等式，不能定义等词。

## 1. 把问题想到底：pyCAS 真实的需求是什么

关键观察：**pyCAS 从不跨域信任结构等词**。它有三值判定通道，
等词从来就是分层的：

    equivalent(): 指针 → 归零 → 三角层 → 账本/多项式 → 采样

这条管线就是"按内容分派的域阶段序列"——**正确的架构模式已经存在，
只是只有 equivalent() 用了它**。债务的真身：

a. 阶段集合不完备（没有有理幂阶段——√x 族 UNVERIFIED 的根因）；
b. 同样的分派逻辑在三条管线里各写一遍（equivalent / _tower_zero /
   integrate 入口），新增一类数要改 N 处；
c. 阶段的假设需求不可声明（主支承诺藏在天知道哪里）。

所以修复不是引入域对象，而是：**把散落的阶段收拢为一份声明式注册
表，让所有管线共享同一份分派数据**。

## 2. 核心设计：Stage 注册表（单一事实源）

    Stage {
      name            # 'ring_fold' | 'trig_basis' | 'ef_contract'
                      # | 'ratpow_merge' | 'alg_reduce' | ...
      detect(t)       # 适用性：头扫描/系数域扫描（声明式，非 if 散落）
      apply(t)        # 全树显式重建 pass（带预算；绝不进构造器）
      needs(ctx)      # 假设需求：['principal-branch'] | ['x>0'] | []
      degrade         # 假设不可满足时：跳过并记录缺什么（诚实降级）
    }

三条管线改为 Stage 列表的实例化：

    normalize_integrate = [ring_fold, ef_contract, ratpow_merge, ...]
    verify_stages       = [ring_fold, alg_reduce, ratpow_merge, trig_basis,
                           tower_zero]
    simplify_auto       = [ring_fold] ∪ auto通道规则

- **L0 构造器不动**：仍是全域安全交集（驻留判等地基）。分数幂在
  L0 保持原子——但 verify 管线里 ratpow_merge 阶段会把差值树中
  的 x^{3/2}·x^{-1} 合并后再做零判定。
- **假设即门控**：stage.needs 对账本 decide；不可满足则该阶段跳过，
  输出附"缺假设 X"（UNVERIFIED 从模糊变具体）。用户 :declare 后
  自动升级 VERIFIED。
- **算法链分派同构解决**：integrate 的瀑布改写为 Stage 序列的声明
  表——spec 表/换元/tan-half/Risch 都是 detect+apply 的 Stage。
  M6 isteps 需要的"推导即数据"由此免费获得。

## 3. 数域轴 × 函数域轴的匹配（用户框架的落地）

| 轴 | Stage 实例 |
|---|---|
| 数域 | alg_reduce(ALG_MODULI)、ga_split(ℚ(i))、param_provisos(params) |
| 函数域 | ring_fold、trig_basis(商环基)、ef_contract/exp-log 塔、ratpow_merge、piecewise 归并 |

匹配 = detect 在输入上命中；排序 = 管线声明的序列；冲突 = 声明的
优先级（沿用规则 prio 语义）。

## 4. 迁移分期（每期独立合入，默认行为不变）

1. P1 定义 Stage 结构体 + 把 equivalent() 现有分层改造为第一个消费
   者（纯重构，行为不变）
2. P2 _tower_zero 与 integrate 入口的公共阶段收编（ef_contract/
   num_powers/trigs_to_exp 变为 Stage；三处重复消除）
3. P3 新增 ratpow_merge 阶段（needs=['principal-branch'∨'x>0']）：
   ∫√x 族按账本状态自动升级 VERIFIED/proviso
4. P4 integrate 瀑布数据化（M6 地基）；arch 域矩阵改述为 Stage 清单

## 5. 与 FriCAS 的关系（诚实定位）

FriCAS 用类型系统把域绑定到值上（编译期）；pyCAS 用"安全交集 L0 +
内容检测的阶段管线 + 三值诚实"达到同一目的（运行期）。这是动态
语言 + 既有驻留架构下的等价物，不是妥协：代价是某些验证从结构级
降到采样级（如实显示），收益是不需要重写整个 L0。
