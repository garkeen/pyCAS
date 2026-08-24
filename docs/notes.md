# pyCAS 修订档案（压缩版）

> 职能：①不可逆裁定的理由存档 ②教训条款（bug 模式清单）
> ③批次索引。叙事过程已删；设计真身在 `cas_v2_arch.md`。

## 1. 不可逆裁定

1. **作用域声明 > 全局状态**。根式/常数进塔一律投影期局部参数化
   （_rcN/_npK），出口回代+free_vars 残留守卫；全程不碰
   ALG_MODULI/ALG_RELATIONS。依据：全局注册表曾致假 VERIFIED
   （α 塌缩为其 minpoly 常数项，验证在影子空间自洽闭环）。
2. **形式恒等 ⇒ 特化保真**：互相超越独立假设下的多项式恒等证书
   在常量特化后仍成立（环同态与 D 可交换）——只可能少化简，
   不可能错。这是根式参数化通道的正确性根据。
3. **算法参考纪律**：RDE/prde 唯一参考 FriCAS intpar.spad；
   sympy 仅作分派细节补充与测试期差分预言机（其 wn→rischDE 链
   有右端缩放缺陷）。运行时零 sympy 依赖。
4. **方向安全序**：误证不可积（假 proved 拒答）> 假 VERIFIED >
   覆盖缺口。有界搜索只许返回 'und'，不许把启发失败包装成证明；
   多抬界只损失效率。
5. **A2 区间判定合法性**：整数缩放+二分隔离区间上的精确区间算术
   （端点全 Fr、向外取界、覆盖即穷举）是隔离判定而非数值采样，
   不违反"采样不进 YES"。
6. **主支承诺位 principal-branch**：仅门控验证管线合并阶段
   （x^{3/2}·x^{-1} 类），不改 L0 规范化；默认关，√x 族保持诚实。
7. **保留名 i**：Sym("i")/Const("i") 统一识别为虚单位→Ga(0,1)
   （单一收口于 Poly._build/_frac_num）；用户以 i 为参数符号冲突
   为文档级取舍（sympy I 同款）。
8. **塔构建层 S("i") 语义冻结**：imag-exp 解析按名字认 Sym-i 是
   验证过的正确路径；检测 IU 会触发共轭对路径破坏 exp(i·x) 积分
   （实测回归），禁止改动。

## 2. 教训条款（bug 模式 → 规则）

- **except-swallow 必须配日志或窄化**：`_mk_rat` NameError 被
  except 吞成 None，同坑摔两次。
- **幂运算必须真循环乘**：swap-twice 负幂恒等让 a^{-2}=1/a，
  曾翻转成假 proved 不可积（最高危方向）。
- **solve 返回未规范嵌套分式**：打印同形 ≠ 内部结构同形，
  from_term 分支覆盖不了——系数级 (num,den) 自底向上算术才可靠。
- **多 patch 脚本区间替换会误删相邻块**：大文件改造每步跑测试
  + git diff 审查。
- **变量集成员 ≠ 实际依赖**：零指数填充维度必须投影收紧，
  否则跨层递归 var-mismatch。
- **合并目标展开必须首成员全担**：逐成员重复分摊使系数翻倍产
  假见证——所有 ok 路径过端到端精确验证闸（D(v)/v==n·f−Σm·w）。
- **域上无 content 概念**：欧几里得+monic 即完备；"content 无定义"
  类跳过守卫是过期认知的僵尸。
- **多元 gcd 系数不得当域元素**：(x−1) 在 ℚ(x) 中是单位元会被
  吞噬；唯一正解 = 原始 PRS（本原分解递归 content + 环伪除）。
- **SymRat∘Ga 必须经 NotImplemented 交接**：任何一侧静默包裹都
  产出内嵌异构叶，下游 content/gcd 全线失守。
- **基层有理积分会以实形态吐 Log**：绕过塔域界——凡探针类调用
  必须 `_term_within_field` 后验门。
- **残数视角盲区**：dlog 判据用 n·D(base)=D(w)/w（对底数的导数），
  直接判 base 会漏 e^{log x /2}=√x 类无极点代数情形；exp 层残数
  带 η 因子非裸整数。
- **RatFunc 自动约分会吃 τ-free 表示**（1/(2x)→1/4 事故）：系数域
  与函数域混淆场景须 raw 视角（现仅剩内部互递归防护，用户面已随
  N1 删除）。
- **数值回验 harness 是最便宜的测试预言机**：∫1/(x²+i) 错成
  ∫1/(x²−1) 当场被拦。
- **守卫是债务的利息不是本金**：每写 hasattr/名字比较/all_fr，
  先问缺哪个通用机制。

## 4. 外部参考锚点（修剪保护对象——随叙事删除前必须移入本节）

- **FriCAS intpar.spad**（ParametricRischDE）：weak normalization :920 /
  getDenom :910 / 变换 :1406-1410 / 右端缩放 :1237；
  parametricLogDerivative 全套已读通（查询类功能未实现）
- **FriCAS 积分入口结构**：顶层 trigs2explogs 前置重写 +
  lfintegrate 五类 kernel 分派；tan 核我们走复指数等价路线
  （结果等价、路径不同）；iiilog：exp(k·Log u)->u^k 收缩对应
  EFContract
- **sympy 已知缺陷记录**：wn→rischDE 链右端缩放缺陷（故 prde 不参其实现，
  仅借 bound_degree/spde/no_cancel 分派语义）；prde.parametric_log_deriv
  本身只有启发式版（z 无 τ' 即放弃），无结构定理完备路径——我们的
  _pld_solve 三态化已越过它
- **SAINT/Rubi 参考实据**：本地 pyCAS/SAINT（Slagle 论文复刻，
  slagle.py 规则编号对应论文）；expreduce resources/rubi/ 全章节 .m 快照

## 3. 批次索引（一行一批）

- M0–M3：地基/有理积分/初等域交互/分析层 ODE 换元（见 git log）
- M4：Faulhaber+Gosper
- M5 主链：M5.0 塔 → M5.1 exp(Hermite 推广+RT) → M5.2 primitive/log
  +递归塔 → M5.2c 塔域 RDE 完备(0258c56) → M5.2.5 ℚ(i) → M5.3 三角
  复指数+实化两切片 → M5.2c-iii prde 三件套 → M5.3.1 ℚ(i) 收尾
  (40595e2) → M5.3.2 出口实化(85dc49b) → M5.4a/c AN 参数化+有理通道
  (51acd05) + A1–A4 收尾批 → M5.5 特殊函数出口族 → M5.6 符号参数积分
  + 常量项收集
- M5 收官批：#1 _pld_solve 三态化(b38cf7e)；#2 limited_integrate
  余陪集定理比率化(b33020a)；#3 混合域门控退役(05403b1)
- 架构批：N1 系数域总算术作弊清零(ebb29d9)；N2 Stage 注册表落地
  (68d3be9)
- 文档重整：本压缩 + arch 单一 M 系列重设计（M6 还债/M7 代数常数
  完备域/M8 引擎/M9 分析完备化/M10 远期分支）
