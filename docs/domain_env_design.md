# 域阶段管线设计（v3）——已全量落地，本文仅存裁决记录

> 运行时真身：`cas/structure.py`（analyze/Stage/VERIFY_STAGES）、
> `cas/structs.py`（Struct/SOLVERS）、`cas/domain_decls.py`（声明登记，
> M6.5 起测试锁定）。路线图归 `cas_v2_arch.md` §6 单一 M 系列。

## 落地态

- P1 ✅ Analysis 一等对象：analyze(t,x) 单遍扫描（layers/coeff/pmap）
  + 13 模块 DOMAIN_DECLS。
- P2 ✅ Pass 协议 + PRE_PASSES 声明表（NumPowerNorm/EFContract/
  EFExpandTrans）。
- P3 ✅ Struct 协议 cas/structs.py：Qx/TanHalf/Tower 三实例；
  混合域处理为顶层共轭拆分（N1 后原生直通，FAIL 仅剩覆盖边界）。
- P4 ✅（N2, 68d3be9）：Stage 协议定稿（needs/gated 假设门控 +
  degrade 具名降级）；VERIFY_STAGES 判零族；SOLVERS 求解总表
  （integrate 头部硬编码 if 链退役）；principal 承诺位单点门控。

## 被否决的前两版（理由存档）

- v1 DomainEnv 对象（FriCAS 类型系统移植）：动态语言里给每个值背
  域标签 = 重写整个 L0；驻留判等全局唯一性破产。
- v2 规则+账本+spec：只覆盖可条件化重写，改不了表示与等词语义
  （规则是事后重写，L0 不合并的项指针永不相等）。

## v3 核心命题（成立依据）

pyCAS 从不跨域信任结构等词——equivalent() 的分层管线就是
"按内容分派的域阶段序列"。债务真身从来不是缺域对象，而是：
①阶段集合不完备 ②同一分派在多管线各写一遍 ③假设需求不可声明。
解法 = 声明式注册表单一事实源。§1 反模式（三管线各写一遍）已随
N2 正式关闭。
