# -*- coding: utf-8 -*-
"""全模块域声明登记（隐藏域约束上缴为数据——统一管线第一步）。

事实来源：docs/cas_v2_arch.md §系数域支持矩阵（2026-08 实证审计）。
导入本模块即完成登记；新能力合入同步更新声明。
"""
from cas.structure import CoeffBase as C, Layer as L, declare

declare("poly", C.PARAMS, {L.RING},
        "叶系数 Fr/Ga/SymRat；Const 命名常数仅 IU 内建，其余拒绝")
declare("factor", C.Q, {L.RING},
        "Zassenhaus 仅 Q[x]；Q(i)/AN/参数当额外变量")
declare("solve", C.Q, {L.RING},
        "低次根式+实 RootOf；参数求根公式回代 UNVERIFIED；超越常数系数拒绝")
declare("msolve", C.Q, {L.RING},
        "Q VERIFIED；Q(i) 路径脆（输出未约简）；params OK")
declare("gsolve", C.Q, {L.RING}, "基计算限 Q；解枚举限有理")
declare("sturm", C.Q, {L.RING},
        "Sturm 假设 Fr；params 崩溃（SymRat numerator bug 已定位）")
declare("ode", C.Q, {L.RING},
        "direct/separable/linear1/constcoef2；特征方程根走代数输出侧")
declare("integrate_rational", C.PARAMS, {L.RING},
        "Hermite+RT：Q 全量/Q(i) 实虚拆分/params atan 判式+proviso；"
        "参数 RootOf 分支化待条件框架阶段二（1/(x^3+a) 类）")
declare("risch_tower", C.MIXED_QI_PARAMS, {L.EXPLOG, L.TRIG, L.ALGEBRAIC},
        "塔内 Q 全链三态；Q(i)+实化切片二；params 塔+Log 参数化+"
        "变指数幂归一；混合域 RDE 门控待 M5.4-c 域泛化 gcd；"
        "残数根越域诚实拒绝 pending M5.4-c")
declare("defint", C.Q, {L.RING, L.EXPLOG, L.TRIG},
        "NL+奇点分割；超越常数界精确；参数界诚实拒（不可数值比较）"
        "；无数值积分通道")
declare("limit", C.PARAMS, {L.RING, L.EXPLOG},
        "数值探针 PROBABLE；参数点 UNKNOWN 诚实；Gruntz 显式延后")
declare("series", C.Q, {L.RING},
        "系数须可折叠数值；超越常数系数诚实拒")
declare("summation", C.PARAMS, {L.RING},
        "Faulhaber+Gosper 有理函数类；调和类诚实拒")
