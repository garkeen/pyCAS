# -*- coding: utf-8 -*-
"""M78.5-N5 统一投影服务（M78.4 双阶梯 N5）。

FriCAS 参照：fspace.spad Kernel / SMP(R,Kernel) 投影惯例 + intef.spad
lfintegrate 分发表的 (系数域标签, 核集) 二元组。本模块为唯一真源：
  Projection(expr) -> (CoeffDomain, KernelSet)
CoeffDomain ∈ {Q, QI, PARAMS, AN, MIXED_QI_PARAMS, FUNC_QxA}（arch §4 矩阵列）
KernelSet = 表达式中全部核（Exp/Log/Power/代数叶）的规范集合。

落地形式：纯函数，无全局副作用，供 apart/risch_core/solve 等分发表
统一读取，替代各自的 is_param_poly / _an_detect 等硬嗅探（N1 纪律）。
"""
from fractions import Fraction as Fr
from cas.term import S, Expr, Sym, Const, is_num, num_val
from cas.poly import SymRat
from cas.gaussian import Ga
from cas.algfield import ALG_FIELDS

COEFF_Q = "Q"
COEFF_QI = "QI"
COEFF_PARAMS = "PARAMS"
COEFF_AN = "AN"
COEFF_MIXED = "MIXED"
COEFF_FUNC = "FUNC"  # ℚ(x)(α) 等函数域系数
COEFF_UNKNOWN = "UNKNOWN"

def coeff_domain_of_poly(p):
    """Poly p 的系数域标签（与 apart._coeff_domain 同义，唯一实现移此）。"""
    has_qi = has_pr = has_an = has_func = False
    mixed = False
    for c in p.monos.values():
        if isinstance(c, Fr):
            continue
        if isinstance(c, Ga):
            if isinstance(c.re, SymRat) or isinstance(c.im, SymRat):
                mixed = True
            else:
                has_qi = True
        elif isinstance(c, SymRat):
            # SymRat 内含 AN 符号 => 混域
            for pp in (c.num, c.den):
                for v in pp.vars:
                    if v in ALG_FIELDS:
                        has_an = True
                    else:
                        has_pr = True
                for cc in pp.monos.values():
                    if not isinstance(cc, Fr):
                        return COEFF_UNKNOWN
            has_pr = True
        elif hasattr(c, "p") and hasattr(c, "q"):
            # RatFunc 叶（函数域 ℚ(x)(α)）
            has_func = True
        elif hasattr(c, "is_zero"):
            has_an = True
        else:
            return COEFF_UNKNOWN
    if has_func:
        return COEFF_FUNC
    if mixed or (has_qi and has_pr) or (has_an and has_pr):
        return COEFF_MIXED
    if has_an:
        return COEFF_AN
    if has_qi:
        return COEFF_QI
    if has_pr:
        return COEFF_PARAMS
    return COEFF_Q

def projection(expr):
    """expr -> (coeff_domain, kernel_set)。

    coeff_domain：扫描全部 Poly 叶系数后的最上确界（MIXED 为顶）。
    kernel_set：frozenset[Term]（Exp/Log/Power/代数核）。
    """
    # 收集全部核与全部访问节点
    kernels = set()
    coeff_tags = set()
    all_syms = set()
    stack = [expr]
    seen = set()
    while stack:
        u = stack.pop()
        if id(u) in seen:
            continue
        seen.add(id(u))
        if isinstance(u, Expr):
            n = u.head.name
            if n in ("Exp", "Log", "Power"):
                kernels.add(u)
                # Power 数值底有理指数即代数核预信号（常数域 AN 预备态）
                if n == "Power" and len(u.args)==2 and is_num(u.args[0]):
                    from cas.term import Rat as _Rat
                    if isinstance(u.args[1], _Rat) and u.args[1].f.denominator>1:
                        coeff_tags.add(COEFF_AN)
            stack.extend(u.args)
        elif isinstance(u, Sym):
            all_syms.add(u)
            if u in ALG_FIELDS:
                coeff_tags.add(COEFF_AN)
            elif u.name not in ("x", "i") and not u.name.startswith("_"):
                # 内部生成符号 _aN/_tN/_clN 不计入 PARAMS
                coeff_tags.add(COEFF_PARAMS)
        elif isinstance(u, Const):
            if u.name == "i":
                coeff_tags.add(COEFF_QI)
    # 合并（MIXED 为顶）
    if not coeff_tags:
        dom = COEFF_Q
    elif len(coeff_tags)==1:
        dom = next(iter(coeff_tags))
    else:
        dom = COEFF_MIXED
    return dom, frozenset(kernels)
