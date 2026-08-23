# -*- coding: utf-8 -*-
"""结构协议与求解器实例（P3：Maple frontend 的通用化，一份实现）。

Struct 协议：project / compute / retract 三段——
  project(t, x, a) -> value | FAIL    入域投影（可失败=不适用）
  compute(value)   -> value'          域内算法（域自有规范形与等词；
                                      允许内部按 verify 门择优形态）
  retract(value')  -> (term, ok|None, provisos)
                                      ok=None 表示交由管线统一验证

诚实性由协议强制：投影失败=不适用；域内证明无解=RischNonElementary
带证据链上抛；出域后统一过 diff 验证背书。
"""

from fractions import Fraction as Fr


class _Fail:
    """投影失败哨兵（不适用≠错误）。"""

    __slots__ = ()

    def __repr__(self):
        return "FAIL"


FAIL = _Fail()


class Struct:
    name = "?"
    method = "?"

    def project(self, t, x, a):
        return FAIL

    def compute(self, v):
        raise NotImplementedError

    def retract(self, v):
        raise NotImplementedError


class QxStruct(Struct):
    """有理函数结构 ℚ(x)/ℚ(i)(x)/ℚ(params)(x)：Hermite + atan/RT。

    代数常数（ALG_MODULI 登记）在计算期间挂起约简——保持符号形态，
    答案经回代还原根式。这确保 ∫1/(x²-√2) 出 log(x-√2) 而非 log(x-2)。"""
    name = "rational"
    method = "Hermite reduction + RootOf log part"

    def project(self, t, x, a):
        from cas.integrate import _rat_pair
        try:
            P, Q = _rat_pair(t, x)
        except Exception:
            return FAIL
        return (P, Q, x)

    def compute(self, v):
        from cas.integrate import integrate_rational
        from cas.poly import alg_suspend
        P, Q, x = v
        # 挂起关系约简：代数常数保持符号形态（_a1 不塌缩为数值）
        with alg_suspend():
            term, ok, provisos = integrate_rational(P, Q, x)
        return (term, ok, provisos)

    def retract(self, v):
        return v


class TanHalfStruct(Struct):
    """三角有理式结构：t = tan(x/2) 代换 → 有理积分。"""
    name = "tan-half"
    method = "t = tan(x/2) substitution -> rational integration"

    def project(self, t, x, a):
        from cas.integrate import _trig_check
        from cas.structure import Layer
        if a is not None and Layer.TRIG not in a.layers:
            return FAIL              # 分析层分派：无三角层直接跳过
        return (t, x) if _trig_check(t, x) else FAIL

    def compute(self, v):
        from cas.integrate import _trig_tan_half
        from cas.errors import PolyError
        tt, xx = v
        res = _trig_tan_half(tt, xx)
        if res is None:
            raise PolyError("tan-half unmatched")
        if len(res) == 4:
            term, ok, _m, prov = res
        else:
            term, ok, prov = res
        return (term, ok, prov)

    def retract(self, v):
        return v


class TowerStruct(Struct):
    """初等函数域结构：exp/log 微分塔上的完备 Risch 判定。

    混合域（ℚ(i,params)）投影即 FAIL（M5.4-c 域泛化 gcd 前不可用，
    理由随 FAIL 传递而非静默）。"""
    name = "tower"
    method = "Risch tower (exp/primitive case)"

    def project(self, t, x, a):
        from cas.risch import (trigs_to_exp, _norm_const_base_powers,
                               _parametrize_const_logs, build_extension,
                               RischUnsupported, _iter_leaf_coefs_m,
                               _mixed_domain_leaf)
        f = trigs_to_exp(_norm_const_base_powers(t, x))
        f, backsub = _parametrize_const_logs(f, x)
        de, fa, fd = build_extension(f, x)
        if any(_mixed_domain_leaf(c) for c in _iter_leaf_coefs_m(fa)) or \
                any(_mixed_domain_leaf(c) for c in _iter_leaf_coefs_m(fd)):
            raise RischUnsupported(
                "tower over Q(i,params) mixed domain pending M5.4-c "
                "(field-generic gcd)")
        return (f, de, fa, fd, backsub, x)

    def compute(self, v):
        from cas.risch import _risch_rec, _realify_log_pairing
        from cas import term as T
        from cas.simplify import simplify as _s, expand as _e
        from cas.diff import verify as _vf
        f, de, fa, fd, backsub, x = v
        j = len(de.levels) - 1
        if j == 0:
            from cas.risch import RischUnsupported
            raise RischUnsupported("no extension layer in expression")
        expr = _risch_rec(fa, fd, de, j)
        subs = {T.S(de.levels[i].name): de.terms[i]
                for i in range(1, len(de.levels))}
        if subs:
            expr = T.subst(expr, subs)
        if backsub:
            expr = T.subst(expr, backsub)
        # 出口实化切片二：log 配对候选先规范化再整体 verify 背书，
        # 失败保留复形态（诚实纪律）
        try:
            e2 = _realify_log_pairing(expr, x)
            if e2 is not None:
                e2 = _s(_e(e2))
                if _vf(e2, x, f) == "VERIFIED":
                    expr = e2
        except Exception:
            pass
        return (expr, x, f)

    def retract(self, v):
        return (v[0], None, [])


STRUCTS = [QxStruct(), TanHalfStruct(), TowerStruct()]
