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

from cas import term as T


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
    """有理函数结构 ℚ(x)/ℚ(i)(x)/ℚ(params)(x)/ℚ(params,α)(x)：
    Hermite + atan/RT。

    根式代数常数（√2 类数值底有理指数幂叶）在投影时局部参数化为
    不透明符号 _rcN：通道内按互相超越独立参数做全部判定与验证——
    形式恒等对一致特化保真，故内部多项式恒等证书在回代后依然成立
    （只可能少化简，不可能错）。出口回代还原根式形态；回代不完整
    （残留 _rc 符号）诚实降级 UNVERIFIED。全程不触碰全局
    ALG_MODULI/ALG_RELATIONS（注册表泄漏曾致假 VERIFIED——作用域
    声明而非全局状态是本切片的架构裁定）。"""

    name = "rational"
    method = "Hermite reduction + RootOf log part"

    def project(self, t, x, a):
        from cas.integrate import _rat_pair, _collect_rad_params
        try:
            P, Q = _rat_pair(t, x)
            return (P, Q, x, {})
        except Exception:
            pass
        # M5.4-c：根式代数常数 -> 局部不透明参数（无全局关系语义）
        try:
            rmap = _collect_rad_params(t)
            if not rmap:
                return FAIL
            t2 = T.subst(t, rmap)
            P, Q = _rat_pair(t2, x)
            back = {sym: rad for rad, sym in rmap.items()}
            # A2：登记隔离区间（符号全局唯一，跨调用无碰撞；
            # retract 清除——泄漏仅冗余不致错）
            # A3：登记极小多项式（apart 的 Trager 范数分解消费）
            from cas.integrate import (AN_INTERVALS, AN_RELATIONS,
                                       _radical_bracket)
            registered = []
            try:
                for rad, sym in rmap.items():
                    b_, e_ = rad.args
                    bv = T.num_val(b_)
                    lo, hi = _radical_bracket(bv, e_.f.numerator,
                                              e_.f.denominator)
                    AN_INTERVALS[sym] = (lo, hi)
                    from fractions import Fraction as _Fr
                    from cas.poly import Poly as _Poly
                    qd_ = e_.f.denominator
                    mp = _Poly((sym,), {(qd_,): _Fr(1),
                                        (0,): _Fr(-(bv ** e_.f.numerator))})
                    AN_RELATIONS[sym] = mp
                    registered.append(sym)
                return (P, Q, x, back)
            except Exception:
                for sym in registered:
                    AN_INTERVALS.pop(sym, None)
                    AN_RELATIONS.pop(sym, None)
                raise
        except Exception:
            return FAIL

    def compute(self, v):
        from cas.integrate import integrate_rational
        from cas.poly import alg_suspend
        P, Q, x, back = v
        # 挂起全局关系约简：本通道的 α 是局部参数（防御性——投影层
        # 已保证不登记任何模，双保险防外部残留注册表干扰）
        with alg_suspend():
            term, ok, provisos = integrate_rational(P, Q, x)
        return (term, ok, provisos, back)

    def retract(self, v):
        term, ok, provisos, back = v
        if back:
            from cas.integrate import AN_INTERVALS, AN_RELATIONS
            for sym in back:
                AN_INTERVALS.pop(sym, None)
                AN_RELATIONS.pop(sym, None)
            term = T.subst(term, back)
        provisos = [T.subst(p, back) for p in provisos]
        # 回代完整性守卫：残留 _rc 符号 = 上次事故的失效形态，
        # 绝不带病出 VERIFIED（诚实降级）
        leaked = T.free_vars(term) & set(back.keys())
        if leaked:
            return (term, False, provisos)
        return (term, ok, provisos)


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
