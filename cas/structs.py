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
from cas.errors import PolyError


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
        from cas.integrate import (_rat_pair, _collect_rad_params,
                                   _collect_const_params)
        try:
            P, Q = _rat_pair(t, x)
            return (P, Q, x, {})
        except Exception:
            pass
        # M5.4-c + M5.6#1：根式/命名常数/常数函数项 -> 局部不透明参数
        try:
            rmap = _collect_const_params(t, x)
            if not rmap:
                return FAIL
            t2 = T.subst(t, rmap)
            P, Q = _rat_pair(t2, x)
            back = {sym: rad for rad, sym in rmap.items()}
            # A2/A3：根式叶登记隔离区间与极小多项式（符号全局唯一，
            # retract 清除——泄漏仅冗余不致错）；非根式常量项无关系语义
            from cas.integrate import (AN_INTERVALS, AN_RELATIONS,
                                       _radical_bracket)
            registered = []
            try:
                for rad, sym in rmap.items():
                    if not (isinstance(rad, T.Expr)
                            and rad.head.name == "Power"):
                        continue
                    b_, e_ = rad.args
                    if not (T.is_num(b_) and isinstance(e_, T.Rat)):
                        continue
                    bv = T.num_val(b_)
                    if bv <= 0 or e_.f <= 0:
                        continue
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
                               _parametrize_const_logs, build_extension)
        f = trigs_to_exp(_norm_const_base_powers(t, x))
        f, backsub = _parametrize_const_logs(f, x)
        de, fa, fd = build_extension(f, x)
        return (f, de, fa, fd, backsub, x)

    def compute(self, v):
        from cas.risch import (_risch_rec_mixed, _realify_log_pairing,
                               RischUnsupported)
        from cas import term as T
        from cas.simplify import simplify as _s, expand as _e
        from cas.diff import verify as _vf
        f, de, fa, fd, backsub, x = v
        j = len(de.levels) - 1
        if j == 0:
            from cas.risch import RischUnsupported
            raise RischUnsupported("no extension layer in expression")
        expr = _risch_rec_mixed(fa, fd, de, j)
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


# ---------------------------------------------------------------------------
# SOLVERS 总表（N2 兑现 v3 设计承诺：integrate 瀑布 = 声明式数据）。
# 条目契约 attempt(t, x) ->
#   (F, method_str, provisos)  命中并已 verify 背书
#   None                       不适用，交下一个
#   RischNonElementary         证明性拒答——原样上抛（不吞）
# 头部五条为快速通道（延迟导入防循环），尾部 StructEntry 包装
# project/compute/retract 三段式。新增求解通道只动本表。
# ---------------------------------------------------------------------------

class _HeadSolver:
    """SOLVERS 条目协议：attempt(t, x) ->
      ('hit', F, method, provisos)   命中（verify 背书态如实随附）
      ('miss', reason)               不适用，交下一个（reason 可空）
    RischNonElementary 在条目内部走完特殊函数出口后原样上抛。"""
    name = "?"

    def attempt(self, t, x):
        raise NotImplementedError


class SpecAnti(_HeadSolver):
    name = "spec antiderivative table"

    def attempt(self, t, x):
        from cas.integrate import _spec_antideriv
        from cas.diff import verify as _vf
        F0 = _spec_antideriv(t, x)
        if F0 is None:
            return "miss", ""
        ok = _vf(F0, x, t) == "VERIFIED"
        return "hit", F0, self.name, []


class TrigLinear(_HeadSolver):
    name = "trig poly: multi-angle linearization + termwise table"

    def attempt(self, t, x):
        from cas.integrate import (_trig_linear_integrand,
                                   _spec_antideriv)
        from cas.diff import verify as _vf
        from cas.simplify import simplify as _s
        tl = _trig_linear_integrand(t, x)
        if tl is None:
            return "miss", ""
        terms_ = []
        for c, g in tl:
            if g is T.ONE:
                G = x
            else:
                G = _spec_antideriv(g, x)
                if G is None:
                    return "miss", ""
            terms_.append(T.times(c, G))
        F0 = _s(T.mk(T.S("Plus"), tuple(terms_)))
        ok = _vf(F0, x, t) == "VERIFIED"
        if not ok:
            return "miss", ""
        return "hit", F0, self.name, []


class Usub(_HeadSolver):
    name = "u-substitution"
    _DEPTH = [0]

    def attempt(self, t, x):
        from cas.integrate import _try_usub
        from cas.pprint import to_str as _ts
        if self._DEPTH[0] >= 3:
            return "miss", ""
        self._DEPTH[0] += 1
        try:
            us = _try_usub(t, x)
        finally:
            self._DEPTH[0] -= 1
        if us is None:
            return "miss", ""
        F, ok, g, _h, _H = us
        return "hit", F, f"u-substitution u={_ts(g)}", []


class PowerRule(_HeadSolver):
    name = "rational power rule (algebraic form)"

    def attempt(self, t, x):
        from cas.integrate import _power_antideriv
        from cas.diff import verify as _vf
        pw = _power_antideriv(t, x)
        if pw is None:
            return "miss", ""
        ok = _vf(pw, x, t) == "VERIFIED"
        return "hit", pw, self.name, []


class SymbolPowerRule(_HeadSolver):
    name = "symbolic power rule (generic form)"

    def attempt(self, t, x):
        from cas.integrate import _symbol_power_antideriv
        from cas.diff import verify as _vf
        spw = _symbol_power_antideriv(t, x)
        if spw is None:
            return "miss", ""
        F_sp, proviso = spw
        ok = _vf(F_sp, x, t) == "VERIFIED"
        return "hit", F_sp, self.name, [proviso]


class StructEntry(_HeadSolver):
    """STRUCTS 三段式包装。project FAIL/域拒 => miss（带原因）；
    compute 链 RischNonElementary => 特殊函数出口尝试后仍上抛
    （证明性拒答不吞）。"""

    def __init__(self, st):
        self.st = st

    @property
    def name(self):
        return self.st.method

    def attempt(self, t, x):
        from cas.risch import RischNonElementary, RischUnsupported
        try:
            v = self.st.project(t, x, None)
        except RischUnsupported as _ru:
            return "miss", str(_ru)
        except PolyError as _pe:
            return "miss", str(_pe)
        if v is FAIL or v is None:
            return "miss", ""
        try:
            term, ok, provisos = self.st.retract(self.st.compute(v))
        except RischNonElementary:
            from cas.integrate import _special_output
            sp = _special_output(t, x)
            if sp is not None:
                return "hit", sp[0], sp[2], sp[3]
            raise                     # 无匹配出口 => 保持 proved 拒答
        except RischUnsupported as _ru:
            return "miss", str(_ru)
        except PolyError as _pe:
            return "miss", str(_pe)
        return ("hit", term, self.st.method, provisos, ok)


SOLVERS = [SpecAnti(), TrigLinear(), Usub(), PowerRule(),
           SymbolPowerRule(),
           StructEntry(QxStruct()), StructEntry(TanHalfStruct()),
           StructEntry(TowerStruct())]
