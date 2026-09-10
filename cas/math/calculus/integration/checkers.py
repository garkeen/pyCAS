# -*- coding: utf-8 -*-
"""积分的 checker（v4 §三 目标位置）。

独立复核：`d/dx antideriv == 被积式`（走微分层，另一套实现）；定积分再核
`值 == antideriv(b) − antideriv(a)`（精确求值）。积分器与积分 checker 分家：
checker 不重跑积分，只复核证书。
"""

from cas.kernel.evidence import Rejected, UnknownResult
from cas.kernel.verdict import Reason
from cas.syntax.term import S
from cas.syntax import term as T
from cas.math.qarith import fold
from cas.math.base.checkers import (
    _is_piecewise, _ok, _one_conclusion, _premise,
)
from cas.math.base.equality import equal


class IntegrateChecker:
    id = "calculus.antiderivative"

    def check(self, proposal, context, services):
        content, bad = _one_conclusion(proposal)
        if bad is not None:
            return bad
        pred = _premise(proposal)
        if pred is None:
            return Rejected(Reason.FRAGMENT, "缺前驱")
        d = proposal.evidence.payload
        f, x, G = pred, d.var, d.antideriv
        from cas.math.integrate import verify_antideriv
        ok = verify_antideriv(G, f, x)
        if ok is False:
            return Rejected(Reason.FRAGMENT, "微分层复核不通过")
        if ok is None:
            # 判零通道覆盖不到（如 exp/sin 组合）——能力缺失，诚实未决，不是反驳
            return UnknownResult(Reason.FRAGMENT, "微分层无法判定（缺展开归零通道）")
        if d.bounds is None:
            want = T.eq(T.mk(S("Integrate"), (T.mk_bound(x, f),)), G)
            if equal(content, want):
                return _ok(proposal, context)
            return Rejected(Reason.FRAGMENT, "内容与原函数等式不符")
        a_t, b_t = d.bounds
        if _is_piecewise(f) or not (T.is_num(a_t) and T.is_num(b_t)):
            return UnknownResult(Reason.FRAGMENT, "分段/代数限定积分独立复核未接")
        Fa = fold(T.subst(G, {x: a_t}))
        Fb = fold(T.subst(G, {x: b_t}))
        val = fold(T.plus(Fb, T.neg(Fa)))
        want = T.eq(T.mk(S("DefIntegrate"), (T.mk_bound(x, f), a_t, b_t)), val)
        if equal(content, want):
            return _ok(proposal, context)
        return Rejected(Reason.FRAGMENT, "定积分值与端点差不符")


CHECKERS = (IntegrateChecker,)


def register(store) -> None:
    for cls in CHECKERS:
        ck = cls()
        if ck.id not in store.checkers:
            store.checkers.register(ck.id, ck)
