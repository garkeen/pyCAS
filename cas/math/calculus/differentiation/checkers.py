# -*- coding: utf-8 -*-
"""微分的 checker（v4 §三 目标位置）。

独立交叉验证：**域层导数**（另一实现）复核项层微分结果。等式前驱一律否证——
等式两边求导不保真（点解方程 x=3 会「推出」1=0）。源在投影域外时没有独立通道，
诚实未决，不冒充验证通过。
"""

from cas.kernel.evidence import Rejected, UnknownResult
from cas.kernel.verdict import Reason
from cas.math.domains.poly import Poly, p_deriv, to_term
from cas.math.domains.ratfunc import RatFunc, rf_deriv, rf_to_term
from cas.math.qarith import fold
from cas.math.project import project
from cas.math.base.checkers import (
    _is_piecewise, _ok, _one_conclusion, _premise,
)
from cas.syntax import term as T


def _cross_diff(src, got, x):
    """单项交叉验证：域层导数（另一实现）重建期望值与项层结果比对。

    None 表示源在投影域外（无独立通道，交上层未决）；True 域层重建与项层结果
    在有理函数域判等；False 不等；其余为诚实未决。"""
    hit = project(src)
    if hit is None:
        return None
    if hit.element is None:
        expected = T.ZERO                      # 常数格（ℤ/ℚ）导数为 0
    else:
        vs = hit.domain.vars
        if x not in vs:
            expected = T.ZERO
        else:
            idx = vs.index(x)
            ring = hit.domain.ring
            if isinstance(hit.element, Poly):
                expected = to_term(ring, p_deriv(ring, hit.element, idx))
            elif isinstance(hit.element, RatFunc):
                expected = rf_to_term(ring, rf_deriv(ring, hit.element, idx))
            else:
                return None
    from cas.math.domains.ratfunc import ratfunc_domain
    allv = tuple(sorted(T.free_vars(expected) | T.free_vars(got),
                        key=lambda s: s.name))
    if not allv:
        return True if fold(T.plus(expected, T.neg(got))) is T.ZERO else False
    rfd = ratfunc_domain(*allv)
    if rfd.equal(expected, got) is True:
        return True
    if rfd.equal(expected, got) is False:
        return False
    return None


class DiffChecker:
    id = "calculus.derivative"

    def check(self, proposal, context, services):
        content, bad = _one_conclusion(proposal)
        if bad is not None:
            return bad
        pred = _premise(proposal)
        if pred is None:
            return Rejected(Reason.FRAGMENT, "缺前驱")
        if T.is_eq(pred):
            return Rejected(Reason.FRAGMENT, "等式前驱不可求导")
        d = proposal.evidence.payload
        x = d.var
        if _is_piecewise(pred):
            from cas.math.piecewise import fold_nested, branches
            if not _is_piecewise(content):
                return UnknownResult(Reason.FRAGMENT, "分段源与非分段结果，无独立通道")
            sbs = branches(fold_nested(pred))
            gbs = branches(fold_nested(content))
            if len(sbs) != len(gbs):
                return UnknownResult(Reason.FRAGMENT, "分支数不同，不冒充否决")
            for (sv, sc), (gv, gc) in zip(sbs, gbs):
                if sc is not gc:
                    return UnknownResult(Reason.FRAGMENT, "分支条件不同")
                r = _cross_diff(sv, gv, x)
                if r is None:
                    return UnknownResult(Reason.FRAGMENT, "该支在投影域外")
                if r is not True:
                    return Rejected(Reason.FRAGMENT, "域层导数与该支不符")
            return _ok(proposal, context)
        r = _cross_diff(pred, content, x)
        if r is None:
            return UnknownResult(Reason.FRAGMENT, "源在投影域外，无独立通道")
        if r is not True:
            return Rejected(Reason.FRAGMENT, "域层导数与项层结果不符")
        return _ok(proposal, context)


CHECKERS = (DiffChecker,)


def register(store) -> None:
    for cls in CHECKERS:
        ck = cls()
        if ck.id not in store.checkers:
            store.checkers.register(ck.id, ck)
