# -*- coding: utf-8 -*-
"""方程求解的 checker（v4 §三 目标位置）。

**回代判官**：求解器交出解（证书），checker 只做代入 + 域标准形判零，
**不重跑求解公式**——这是 §7.3「验证器与求解器独立」最直接的落点。
判零在投影外时诚实未决。
"""

from cas.syntax import term as T
from cas.kernel.evidence import Rejected, UnknownResult
from cas.kernel.verdict import Reason
from cas.math.judge import back_substitute
from cas.math.base.checkers import (
    _ok, _one_conclusion, _premise,
)


class SolveChecker:
    id = "solve.back_substitute"

    def check(self, proposal, context, services):
        content, bad = _one_conclusion(proposal)
        if bad is not None:
            return bad
        pred = _premise(proposal)
        if pred is None or not T.is_eq(pred):
            return Rejected(Reason.FRAGMENT, "前驱不是等式")
        d = proposal.evidence.payload
        if not (T.is_eq(content) and content.args[0] is d.var
                and content.args[1] is d.solution):
            return Rejected(Reason.FRAGMENT, "内容不是该变量等于该解")
        z = back_substitute(pred, d.var, d.solution).zero
        if z is True:
            return _ok(proposal, context)
        if z is False:
            return Rejected(Reason.FRAGMENT, "回代不判零：非解")
        return UnknownResult(Reason.FRAGMENT, "回代判零在投影外，未决")


CHECKERS = (SolveChecker,)


def register(store) -> None:
    for cls in CHECKERS:
        ck = cls()
        if ck.id not in store.checkers:
            store.checkers.register(ck.id, ck)
