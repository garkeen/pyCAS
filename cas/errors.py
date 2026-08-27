class BudgetExceeded(Exception):
    def __init__(self, spent=0, message="evaluation budget exceeded"):
        self.spent = spent
        super().__init__(message)


class PolyError(Exception):
    pass


class ParseError(Exception):
    pass


class SolveError(Exception):
    pass


class TacticsError(Exception):
    """战术层拒答：能力边界内无法完成（诚实报错，不猜）。"""


class DiffError(Exception):
    """微分拒答：缺导数模板或结构不支持（如绑定变量下微分）。"""


class CadError(Exception):
    """柱面分解拒答。reason 取自 verdict.Reason：
    FRAGMENT=片段未覆盖（如多变量/非多项式分区），
    UNDECIDABLE=定理级不可判定（超越条件、超越根比大小，拒答表 §7）。"""

    def __init__(self, message, reason=None):
        super().__init__(message)
        self.reason = reason


class PiecewiseError(Exception):
    """分段容器拒答：病态结构（如条件位置放了分段值）或片段不支持。"""
