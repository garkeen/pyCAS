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
