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
