class BudgetExceeded(Exception):
    def __init__(self, spent=0, message="evaluation budget exceeded"):
        self.spent = spent
        super().__init__(message)


class ParseError(Exception):
    pass


class ScopeError(Exception):
    """A declaration/definition violates the scope contract (symbol not fresh,
    illegal recursion, unbound right-hand side)."""


class BranchError(Exception):
    """A branch operation violates the merge conditions (coverage unproved, the
    branches answer different tasks, a symbol escaped, ...)."""


class TacticsError(Exception):
    """Tactics refusal: cannot be completed within the capability boundary.
    Reported honestly rather than guessed."""


class DiffError(Exception):
    """Differentiation refusal: a derivative template is missing or the
    structure is unsupported (for example differentiating under a binder)."""


class CadError(Exception):
    """Cylindrical decomposition refusal. `reason` comes from verdict.Reason:
    FRAGMENT means the fragment does not cover the input (multivariate or
    non-polynomial partitioning), UNDECIDABLE means undecidable in principle
    (transcendental conditions, comparing transcendental roots)."""

    def __init__(self, message, reason=None):
        super().__init__(message)
        self.reason = reason


class PiecewiseError(Exception):
    """Piecewise container refusal: an ill-formed structure (for example a
    piecewise value in a condition slot) or an unsupported fragment."""


class IntegrateError(Exception):
    """Integration refusal. `reason` comes from verdict.Reason: FRAGMENT means
    the fragment does not cover the input (rational or transcendental
    integrands, improper endpoints needing a limit), UNDECIDABLE means
    undecidable. Refused honestly rather than guessing an antiderivative."""

    def __init__(self, message, reason=None):
        super().__init__(message)
        self.reason = reason
