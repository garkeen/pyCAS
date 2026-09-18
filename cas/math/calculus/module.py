# -*- coding: utf-8 -*-
"""Assembly of the calculus module.

Each checker registers itself through its own module's `register(builder)` step
called from here, rather than through a separate hardcoded list in the runtime,
so adding a calculus checker is a one-place change (its checkers.py plus this
install).
"""


def install(builder) -> None:
    from cas.math.calculus.differentiation import checkers as diff_c
    from cas.math.calculus.integration import checkers as int_c
    diff_c.register(builder)
    int_c.register(builder)
