# -*- coding: utf-8 -*-
"""Assembly of the solving module.

The equation checker registers itself through its own module's
`register(builder)` step called from here, rather than through a separate
hardcoded list in the runtime.
"""


from cas.math.builder import MathBuilder


def install(builder: MathBuilder) -> None:
    from cas.math.solving.equations import checkers as eq_c
    eq_c.register(builder)
