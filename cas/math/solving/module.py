# -*- coding: utf-8 -*-
"""Assembly of the solving module.

The equation checker registers itself through its own module's
`register(builder)` step called from here, rather than through a separate
hardcoded list in the runtime.
"""


def install(builder) -> None:
    from cas.math.solving.equations import checkers as eq_c
    eq_c.register(builder)
