"""Frontend parser: the runtime-aware face of the syntax parser.

The grammar and the construction primitives live in `cas/syntax/parse.py`, which
is pure syntax and depends on neither the runtime nor any math module. That lets
the declaration DSL (`cas/math/loader.py`) parse rule and template text through
the syntax layer instead of reaching into the frontend, so the trusted admission
channel no longer depends on a UI-layer module.

This module is the thin runtime-binding shim for ordinary surface expressions: it
injects the assembled runtime's alias and constant-atom lookup into the syntax
parser. The DSL channel passes its own constant table and bypasses these hooks.
"""

from cas.syntax.parse import tokenize, Parser
from cas.runtime import dispatch as rt


def _alias(name):
    h = rt.alias_head(name)
    return h if h is not None else name


def _const_atom(name):
    d = rt.const_by_name(name)
    return d.atom if d is not None else None


def parse(s, pattern=False, constants=None):
    """Parse an expression.

    `constants` is an optional name-to-constant-atom table; the declaration DSL
    passes it to avoid calling back into the runtime during bootstrap. Ordinary
    expressions are resolved through the assembled runtime's alias and constant
    tables (injected here), so a new surface name or constant needs no parser
    change.
    """
    return Parser(tokenize(s), pattern=pattern, constants=constants,
                  alias_fn=_alias, const_fn=_const_atom).parse()
