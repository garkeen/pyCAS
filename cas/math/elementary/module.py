"""Assembly of the elementary module.

All mathematical semantics of constants and functions are declared in the DSL
data file `declarations.dsl`, never registered from Python; this module only
performs the assembly calls: read the DSL and hand the declarations to the
builder. Importing this module registers nothing; assembly only happens when
`bootstrap()` calls `install`.

The admission discipline (only unconditional identities, branch-breaking
templates set to null with the reason recorded) is written in the DSL file's
comments and notes and is checkable mechanically against that text rather than by
reviewing Python registration calls.
"""

from pathlib import Path

from cas.math.builder import MathBuilder
from cas.math.loader import load_declarations

_DATA = Path(__file__).with_name("declarations.dsl")


def install(builder: MathBuilder) -> None:
    """Install the parsed declaration set in explicit assembly order."""
    builder.register_declarations(load_declarations(_DATA))
