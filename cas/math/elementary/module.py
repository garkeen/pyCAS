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

import os

from cas.math.loader import load_declarations

_DATA = os.path.join(os.path.dirname(__file__), "declarations.dsl")


def install(builder) -> None:
    """Install the DSL declarations into the builder (called by bootstrap in
    dependency order)."""
    decls = load_declarations(_DATA)
    for c in decls.constants:
        builder.declare_constant(**c)
    for f in decls.functions:
        builder.declare_function(**f)
    for surface, head in decls.aliases:
        builder.declare_alias(surface, head)
    for role, head in decls.roles:
        builder.declare_role(role, head)
    for head in decls.binders:
        builder.declare_binder(head)
    for head, policy in decls.lifts:
        builder.declare_lift(head, policy)
    for line in decls.rules:
        builder.declare_rule(line)
