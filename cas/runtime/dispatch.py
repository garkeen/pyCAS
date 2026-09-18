"""Runtime query entry point.

Consumers (parser, pprint, decide, project, rules, domcond, diff, ...) read
mathematical semantics through this module. The semantics come from explicit
assembly rather than from an import side effect, so importing any math module
registers nothing.

The first call triggers `bootstrap()` once; afterwards the runtime is read-only.
The only write entry point is RuntimeBuilder. There is no `reset_runtime`:
dropping only the dispatch cache would leave the math modules bound to the old
runtime, so a half-reset would be a silent wrong-answer trap. Tests re-assemble
by calling `bootstrap()` again, which re-binds every math module.

Attribute access is forwarded to the assembled Runtime through the module-level
`__getattr__` (PEP 562) rather than one hand-written forwarding function per
Runtime method. A per-method list duplicates the whole Runtime API by hand and
has to be edited on every addition, which is exactly the kind of duplication to
avoid. Two names are not forwarded because they are not Runtime methods:
`domain_normal_form` and `new_workflow` forward computation to the math layer.
"""

from cas.runtime.bootstrap import bootstrap

_runtime = None


def get_runtime():
    """Return the runtime, assembling it on the first call."""
    global _runtime
    if _runtime is None:
        _runtime = bootstrap()
    return _runtime


def __getattr__(name):
    """Forward every other attribute to the assembled Runtime.

    This replaces a hand-written forwarding function per Runtime method: the query
    surface is exactly the read-only surface of the Runtime, with no duplicated
    method list to keep in sync. An unknown name still raises AttributeError,
    because getattr on the Runtime raises it.
    """
    if name.startswith("__"):
        raise AttributeError(f"module {__name__!r} has no attribute {name!r}")
    return getattr(get_runtime(), name)


# --- computation forwarding (the frontend must not reach into math directly) ---

def domain_normal_form(t):
    """The domain normal form, used by the frontend (the REPL norm command) so it
    need not import math."""
    from cas.math.base.equality import normal_form
    return normal_form(t)


def new_workflow(**kw):
    """Create a workflow session, with ledger, checkers and decision services
    assembled by the runtime."""
    from cas.runtime.runtime import new_workflow as _nw
    return _nw(**kw)
