"""Runtime query entry point.

Consumers (parser, pprint, repl) read mathematical semantics through this module,
and the application installs the assembled runtime here. The semantics come from
explicit assembly rather than from an import side effect, so importing any math
module registers nothing.

**Installation is explicit too.** The application entry point calls `bootstrap()`
and installs the result; `get_runtime()` does not assemble on demand, because a
module that assembles itself on the first attribute read hides an
application-level decision inside a read and leaves the reader with a runtime
nobody chose. There is no `reset_runtime`: dropping only the installed runtime
would leave callers holding the old one, so a half-reset would be a
silent wrong-answer trap. Re-assembly is `bootstrap()` plus `install()`.

Attribute access is forwarded to the installed Runtime through the module-level
`__getattr__` (PEP 562) rather than one hand-written forwarding function per
Runtime method. A per-method list duplicates the whole Runtime API by hand and
has to be edited on every addition, which is exactly the kind of duplication to
avoid. Two names are not forwarded because they are not Runtime methods:
`domain_normal_form` and `new_workflow` forward computation to the math layer.
"""

from cas.runtime.bootstrap import bootstrap

_runtime = None


def install(runtime) -> None:
    """Install the assembled runtime as this process's runtime.

    Called by an application entry point (the REPL, the test session) with the
    result of `bootstrap()`. Installing is an explicit act so that "which runtime
    is in effect" is answered by the application's own code.
    """
    global _runtime
    _runtime = runtime


def get_runtime():
    """The installed runtime.

    Reading semantics before the application assembled one is a wiring error, so
    this raises with the fix rather than assembling behind the reader's back.
    """
    if _runtime is None:
        raise RuntimeError(
            "no runtime installed: an application entry point must call "
            "install(bootstrap()) before reading mathematical semantics")
    return _runtime


def __getattr__(name):
    """Forward every other attribute to the installed Runtime.

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
    need not import math. The context is the installed runtime's, exactly as in
    `cas.api`: this module is the frontend boundary, not a math algorithm."""
    from cas.math.base.equality import normal_form
    return normal_form(get_runtime().math, t)


def new_workflow(**kw):
    """Create a workflow session, with ledger, checkers and decision services
    assembled by the runtime."""
    from cas.runtime.runtime import new_workflow as _nw
    return _nw(**kw)
