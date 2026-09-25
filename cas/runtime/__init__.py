"""Explicit runtime assembly and query surface.

`bootstrap()` returns an immutable `Runtime`; consumers receive that value
explicitly. There is no process-global runtime slot or compatibility dispatch.
"""

from cas.math.builder import CommandSpec
from cas.math.decls import ConstantDecl, FunctionDecl
from cas.runtime.bootstrap import bootstrap
from cas.runtime.registry import RuntimeBuilder
from cas.runtime.runtime import Runtime, new_workflow

__all__ = (
    "bootstrap",
    "RuntimeBuilder",
    "Runtime",
    "CommandSpec",
    "ConstantDecl",
    "FunctionDecl",
    "new_workflow",
)
