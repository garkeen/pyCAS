# -*- coding: utf-8 -*-
"""Runtime package.

    registry.py   assembly-time registry (RuntimeBuilder) -- the only write entry
    runtime.py    the assembled read-only query surface (Runtime)
    bootstrap.py  explicit assembly (bootstrap) -- replaces import-time self-registration
    dispatch.py   runtime query entry point (get_runtime + query functions)

`runtime` is the only layer allowed to import every math module; math modules
depend only on syntax / kernel / workflow / math.domains and must **never** depend
on runtime in return. Consumers that need precomputed state (the projection base
field ladder, the decision stages) therefore receive it bound from the outside by
bootstrap, instead of fetching it themselves.
"""

from cas.runtime.bootstrap import bootstrap
from cas.runtime.dispatch import get_runtime
from cas.runtime.registry import ConstantDecl, FunctionDecl, RuntimeBuilder
from cas.runtime.runtime import Runtime, new_workflow

__all__ = ("bootstrap", "get_runtime", "RuntimeBuilder",
           "Runtime", "ConstantDecl", "FunctionDecl", "new_workflow")
