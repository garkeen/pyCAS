"""Explicit partial-function relations and their registered extension."""

from cas.math.functions.checker import FunctionEqualityChecker
from cas.math.functions.equality import (
    FunctionEqualityCertificate,
    FunctionEqualityClaim,
    FunctionEqualityKind,
    FunctionEqualityVocabulary,
    equal_on,
    same_partial_function,
)
from cas.math.functions.operation import (
    FunctionComparisonOperation,
    FunctionExtensionOperation,
)

__all__ = [
    "FunctionComparisonOperation",
    "FunctionEqualityCertificate",
    "FunctionEqualityChecker",
    "FunctionEqualityClaim",
    "FunctionEqualityKind",
    "FunctionEqualityVocabulary",
    "FunctionExtensionOperation",
    "equal_on",
    "same_partial_function",
]
