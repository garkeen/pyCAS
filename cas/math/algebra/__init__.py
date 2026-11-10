"""Polynomial algebra operations and their independent checkers."""

from cas.math.algebra.gcd_checker import PolynomialGcdChecker
from cas.math.algebra.gcd_operation import PolynomialGcdOperation
from cas.math.algebra.gcd_specification import (
    GcdCertificate,
    GcdClaim,
    GcdVocabulary,
    has_gcd,
)
from cas.math.algebra.resultant_checker import ResultantChecker
from cas.math.algebra.resultant_operation import ResultantOperation
from cas.math.algebra.resultant_specification import (
    ResultantCertificate,
    ResultantClaim,
    ResultantVocabulary,
    has_resultant,
)
from cas.math.algebra.root_count_checker import RootCountChecker
from cas.math.algebra.root_count_operation import RootCountOperation
from cas.math.algebra.root_count_specification import (
    RootCountCertificate,
    RootCountClaim,
    RootCountVocabulary,
    has_root_count,
)

__all__ = [
    "GcdCertificate",
    "GcdClaim",
    "GcdVocabulary",
    "PolynomialGcdChecker",
    "PolynomialGcdOperation",
    "ResultantCertificate",
    "ResultantChecker",
    "ResultantClaim",
    "ResultantOperation",
    "ResultantVocabulary",
    "RootCountCertificate",
    "RootCountChecker",
    "RootCountClaim",
    "RootCountOperation",
    "RootCountVocabulary",
    "has_gcd",
    "has_resultant",
    "has_root_count",
]
