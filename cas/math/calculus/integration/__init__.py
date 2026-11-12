"""Polynomial integration, rational Hermite reduction and the log part.

The Hermite and rational-logarithmic operations share the request-local
`RationalFunctionView` over the fixed default `Q[x]` representation.  The
rational-logarithmic checker, operation, elementary bootstrap registration,
workspace helper and REPL `integrate_log` are end-to-end; `bootstrap` and the
parameterized assemblies neither intern `HasRationalLogAntiderivative` nor
register the operation.  Algebraic residues, RootSum representations and
real-log branches remain outside the fragment, so I0 is not complete.
"""

from cas.math.calculus.integration.hermite_checker import HermiteChecker
from cas.math.calculus.integration.hermite_operation import (
    HermiteReductionOperation,
)
from cas.math.calculus.integration.hermite_specification import (
    HermiteCertificate,
    HermiteClaim,
    HermiteVocabulary,
)
from cas.math.calculus.integration.logarithmic_checker import (
    LogarithmicIntegrationChecker,
)
from cas.math.calculus.integration.logarithmic_operation import (
    LogarithmicIntegrationOperation,
)
from cas.math.calculus.integration.logarithmic_specification import (
    RationalLogAntiderivativeCertificate,
    RationalLogAntiderivativeClaim,
    RationalLogVocabulary,
    certificate_matches_claim,
    has_rational_log_antiderivative,
    parse_rational_log_antiderivative,
    parse_rational_log_terms,
    rational_log_antiderivative_term,
    rational_log_term,
    rational_log_term_set,
)
from cas.math.calculus.integration.operation import IntegrationOperation
from cas.math.calculus.integration.rational_view import RationalFunctionView
from cas.math.calculus.integration.service import (
    PolynomialAntiderivativeService,
)
from cas.math.calculus.integration.view import IntegrationView

__all__ = [
    "HermiteCertificate",
    "HermiteChecker",
    "HermiteClaim",
    "HermiteReductionOperation",
    "HermiteVocabulary",
    "IntegrationOperation",
    "IntegrationView",
    "LogarithmicIntegrationChecker",
    "LogarithmicIntegrationOperation",
    "PolynomialAntiderivativeService",
    "RationalFunctionView",
    "RationalLogAntiderivativeCertificate",
    "RationalLogAntiderivativeClaim",
    "RationalLogVocabulary",
    "certificate_matches_claim",
    "has_rational_log_antiderivative",
    "parse_rational_log_antiderivative",
    "parse_rational_log_terms",
    "rational_log_antiderivative_term",
    "rational_log_term",
    "rational_log_term_set",
]
