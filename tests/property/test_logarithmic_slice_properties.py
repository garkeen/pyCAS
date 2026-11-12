"""Fixed-seed properties of the rational-logarithmic vertical slice.

Every generated source is an exact logarithmic derivative
``D(v) + sum(c_i * g_i'/g_i)``.  The workspace must integrate it through the
registered operation, the independent checker must re-prove the resulting
claim, and the recorded structured components must reproduce the source when
differentiated again.  A tampered structured component or certificate must
never be verified and must not write to the ledger.
"""

import random
from dataclasses import replace
from fractions import Fraction

from logarithmic_support import (
    log_setup,
    monic_product,
    polynomial,
    render,
)

from cas.kernel.evidence import (
    AlgebraService,
    CheckRequest,
    DecisionService,
    DefinednessService,
    InvalidEvidence,
    VerificationContext,
    Verified,
)
from cas.language.roles import CandidateRole
from cas.math.calculus.integration.logarithmic_specification import (
    RationalLogAntiderivativeCertificate,
    parse_rational_log_antiderivative,
    parse_rational_log_terms,
)
from cas.runtime.bootstrap import bootstrap_elementary, new_workspace
from cas.semantics.bridge import AlgebraView, typed_view
from cas.semantics.frames import FrameSorts
from cas.syntax import term as T
from cas.workflow.records import OperationStatus

_SEED = 20261112
_ROOTS = tuple(range(-5, 6))
_COEFFICIENTS = (
    Fraction(1),
    Fraction(-1),
    Fraction(1, 2),
    Fraction(-1, 2),
    Fraction(2),
    Fraction(-2),
    Fraction(1, 3),
    Fraction(-1, 3),
)


def random_case(setup, rng: random.Random):
    """A rendered source term, its polynomial part and its log terms."""
    field = setup.bridge.field
    ring = field.polynomials
    term_count = rng.randint(1, 3)
    coefficients = rng.sample(_COEFFICIENTS, term_count)
    available = list(_ROOTS)
    rng.shuffle(available)
    entries = []
    for coefficient in coefficients:
        size = rng.randint(1, 2)
        roots = tuple(available.pop() for _ in range(size))
        entries.append((coefficient, monic_product(setup, roots)))
    degree = rng.randint(0, 2)
    part = polynomial(
        setup,
        tuple(
            (exponent, Fraction(rng.randint(-2, 2)))
            for exponent in range(degree + 1)
        ),
    )
    value = field.derivative(field.of_polynomial(part))
    for coefficient, argument in entries:
        value = field.add(
            value,
            field.fraction(
                ring.mul(
                    ring.constant(coefficient),
                    ring.derivative(argument, 0),
                ),
                argument,
            ),
        )
    return render(setup, value), part, entries


def field_view(runtime, bridge, request, term):
    outcome = typed_view(
        bridge,
        term,
        runtime.frames,
        runtime.frame.id,
        runtime.signature,
        request,
    )
    assert isinstance(outcome, AlgebraView), outcome
    return outcome


def rebound_source(runtime, operation, structured, claim):
    """Differentiate the recorded polynomial part and log terms."""
    view = operation.views[0]
    field = view.field
    ring = field.polynomials
    total = field.derivative(
        field_view(
            runtime,
            view.bridge,
            view.request,
            structured["polynomial_part"],
        ).value
    )
    entries = parse_rational_log_terms(
        runtime.signature,
        operation.vocabulary.log_function,
        structured["log_terms"],
    )
    assert entries is not None
    for coefficient, argument_term in entries:
        argument_view = field_view(
            runtime, view.bridge, view.request, argument_term
        )
        assert ring.is_constant(argument_view.value.denominator)
        argument = argument_view.value.numerator
        total = field.add(
            total,
            field.fraction(
                ring.mul(
                    ring.constant(coefficient),
                    ring.derivative(argument, 0),
                ),
                argument,
            ),
        )
    source_view = field_view(
        runtime, view.bridge, view.request, claim.source
    )
    return field.equal(total, source_view.value)


def test_random_logarithmic_derivatives_verify_through_the_workspace():
    runtime = bootstrap_elementary()
    setup = log_setup(runtime)
    workspace = new_workspace(runtime)
    found = runtime.operations.get("integrate_rational_logarithmic")
    assert found is not None
    rng = random.Random(_SEED)
    for _ in range(6):
        term, _, _ = random_case(setup, rng)
        first = workspace.intake(term, "source")
        result = workspace.integrate_rational_logarithmic(
            first, runtime.variable
        )
        assert result.status in (
            OperationStatus.VERIFIED,
            OperationStatus.CONDITIONAL,
        ), result.detail
        assert result.result is not None
        assert result.structured is not None
        assert result.verifications
        assert (
            result.verifications[0].status is OperationStatus.VERIFIED
        )
        candidate = result.candidate
        assert candidate is not None
        claim = parse_rational_log_antiderivative(
            found.vocabulary, candidate.specifications[0].term
        )
        assert claim is not None
        structured = dict(result.structured.components)
        assert tuple(structured) == ("polynomial_part", "log_terms")
        assert rebound_source(runtime, found, structured, claim)


def test_a_tampered_component_is_not_verified_and_writes_nothing():
    runtime = bootstrap_elementary()
    setup = log_setup(runtime)
    workspace = new_workspace(runtime)
    found = runtime.operations.get("integrate_rational_logarithmic")
    assert found is not None
    rng = random.Random(_SEED + 1)
    term, _, _ = random_case(setup, rng)
    first = workspace.intake(term, "source")
    result = workspace.integrate_rational_logarithmic(
        first, runtime.variable
    )
    candidate = result.candidate
    assert candidate is not None
    assert result.structured is not None
    claim = parse_rational_log_antiderivative(
        found.vocabulary, candidate.specifications[0].term
    )
    assert claim is not None
    certificate = candidate.certificate
    assert isinstance(certificate, RationalLogAntiderivativeCertificate)

    view = found.views[0]
    decision = DecisionService(
        runtime.signature,
        FrameSorts(runtime.frames, runtime.frame.id),
    )
    context = VerificationContext(
        runtime.world.id,
        runtime.frame.id,
        runtime.frames,
        decision=decision,
        definedness=DefinednessService(
            decision, runtime.frames, runtime.frame.id
        ),
        algebra=AlgebraService(view.request),
    )
    checker_id = found.checker_bindings[0].checker_id
    spec = runtime.store.checkers.spec(checker_id)
    assert spec is not None

    def check(certificate, structured):
        return spec.checker.check(
            CheckRequest(
                runtime.frame.id,
                candidate.specifications,
                (),
                certificate,
                problem=candidate.problem,
                candidate=candidate.term,
                candidate_role=CandidateRole.RESULT,
                context=context,
                structured=structured,
            )
        )

    before = runtime.store.stats()
    honest = check(
        certificate,
        (
            ("polynomial_part", claim.polynomial_part),
            ("log_terms", claim.log_terms),
        ),
    )
    assert isinstance(honest, Verified)
    tampered_structured = check(
        certificate,
        (
            ("polynomial_part", claim.log_terms),
            ("log_terms", claim.polynomial_part),
        ),
    )
    assert isinstance(tampered_structured, InvalidEvidence)
    tampered_certificate = check(
        replace(certificate, source=T.number(0)),
        (
            ("polynomial_part", claim.polynomial_part),
            ("log_terms", claim.log_terms),
        ),
    )
    assert isinstance(tampered_certificate, InvalidEvidence)
    assert runtime.store.stats() == before
