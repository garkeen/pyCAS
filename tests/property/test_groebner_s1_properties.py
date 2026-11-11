"""Fixed-seed Groebner-slice laws: canonical basis and certificate trust."""

import random
from fractions import Fraction

from support import verification_context, view_of

from cas.frontend.session import Session
from cas.kernel.evidence import CheckRequest, InvalidEvidence
from cas.language.roles import CandidateRole
from cas.math.algebra.groebner_operation import GroebnerOperation
from cas.math.algebra.groebner_specification import GroebnerCertificate
from cas.runtime.bootstrap import bootstrap, new_workspace
from cas.semantics.bridge import Rendered
from cas.syntax import term as T
from cas.workflow.records import OperationStatus

SEED = 20261111


def random_polynomial(rng, ring, *, max_degree=2):
    value = ring.zero()
    for _ in range(rng.randint(1, 4)):
        exponents = (
            rng.randint(0, max_degree),
            rng.randint(0, max_degree),
        )
        coefficient = Fraction(
            rng.randint(-3, 3), rng.randint(1, 3)
        )
        value = ring.add(value, ring.monomial(exponents, coefficient))
    return value


def random_system(rng, ring, *, count=3):
    return tuple(random_polynomial(rng, ring) for _ in range(count))


def groebner_operation(runtime):
    found = runtime.operations.get("groebner_basis")
    assert isinstance(found, GroebnerOperation)
    return found


def render(runtime, value):
    found = groebner_operation(runtime)
    view = view_of(
        runtime,
        T.number(0),
        bridge=found.bridge,
        request=found.request,
    )
    rendered = found.bridge.render(view, value)
    assert isinstance(rendered, Rendered)
    return rendered.term


def verified_basis(runtime, terms):
    workspace = new_workspace(runtime)
    expressions = tuple(
        workspace.intake(term, f"g{index}")
        for index, term in enumerate(terms)
    )
    result = workspace.groebner_basis(expressions)
    assert result.status is OperationStatus.VERIFIED, result.detail
    assert result.result is not None
    return result


def test_the_verified_basis_is_invariant_under_permutation_and_scaling():
    runtime = bootstrap()
    found = groebner_operation(runtime)
    rng = random.Random(SEED)
    for _ in range(8):
        generators = random_system(rng, found.ring)
        base = verified_basis(
            runtime, tuple(render(runtime, value) for value in generators)
        )
        transformed = [
            found.ring.mul(
                found.ring.constant(
                    Fraction(
                        rng.choice([-3, -2, -1, 2, 3]),
                        rng.randint(1, 3),
                    )
                ),
                value,
            )
            for value in generators
        ]
        rng.shuffle(transformed)
        alternate = verified_basis(
            runtime,
            tuple(render(runtime, value) for value in transformed),
        )
        assert alternate.result.term == base.result.term


def test_the_verified_basis_is_invariant_under_redundant_generators():
    runtime = bootstrap()
    found = groebner_operation(runtime)
    rng = random.Random(SEED + 1)
    for _ in range(8):
        generators = random_system(rng, found.ring)
        base = verified_basis(
            runtime, tuple(render(runtime, value) for value in generators)
        )
        redundant = generators + (
            found.ring.add(generators[0], generators[-1]),
            found.ring.zero(),
        )
        alternate = verified_basis(
            runtime, tuple(render(runtime, value) for value in redundant)
        )
        assert alternate.result.term == base.result.term


def test_a_tampered_cofactor_certificate_is_invalid_evidence():
    session = Session(bootstrap())
    session.execute("x^2 + y^2 - 1")
    session.execute("x - y")
    session.execute("groebner_basis @E0 @E1")
    runtime = session.runtime
    candidate = session.workspace.candidates()[0]
    certificate = candidate.certificate
    assert isinstance(certificate, GroebnerCertificate)
    checker = runtime.store.checkers.get("algebra.groebner")
    assert checker is not None
    tampered_rows = [
        list(row) for row in certificate.cofactors
    ]
    tampered_rows[0] = [T.number(0) for _ in tampered_rows[0]]
    tampered = GroebnerCertificate(
        tuple(tuple(row) for row in tampered_rows)
    )
    context = verification_context(
        runtime, candidate.frame, algebra=candidate.algebra
    )
    for supplied in (
        GroebnerCertificate(()),
        tampered,
    ):
        outcome = checker.check(
            CheckRequest(
                candidate.frame,
                candidate.specifications,
                (),
                supplied,
                problem=candidate.problem,
                candidate=candidate.term,
                candidate_role=CandidateRole.SET,
                context=context,
            )
        )
        assert isinstance(outcome, InvalidEvidence), outcome
