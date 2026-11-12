"""Fixed-seed Q[x] factorization-slice laws: search, product and trust."""

import random
from fractions import Fraction

from support import render_value, verification_context, view_of

from cas.algebra.factorization import factor_polynomial_over_q
from cas.frontend import parse
from cas.kernel.evidence import CheckRequest, InvalidEvidence
from cas.language.roles import CandidateRole
from cas.math.algebra.factorization_operation import (
    FactorizationOperation,
)
from cas.math.algebra.factorization_specification import (
    factorization_product_term,
    parse_factor_entries,
    rational_literal,
)
from cas.runtime.bootstrap import bootstrap, new_workspace
from cas.syntax import term as T
from cas.workflow.records import OperationStatus

SEED = 20261112

LINEAR = ("x", "x - 1", "x + 1", "x - 2", "x + 3")
QUADRATIC = ("x^2 + 1", "x^2 + x + 1", "x^2 + 2")
CUBIC = ("x^3 - 2", "x^3 + x + 1")
QUARTIC = ("x^4 + 1", "x^4 + x^3 + x^2 + x + 1")
IRREDUCIBLES = LINEAR + QUADRATIC + CUBIC + QUARTIC

UNITS = tuple(
    Fraction(value)
    for value in (-3, -2, -1, 1, 2, 3)
)


def operation(runtime):
    found = runtime.operations.get("factor_polynomial")
    assert isinstance(found, FactorizationOperation)
    return found


def value_of(runtime, text):
    term = parse(text, runtime.table, runtime.signature)
    return view_of(runtime, term).value


def random_factorization(rng, runtime):
    found = operation(runtime)
    bases = rng.sample(IRREDUCIBLES, rng.randint(1, 4))
    unit = rng.choice(UNITS)
    product = found.ring.constant(unit)
    for text in bases:
        multiplicity = rng.randint(1, 3)
        factor = value_of(runtime, text)
        product = found.ring.mul(
            product, found.ring.pow(factor, multiplicity)
        )
    return product, unit


def verified(runtime, value):
    workspace = new_workspace(runtime)
    source = workspace.intake(render_value(runtime, value), "source")
    result = workspace.factor_polynomial(source, runtime.variable)
    assert result.status is OperationStatus.VERIFIED, result.detail
    assert result.result is not None
    assert result.structured is not None
    candidate = result.candidate
    assert candidate is not None
    return workspace, source, result, candidate


def tampered_structured(candidate):
    assert candidate.structured is not None
    components = dict(candidate.structured)
    unit = rational_literal(components["unit"])
    assert unit is not None
    return (
        ("unit", T.number(unit + 1)),
        ("factors", components["factors"]),
    )


def test_random_products_factor_and_multiply_back_to_the_source():
    runtime = bootstrap()
    found = operation(runtime)
    rng = random.Random(SEED)
    for _ in range(8):
        value, unit = random_factorization(rng, runtime)
        _, _, result, candidate = verified(runtime, value)
        components = dict(candidate.structured or ())
        assert set(components) == {"unit", "factors"}
        assert rational_literal(components["unit"]) == unit
        entries = parse_factor_entries(
            runtime.signature, components["factors"]
        )
        assert entries is not None
        product = found.ring.constant(unit)
        rendered = view_of(runtime, T.number(1))
        for factor_term, multiplicity in entries:
            factor = view_of(runtime, factor_term).value
            product = found.ring.mul(
                product, found.ring.pow(factor, multiplicity)
            )
        assert found.ring.equal(product, value)
        record = factor_polynomial_over_q(found.ring, value)
        rendered_record = {
            runtime.bridge.render(rendered, factor).term: multiplicity
            for factor, multiplicity in record.factors
        }
        assert dict(entries) == rendered_record
        assert result.result is not None
        assert result.result.term == factorization_product_term(
            runtime.signature,
            components["unit"],
            components["factors"],
        )


def test_every_published_factor_term_is_monic_and_nonconstant():
    runtime = bootstrap()
    found = operation(runtime)
    rng = random.Random(SEED + 1)
    for _ in range(6):
        value, _ = random_factorization(rng, runtime)
        _, _, _, candidate = verified(runtime, value)
        components = dict(candidate.structured or ())
        entries = parse_factor_entries(
            runtime.signature, components["factors"]
        )
        assert entries is not None
        for factor_term, multiplicity in entries:
            assert multiplicity >= 1
            factor = view_of(runtime, factor_term).value
            degree = found.ring.degree(factor, 0)
            assert degree >= 1
            assert found.ring.coefficients.is_one(
                found.ring.coefficient(factor, (degree,))
            )


def test_tampering_one_structured_component_is_invalid_evidence():
    runtime = bootstrap()
    rng = random.Random(SEED + 2)
    checker = runtime.store.checkers.get("algebra.factorization")
    assert checker is not None
    for _ in range(4):
        value, _ = random_factorization(rng, runtime)
        _, _, _, candidate = verified(runtime, value)
        before = runtime.store.stats()
        outcome = checker.check(
            CheckRequest(
                candidate.frame,
                candidate.specifications,
                (),
                candidate.certificate,
                problem=candidate.problem,
                candidate=candidate.term,
                candidate_role=CandidateRole.RESULT,
                context=verification_context(
                    runtime,
                    candidate.frame,
                    algebra=candidate.algebra,
                ),
                structured=tampered_structured(candidate),
            )
        )
        assert isinstance(outcome, InvalidEvidence)
        assert runtime.store.stats() == before
