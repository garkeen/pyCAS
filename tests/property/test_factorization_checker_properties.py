"""Fixed-seed properties for the independent `HasFactorization` checker."""

import random
from dataclasses import replace
from fractions import Fraction

from factorization_support import (
    check_bundle,
    factorization_setup,
    render,
    valid_bundle,
)
from support import verification_context

from cas.kernel.evidence import InvalidEvidence, Verified
from cas.language.roles import CandidateRole
from cas.semantics.bridge import AlgebraView, typed_view
from cas.syntax import term as T

_SEED = 20261111
_UNITS = (1, -1, 2, 3, Fraction(1, 2))


def _random_value(ring, rng: random.Random):
    """A product of known factors with bounded total degree."""
    x = ring.generator(0)
    one = ring.one()
    candidates = (
        x,
        ring.sub(x, one),
        ring.add(x, one),
        ring.sub(x, ring.constant(Fraction(2))),
        ring.add(ring.pow(x, 2), one),
        ring.add(ring.pow(x, 2), ring.constant(Fraction(2))),
    )
    value = ring.constant(Fraction(rng.choice(_UNITS)))
    degree = 0
    for _ in range(rng.randint(0, 3)):
        factor = rng.choice(candidates)
        multiplicity = rng.randint(1, 2)
        added = ring.degree(factor, 0) * multiplicity
        if degree + added > 6:
            continue
        value = ring.mul(value, ring.pow(factor, multiplicity))
        degree += added
    return value


def _value_from_term(setup, term):
    view = typed_view(
        setup.runtime.bridge,
        term,
        setup.runtime.frames,
        setup.frame,
        setup.signature,
        setup.runtime.request,
    )
    assert isinstance(view, AlgebraView), view
    return view.value


def test_random_known_products_are_verified(runtime):
    setup = factorization_setup(runtime)
    ring = setup.runtime.ring
    rng = random.Random(_SEED)
    for _ in range(12):
        value = _random_value(ring, rng)
        bundle = valid_bundle(setup, value)
        outcome = check_bundle(setup, bundle)
        assert isinstance(outcome, Verified), (
            render(setup, value),
            outcome,
        )
        assert outcome.checked == (bundle.proposition,)
        nonlinear = any(
            ring.degree(_value_from_term(setup, term), 0) >= 2
            for term, _ in bundle.entries
        )
        assert (
            bundle.certificate.irreducibility is not None
        ) == nonlinear


def test_tampering_one_component_is_not_verified(runtime):
    setup = factorization_setup(runtime)
    rng = random.Random(_SEED + 1)
    for _ in range(12):
        value = _random_value(setup.runtime.ring, rng)
        bundle = valid_bundle(setup, value)
        assert isinstance(check_bundle(setup, bundle), Verified)
        wrong_structured = check_bundle(
            setup, bundle, structured=None
        )
        assert isinstance(wrong_structured, InvalidEvidence)
        wrong_candidate = check_bundle(
            setup, bundle, candidate=T.number(0)
        )
        assert isinstance(wrong_candidate, InvalidEvidence)
        assert isinstance(
            check_bundle(setup, bundle, role=CandidateRole.SOURCE),
            InvalidEvidence,
        )
        assert isinstance(
            check_bundle(
                setup,
                bundle,
                context=verification_context(
                    setup.runtime, setup.frame
                ),
            ),
            InvalidEvidence,
        )
        witness = bundle.certificate.irreducibility
        if witness is not None:
            tampered = replace(
                witness,
                lifted=(T.number(0), *witness.lifted[1:]),
            )
            claimed = replace(bundle.certificate, irreducibility=tampered)
            outcome = check_bundle(
                setup, bundle, certificate=claimed
            )
            assert isinstance(outcome, InvalidEvidence), outcome
