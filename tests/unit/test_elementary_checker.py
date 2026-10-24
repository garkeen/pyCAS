"""Independent checker for the declared elementary fragment."""

from support import runtime_proposition, variable

from cas.frontend import parse
from cas.kernel.evidence import (
    CheckRequest,
    InvalidEvidence,
    Unverified,
    Verified,
)
from cas.language.decisions import Reason
from cas.math.calculus.differentiation.elementary_checker import (
    ElementaryDerivativeCertificate,
)
from cas.math.calculus.differentiation.specification import has_derivative
from cas.runtime import bootstrap_elementary
from cas.syntax import term as T


def setup():
    runtime = bootstrap_elementary()
    return runtime


def term(runtime, text):
    return parse(text, runtime.table, runtime.signature)


def claim(runtime, source, candidate, region=None, variable_term=None):
    return runtime_proposition(
        runtime,
        has_derivative(
            runtime.vocabulary,
            T.TRUE if region is None else region,
            source,
            variable(runtime) if variable_term is None else variable_term,
            candidate,
        ),
    )


def certificate(runtime, source, candidate, region=None, variable_term=None):
    return ElementaryDerivativeCertificate(
        T.TRUE if region is None else region,
        source,
        runtime.variable if variable_term is None else variable_term.symbol_id,
        candidate,
    )


def check(runtime, proposition, cert):
    return runtime.checker.check(
        CheckRequest(runtime.frame.id, (proposition,), (), cert)
    )


def test_the_checker_accepts_the_expected_candidate():
    runtime = setup()
    source = term(runtime, "sin(x)")
    candidate = term(runtime, "cos(x)")
    outcome = check(
        runtime,
        claim(runtime, source, candidate),
        certificate(runtime, source, candidate),
    )
    assert isinstance(outcome, Verified)
    assert outcome.checked == (claim(runtime, source, candidate),)


def test_a_different_candidate_is_unverified_not_refuted():
    runtime = setup()
    source = term(runtime, "sin(x)")
    wrong = term(runtime, "-cos(x)")
    outcome = check(
        runtime,
        claim(runtime, source, wrong),
        certificate(runtime, source, wrong),
    )
    assert isinstance(outcome, Unverified)
    assert outcome.reason is Reason.FRAGMENT
    assert "verified derivative" in outcome.detail


def test_a_differently_shaped_equivalent_candidate_is_not_refuted():
    runtime = setup()
    source = term(runtime, "sin(x)")
    candidate = term(runtime, "cos(x)*1")
    outcome = check(
        runtime,
        claim(runtime, source, candidate),
        certificate(runtime, source, candidate),
    )
    assert isinstance(outcome, Unverified)
    assert outcome.reason is Reason.FRAGMENT


def test_a_certificate_must_match_the_claim():
    runtime = setup()
    source = term(runtime, "sin(x)")
    candidate = term(runtime, "cos(x)")
    other = term(runtime, "exp(x)")
    outcome = check(
        runtime,
        claim(runtime, source, candidate),
        certificate(runtime, other, candidate),
    )
    assert isinstance(outcome, InvalidEvidence)
    assert "does not match" in outcome.detail


def test_the_conclusion_must_be_a_derivative_specification():
    runtime = setup()
    proposition = runtime_proposition(runtime, term(runtime, "sin(x) > 0"))
    outcome = check(
        runtime,
        proposition,
        certificate(runtime, T.number(1), T.number(0)),
    )
    assert isinstance(outcome, InvalidEvidence)


def test_a_different_region_is_unverified():
    runtime = setup()
    source = term(runtime, "sin(x)")
    candidate = term(runtime, "cos(x)")
    region = term(runtime, "x > 0")
    outcome = check(
        runtime,
        claim(runtime, source, candidate, region=region),
        certificate(runtime, source, candidate, region=region),
    )
    assert isinstance(outcome, Unverified)
    assert outcome.reason is Reason.FRAGMENT
    assert "region" in outcome.detail


def test_the_claim_must_use_this_fragments_variable():
    runtime = setup()
    source = term(runtime, "sin(x)")
    candidate = term(runtime, "cos(x)")
    pi = T.symbol(runtime.elementary.constants["pi"].symbol, "pi")
    outcome = check(
        runtime,
        claim(runtime, source, candidate, variable_term=pi),
        certificate(runtime, source, candidate, variable_term=pi),
    )
    assert isinstance(outcome, Unverified)
    assert outcome.reason is Reason.FRAGMENT


def test_conditional_claims_are_verified_on_their_region():
    runtime = setup()
    source = term(runtime, "sqrt(x)")
    candidate = term(runtime, "1/2*sqrt(x)^-1")
    region = term(runtime, "x >= 0 and x > 0")
    outcome = check(
        runtime,
        claim(runtime, source, candidate, region=region),
        certificate(runtime, source, candidate, region=region),
    )
    assert isinstance(outcome, Verified)

    without_region = check(
        runtime,
        claim(runtime, source, candidate),
        certificate(runtime, source, candidate),
    )
    assert isinstance(without_region, Unverified)
    assert without_region.reason is Reason.FRAGMENT
    assert "region" in without_region.detail

    wrong_candidate = check(
        runtime,
        claim(runtime, source, T.number(0), region=region),
        certificate(runtime, source, T.number(0), region=region),
    )
    assert isinstance(wrong_candidate, Unverified)


def test_a_weaker_region_is_unverified():
    runtime = setup()
    source = term(runtime, "sqrt(x)")
    candidate = term(runtime, "1/2*sqrt(x)^-1")
    region = term(runtime, "x >= 0")
    outcome = check(
        runtime,
        claim(runtime, source, candidate, region=region),
        certificate(runtime, source, candidate, region=region),
    )
    assert isinstance(outcome, Unverified)
    assert "region" in outcome.detail
