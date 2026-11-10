"""Parameter specialization: exact points, localizations and coverage."""

from fractions import Fraction

import pytest
from support import equation, head_app, runtime_proposition, variable

from cas.foundation.ids import SymbolId
from cas.language.problems import ParameterMode
from cas.language.signatures import StructuralHead
from cas.runtime import bootstrap_parameterized
from cas.semantics.regions import RegionSpec, region_from_proposition
from cas.semantics.specialization import (
    Applied,
    CoverageClaim,
    GenericResult,
    InvalidSpecialization,
    NeedsRecomputation,
    OutsideValidity,
    Specialization,
    specialize,
)
from cas.syntax import term as T


def setup():
    runtime = bootstrap_parameterized()
    a_id = runtime.request.parameters[0]
    a = T.symbol(a_id, "a")
    x = variable(runtime)
    true = runtime_proposition(runtime, T.TRUE)
    return runtime, a_id, a, x, true


def make_generic(
    runtime,
    true,
    result,
    *,
    valid_on=None,
    excluded=(),
    mode=ParameterMode.ALL_PARAMETER_VALUES,
):
    return GenericResult.assemble(
        result=result,
        valid_on=region_from_proposition(
            true if valid_on is None else valid_on
        ),
        excluded_cases=tuple(
            region_from_proposition(case) for case in excluded
        ),
        correctness_specification=true,
        parameter_mode=mode,
    )


def test_an_unconditional_point_substitutes_the_parameter():
    runtime, a_id, a, x, true = setup()
    result_term = head_app(
        runtime.signature, StructuralHead.TIMES, a, x
    )
    generic = make_generic(runtime, true, result_term)
    outcome = specialize(
        generic,
        runtime.request,
        Specialization({a_id: 3}),
        runtime.signature,
    )
    assert isinstance(outcome, Applied)
    expected = head_app(
        runtime.signature, StructuralHead.TIMES, T.number(3), x
    )
    assert outcome.result == expected
    assert outcome.specialization.values == {a_id: Fraction(3)}


def test_a_fractional_point_is_exact():
    runtime, a_id, a, x, true = setup()
    result_term = head_app(
        runtime.signature, StructuralHead.TIMES, a, x
    )
    outcome = specialize(
        make_generic(runtime, true, result_term),
        runtime.request,
        Specialization({a_id: Fraction(1, 2)}),
        runtime.signature,
    )
    assert isinstance(outcome, Applied)
    assert outcome.result == head_app(
        runtime.signature, StructuralHead.TIMES, T.number(Fraction(1, 2)), x
    )


def test_the_validity_region_is_checked_at_the_point():
    runtime, a_id, a, _, true = setup()
    valid_on = equation(runtime, a, T.number(0))
    generic = make_generic(runtime, true, a, valid_on=valid_on)
    assert generic.coverage_claim is CoverageClaim.PARTIAL

    inside = specialize(
        generic,
        runtime.request,
        Specialization({a_id: 0}),
        runtime.signature,
    )
    assert isinstance(inside, Applied)

    outside = specialize(
        generic,
        runtime.request,
        Specialization({a_id: 1}),
        runtime.signature,
    )
    assert isinstance(outside, OutsideValidity)
    assert isinstance(outside.valid_on, RegionSpec)
    assert outside.valid_on == region_from_proposition(valid_on)
    assert outside.valid_on.condition is valid_on


def test_an_excluded_case_forces_recomputation_only_when_it_holds():
    runtime, a_id, a, _, true = setup()
    excluded = equation(runtime, a, T.number(0))
    generic = make_generic(runtime, true, a, excluded=(excluded,))
    assert generic.coverage_claim is CoverageClaim.PARTIAL

    hits = specialize(
        generic,
        runtime.request,
        Specialization({a_id: 0}),
        runtime.signature,
    )
    assert isinstance(hits, NeedsRecomputation)
    assert hits.conditions == (region_from_proposition(excluded),)
    assert all(
        isinstance(case, RegionSpec) for case in hits.conditions
    )

    avoids = specialize(
        generic,
        runtime.request,
        Specialization({a_id: 1}),
        runtime.signature,
    )
    assert isinstance(avoids, Applied)


def test_an_undecidable_condition_is_not_treated_as_valid():
    runtime, a_id, a, x, true = setup()
    unresolved = equation(runtime, x, T.number(0))
    generic = make_generic(runtime, true, a, excluded=(unresolved,))
    outcome = specialize(
        generic,
        runtime.request,
        Specialization({a_id: 1}),
        runtime.signature,
    )
    assert isinstance(outcome, NeedsRecomputation)
    assert outcome.conditions == (region_from_proposition(unresolved),)


def test_arithmetic_and_logic_conditions_are_evaluated_exactly():
    runtime, a_id, a, _, true = setup()
    sum_is_two = head_app(
        runtime.signature,
        StructuralHead.EQ,
        head_app(
            runtime.signature, StructuralHead.PLUS, a, T.number(1)
        ),
        T.number(2),
    )
    generic = make_generic(
        runtime,
        true,
        a,
        valid_on=runtime_proposition(runtime, sum_is_two),
    )
    assert isinstance(
        specialize(
            generic,
            runtime.request,
            Specialization({a_id: 1}),
            runtime.signature,
        ),
        Applied,
    )
    assert isinstance(
        specialize(
            generic,
            runtime.request,
            Specialization({a_id: 2}),
            runtime.signature,
        ),
        OutsideValidity,
    )

    either = head_app(
        runtime.signature,
        StructuralHead.OR,
        equation(runtime, a, T.number(0)).term,
        equation(runtime, a, T.number(1)).term,
    )
    generic = make_generic(
        runtime,
        true,
        a,
        valid_on=runtime_proposition(runtime, either),
    )
    assert isinstance(
        specialize(
            generic,
            runtime.request,
            Specialization({a_id: 1}),
            runtime.signature,
        ),
        Applied,
    )
    assert isinstance(
        specialize(
            generic,
            runtime.request,
            Specialization({a_id: 2}),
            runtime.signature,
        ),
        OutsideValidity,
    )


def test_the_assignment_must_match_the_request_parameters():
    runtime, a_id, a, _, true = setup()
    generic = make_generic(runtime, true, a)
    missing = specialize(
        generic,
        runtime.request,
        Specialization({SymbolId(10_000): 1}),
        runtime.signature,
    )
    assert isinstance(missing, InvalidSpecialization)
    assert "missing" in missing.detail

    extra = specialize(
        generic,
        runtime.request,
        Specialization({a_id: 1, runtime.variable: 2}),
        runtime.signature,
    )
    assert isinstance(extra, InvalidSpecialization)
    assert "extra" in extra.detail


def test_a_specialization_needs_exact_nonempty_values():
    with pytest.raises(ValueError):
        Specialization({})
    with pytest.raises(TypeError):
        Specialization({SymbolId(1): True})
    with pytest.raises(TypeError):
        Specialization({SymbolId(1): "1"})  # type: ignore[dict-item]


def test_coverage_claims_follow_the_request_mode():
    runtime, _, a, _, true = setup()
    unconditional = make_generic(
        runtime, true, a, mode=ParameterMode.ALL_PARAMETER_VALUES
    )
    assert unconditional.coverage_claim is CoverageClaim.ALL_VALUES
    assert unconditional.is_unconditional

    generic = make_generic(
        runtime, true, a, mode=ParameterMode.GENERIC_PARAMETERS
    )
    assert generic.coverage_claim is CoverageClaim.GENERIC

    specified = make_generic(
        runtime, true, a, mode=ParameterMode.SPECIFIED_VALUES
    )
    assert specified.coverage_claim is CoverageClaim.SPECIFIED


def test_an_all_values_claim_cannot_hide_an_exception():
    runtime, _, a, _, true = setup()
    excluded = equation(runtime, a, T.number(0))
    true_region = region_from_proposition(true)
    excluded_region = region_from_proposition(excluded)
    with pytest.raises(ValueError):
        GenericResult(
            a,
            true_region,
            (excluded_region,),
            true,
            CoverageClaim.ALL_VALUES,
        )
    with pytest.raises(ValueError):
        GenericResult(
            a,
            region_from_proposition(equation(runtime, a, T.number(0))),
            (),
            true,
            CoverageClaim.ALL_VALUES,
        )


def test_generic_result_rejects_bare_propositions_as_regions():
    runtime, _, a, _, true = setup()
    excluded = equation(runtime, a, T.number(0))
    true_region = region_from_proposition(true)
    with pytest.raises(TypeError):
        GenericResult(
            a,
            true,
            (),
            true,
            CoverageClaim.PARTIAL,
        )
    with pytest.raises(TypeError):
        GenericResult(
            a,
            true_region,
            (excluded,),
            true,
            CoverageClaim.PARTIAL,
        )
    with pytest.raises(TypeError):
        GenericResult(
            a,
            true_region,
            (),
            T.TRUE,
            CoverageClaim.PARTIAL,
        )
    with pytest.raises(TypeError):
        GenericResult(
            a,
            true_region,
            (),
            true,
            "partial",
        )


def _power(runtime, base, exponent):
    return head_app(
        runtime.signature, StructuralHead.POWER, base, T.number(exponent)
    )


def _ne(runtime, left):
    return head_app(
        runtime.signature, StructuralHead.NE, left, T.number(0)
    )


def test_a_partial_validity_region_is_outside_when_a_premise_is_false():
    runtime, a_id, a, _, true = setup()
    valid_on = runtime_proposition(
        runtime,
        head_app(
            runtime.signature,
            StructuralHead.EQ,
            _power(runtime, a, -1),
            T.number(1),
        ),
    )
    assert tuple(
        premise.term for premise in valid_on.definedness
    ) == (_ne(runtime, a),)
    generic = make_generic(runtime, true, a, valid_on=valid_on)
    outcome = specialize(
        generic,
        runtime.request,
        Specialization({a_id: 0}),
        runtime.signature,
    )
    assert isinstance(outcome, OutsideValidity)
    assert outcome.valid_on == region_from_proposition(valid_on)


def test_an_undecidable_validity_premise_requires_recomputation():
    runtime, a_id, a, x, true = setup()
    valid_on = runtime_proposition(
        runtime,
        head_app(
            runtime.signature,
            StructuralHead.EQ,
            _power(runtime, x, -1),
            T.number(1),
        ),
    )
    assert valid_on.definedness
    generic = make_generic(runtime, true, a, valid_on=valid_on)
    outcome = specialize(
        generic,
        runtime.request,
        Specialization({a_id: 2}),
        runtime.signature,
    )
    assert isinstance(outcome, NeedsRecomputation)
    assert outcome.conditions == (region_from_proposition(valid_on),)


def test_a_true_premise_with_a_true_condition_is_applied():
    runtime, a_id, a, _, true = setup()
    condition = head_app(
        runtime.signature,
        StructuralHead.AND,
        _ne(runtime, a),
        head_app(
            runtime.signature,
            StructuralHead.EQ,
            _power(runtime, a, -1),
            T.number(1),
        ),
    )
    valid_on = runtime_proposition(runtime, condition)
    assert tuple(
        premise.term for premise in valid_on.definedness
    ) == (_ne(runtime, a),)
    generic = make_generic(runtime, true, a, valid_on=valid_on)
    outcome = specialize(
        generic,
        runtime.request,
        Specialization({a_id: 1}),
        runtime.signature,
    )
    assert isinstance(outcome, Applied)
    assert outcome.result == T.number(1)


def test_an_excluded_case_with_a_false_premise_does_not_apply():
    runtime, a_id, a, _, true = setup()
    excluded = runtime_proposition(
        runtime,
        head_app(
            runtime.signature,
            StructuralHead.EQ,
            _power(runtime, a, -1),
            T.number(1),
        ),
    )
    assert excluded.definedness
    generic = make_generic(runtime, true, a, excluded=(excluded,))
    outcome = specialize(
        generic,
        runtime.request,
        Specialization({a_id: 0}),
        runtime.signature,
    )
    assert isinstance(outcome, Applied)


def test_an_excluded_case_with_an_undecidable_premise_requires_recomputation():
    runtime, a_id, a, x, true = setup()
    excluded = runtime_proposition(
        runtime,
        head_app(
            runtime.signature,
            StructuralHead.EQ,
            _power(runtime, x, -1),
            T.number(1),
        ),
    )
    assert excluded.definedness
    generic = make_generic(runtime, true, a, excluded=(excluded,))
    outcome = specialize(
        generic,
        runtime.request,
        Specialization({a_id: 1}),
        runtime.signature,
    )
    assert isinstance(outcome, NeedsRecomputation)
    assert outcome.conditions == (region_from_proposition(excluded),)
