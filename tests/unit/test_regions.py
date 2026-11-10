"""Region specifications and their restricted certificates."""

import pytest
from support import head_app, runtime_proposition, variable

from cas.language import sorts as S
from cas.language.signatures import LanguageSignature, StructuralHead
from cas.runtime.bootstrap import bootstrap
from cas.semantics.conditions import condition_satisfiable
from cas.semantics.frames import Declaration
from cas.semantics.regions import (
    CoversCertificate,
    NonemptyCertificate,
    RegionSpec,
    SubregionCertificate,
    certify_covers,
    certify_nonempty,
    certify_subregion,
    region_from_proposition,
    verify_region_certificate,
)
from cas.syntax import term as T


def _region(runtime, term, coordinates=None, frame=None, sorts=None):
    proposition = runtime_proposition(runtime, term, frame=frame)
    if coordinates is None:
        coordinates = (runtime.variable,)
    if sorts is None:
        sorts = tuple((item, S.REAL) for item in coordinates)
    return RegionSpec(coordinates, proposition, sorts)


def _gt(runtime, bound=0):
    return head_app(
        runtime.signature,
        StructuralHead.GT,
        variable(runtime),
        T.number(bound),
    )


def _lt(runtime, bound=0):
    return head_app(
        runtime.signature,
        StructuralHead.LT,
        variable(runtime),
        T.number(bound),
    )


def _ne(runtime):
    return head_app(
        runtime.signature,
        StructuralHead.NE,
        variable(runtime),
        T.number(0),
    )


def _power(runtime, base, exponent):
    return head_app(
        runtime.signature,
        StructuralHead.POWER,
        base,
        T.number(exponent),
    )


def _and(runtime, *terms):
    return head_app(runtime.signature, StructuralHead.AND, *terms)


def _or(runtime, *terms):
    return head_app(runtime.signature, StructuralHead.OR, *terms)


def _child_frame(runtime, name="region_y", sort=S.REAL):
    symbol = runtime.table.intern(name)
    frame = runtime.frames.create(
        runtime.frame.id,
        declarations=(Declaration(symbol, name, sort),),
    )
    return symbol, frame


def test_region_spec_preserves_coordinate_order_and_meaning(runtime):
    symbol, frame = _child_frame(runtime)
    term = head_app(
        runtime.signature,
        StructuralHead.PLUS,
        variable(runtime),
        T.symbol(symbol, "region_y"),
    )
    condition = head_app(
        runtime.signature,
        StructuralHead.GT,
        term,
        T.number(0),
    )
    proposition = runtime_proposition(runtime, condition, frame=frame.id)
    spec = RegionSpec((symbol, runtime.variable), proposition)
    assert spec.coordinates == (symbol, runtime.variable)
    assert spec.condition is proposition
    assert spec.meaning == proposition.meaning


def test_region_spec_rejects_invalid_coordinates_and_conditions(runtime):
    true = runtime_proposition(runtime, T.TRUE)
    with pytest.raises(TypeError):
        RegionSpec((True,), true)
    with pytest.raises(ValueError):
        RegionSpec((runtime.variable, runtime.variable), true)
    with pytest.raises(TypeError):
        RegionSpec((runtime.variable,), T.TRUE)
    with pytest.raises(ValueError):
        RegionSpec((), runtime_proposition(runtime, _gt(runtime)))


def test_region_from_proposition_sorts_coordinates_deterministically(runtime):
    symbol, frame = _child_frame(runtime)
    condition = head_app(
        runtime.signature,
        StructuralHead.GT,
        head_app(
            runtime.signature,
            StructuralHead.PLUS,
            T.symbol(symbol, "region_y"),
            variable(runtime),
        ),
        T.number(0),
    )
    proposition = runtime_proposition(runtime, condition, frame=frame.id)
    region = region_from_proposition(proposition)
    assert region.condition is proposition
    assert region.coordinates == tuple(
        sorted((runtime.variable, symbol))
    )
    assert region.coordinates == (runtime.variable, symbol)
    assert region_from_proposition(proposition) == region
    with pytest.raises(TypeError):
        region_from_proposition(T.TRUE)


def test_condition_satisfiability_is_conservative(runtime):
    signature = runtime.signature
    assert condition_satisfiable(T.TRUE, signature) is True
    assert condition_satisfiable(T.FALSE, signature) is False
    assert condition_satisfiable(_gt(runtime), signature) is True
    assert (
        condition_satisfiable(_and(runtime, _gt(runtime), _lt(runtime)), signature)
        is False
    )
    assert condition_satisfiable(_or(runtime, _gt(runtime), _lt(runtime)), signature) is None

    power = head_app(
        runtime.signature,
        StructuralHead.POWER,
        variable(runtime),
        T.number(2),
    )
    nonlinear = head_app(
        runtime.signature,
        StructuralHead.GT,
        head_app(
            runtime.signature, StructuralHead.PLUS, power, T.number(1)
        ),
        T.number(0),
    )
    assert condition_satisfiable(nonlinear, signature) is None

    symbol, frame = _child_frame(runtime)
    multi_atom = head_app(
        runtime.signature,
        StructuralHead.GT,
        head_app(
            runtime.signature,
            StructuralHead.PLUS,
            variable(runtime),
            T.symbol(symbol, "region_y"),
        ),
        T.number(0),
    )
    proposition = runtime_proposition(runtime, multi_atom, frame=frame.id)
    assert proposition is not None
    assert condition_satisfiable(multi_atom, signature) is None


def test_certify_nonempty_accepts_ground_and_interval_regions(runtime):
    ground = RegionSpec(
        (), runtime_proposition(runtime, T.TRUE)
    )
    certificate = certify_nonempty(ground, runtime.signature)
    assert isinstance(certificate, NonemptyCertificate)
    assert verify_region_certificate(certificate, runtime.signature)

    interval = _region(runtime, _gt(runtime, 0))
    certificate = certify_nonempty(interval, runtime.signature)
    assert isinstance(certificate, NonemptyCertificate)
    assert verify_region_certificate(certificate, runtime.signature)


def test_certify_nonempty_rejects_false_and_unknown_regions(runtime):
    false = RegionSpec((), runtime_proposition(runtime, T.FALSE))
    assert certify_nonempty(false, runtime.signature) is None

    contradictory = _region(
        runtime, _and(runtime, _gt(runtime), _lt(runtime))
    )
    assert certify_nonempty(contradictory, runtime.signature) is None

    disjunctive = _region(
        runtime, _or(runtime, _gt(runtime), _lt(runtime))
    )
    assert certify_nonempty(disjunctive, runtime.signature) is None

    power = head_app(
        runtime.signature,
        StructuralHead.POWER,
        variable(runtime),
        T.number(2),
    )
    nonlinear = _region(
        runtime,
        head_app(
            runtime.signature,
            StructuralHead.GT,
            head_app(
                runtime.signature,
                StructuralHead.PLUS,
                power,
                T.number(1),
            ),
            T.number(0),
        ),
    )
    assert certify_nonempty(nonlinear, runtime.signature) is None


def test_certify_subregion_proves_inclusion_and_rejects_unknown(runtime):
    outer = _region(runtime, _gt(runtime, 0))
    inner = _region(runtime, _gt(runtime, 1))
    certificate = certify_subregion(inner, outer, runtime.signature)
    assert isinstance(certificate, SubregionCertificate)
    assert verify_region_certificate(certificate, runtime.signature)

    outside = _region(runtime, _lt(runtime, 0))
    assert certify_subregion(outside, outer, runtime.signature) is None

    symbol, frame = _child_frame(runtime)
    other = RegionSpec(
        (symbol,),
        runtime_proposition(
            runtime,
            head_app(
                runtime.signature,
                StructuralHead.GT,
                T.symbol(symbol, "region_y"),
                T.number(0),
            ),
            frame=frame.id,
        ),
        ((symbol, S.REAL),),
    )
    assert certify_subregion(other, outer, runtime.signature) is None

    empty = _region(
        runtime, _and(runtime, _gt(runtime), _lt(runtime))
    )
    assert certify_subregion(empty, outer, runtime.signature) is None


def test_a_subregion_certificate_is_rechecked_not_trusted(runtime):
    outer = _region(runtime, _gt(runtime, 0))
    inner = _region(runtime, _gt(runtime, 1))
    forged = SubregionCertificate(outer, inner, "forged")
    assert verify_region_certificate(forged, runtime.signature) is False

    genuine_with_label = SubregionCertificate(inner, outer, "not a proof")
    assert verify_region_certificate(
        genuine_with_label, runtime.signature
    )


def test_certify_covers_proves_identical_complementary_and_simple_cases(
    runtime,
):
    identical = _region(runtime, _gt(runtime, 0))
    certificate = certify_covers(
        identical, (identical,), runtime.signature
    )
    assert isinstance(certificate, CoversCertificate)
    assert verify_region_certificate(certificate, runtime.signature)

    union = _region(
        runtime, _or(runtime, _gt(runtime), _lt(runtime))
    )
    positive = _region(runtime, _gt(runtime))
    negative = _region(runtime, _lt(runtime))
    certificate = certify_covers(
        union, (positive, negative), runtime.signature
    )
    assert isinstance(certificate, CoversCertificate)
    assert verify_region_certificate(certificate, runtime.signature)

    outer = _region(runtime, _gt(runtime, 0))
    inner = _region(runtime, _gt(runtime, 1))
    certificate = certify_covers(
        outer, (inner, outer), runtime.signature
    )
    assert isinstance(certificate, CoversCertificate)
    assert verify_region_certificate(certificate, runtime.signature)


def test_certify_covers_rejects_unproved_and_empty_piece_sets(runtime):
    region = _region(runtime, _gt(runtime, 0))
    first = _region(runtime, _gt(runtime, 1))
    second = _region(runtime, _gt(runtime, 2))
    assert certify_covers(region, (first, second), runtime.signature) is None
    assert certify_covers(region, (), runtime.signature) is None


def test_covers_needs_an_or_head_for_multiple_pieces(runtime):
    heads = {
        symbol_id: head
        for symbol_id, head in runtime.signature.heads.items()
        if head is not StructuralHead.OR
    }
    signature = LanguageSignature.build(
        heads,
        binders=runtime.signature.binders,
        operators=runtime.signature.operators,
    )
    region = _region(runtime, _gt(runtime, 0))
    first = _region(runtime, _gt(runtime, 1))
    second = _region(runtime, _gt(runtime, 2))
    assert certify_covers(region, (first, second), signature) is None


def test_a_covers_certificate_is_rechecked_not_trusted(runtime):
    region = _region(runtime, _gt(runtime, 0))
    piece = _region(runtime, _gt(runtime, 1))
    forged = CoversCertificate(region, (piece,), "forged")
    assert verify_region_certificate(forged, runtime.signature) is False
    with pytest.raises(ValueError):
        CoversCertificate(region, (), "empty")


def test_region_certificates_require_one_meaning_environment(runtime):
    other = bootstrap()
    other_region = RegionSpec(
        (other.variable,),
        runtime_proposition(other, head_app(
            other.signature,
            StructuralHead.GT,
            variable(other),
            T.number(0),
        )),
    )
    runtime_region = _region(runtime, _gt(runtime, 0))
    with pytest.raises(ValueError):
        SubregionCertificate(other_region, runtime_region, "foreign")
    with pytest.raises(ValueError):
        CoversCertificate(
            other_region, (runtime_region,), "foreign"
        )


def test_certify_nonempty_accepts_a_condition_that_proves_its_premise(
    runtime,
):
    powered = _power(runtime, T.number(2), -1)
    condition = head_app(
        runtime.signature, StructuralHead.EQ, powered, powered
    )
    region = RegionSpec((), runtime_proposition(runtime, condition))
    assert tuple(
        premise.term for premise in region.condition.definedness
    ) == (
        head_app(
            runtime.signature,
            StructuralHead.NE,
            T.number(2),
            T.number(0),
        ),
    )
    certificate = certify_nonempty(region, runtime.signature)
    assert isinstance(certificate, NonemptyCertificate)
    assert verify_region_certificate(certificate, runtime.signature)


def test_certify_subregion_accepts_a_condition_that_proves_its_premise(
    runtime,
):
    powered = _power(runtime, variable(runtime), -1)
    condition = _and(
        runtime,
        _gt(runtime, 0),
        head_app(
            runtime.signature, StructuralHead.EQ, powered, powered
        ),
    )
    partial = _region(runtime, condition)
    assert tuple(
        premise.term for premise in partial.condition.definedness
    ) == (_ne(runtime),)
    outer = _region(runtime, _gt(runtime, 0))
    certificate = certify_subregion(
        partial, outer, runtime.signature
    )
    assert isinstance(certificate, SubregionCertificate)
    assert verify_region_certificate(certificate, runtime.signature)


def test_certify_nonempty_rejects_an_open_premise(runtime):
    powered = _power(runtime, variable(runtime), -1)
    condition = head_app(
        runtime.signature, StructuralHead.EQ, powered, powered
    )
    region = _region(runtime, condition)
    assert tuple(
        premise.term for premise in region.condition.definedness
    ) == (_ne(runtime),)
    assert certify_nonempty(region, runtime.signature) is None


def test_certify_subregion_rejects_an_open_premise(runtime):
    symbol, frame = _child_frame(runtime)
    y = T.symbol(symbol, "region_y")
    powered = _power(runtime, y, -1)
    condition = _and(
        runtime,
        _gt(runtime, 0),
        head_app(
            runtime.signature, StructuralHead.EQ, powered, powered
        ),
    )
    partial = RegionSpec(
        (runtime.variable, symbol),
        runtime_proposition(runtime, condition, frame=frame.id),
        ((runtime.variable, S.REAL), (symbol, S.REAL)),
    )
    outer = RegionSpec(
        (runtime.variable, symbol),
        runtime_proposition(runtime, _gt(runtime, 0), frame=frame.id),
        ((runtime.variable, S.REAL), (symbol, S.REAL)),
    )
    assert tuple(
        premise.term for premise in partial.condition.definedness
    ) == (
        head_app(
            runtime.signature, StructuralHead.NE, y, T.number(0)
        ),
    )
    assert certify_subregion(partial, outer, runtime.signature) is None


def test_certify_covers_rejects_a_piece_with_an_open_premise(runtime):
    symbol, frame = _child_frame(runtime)
    y = T.symbol(symbol, "region_y")
    region = RegionSpec(
        (runtime.variable, symbol),
        runtime_proposition(runtime, _gt(runtime, 0), frame=frame.id),
        ((runtime.variable, S.REAL), (symbol, S.REAL)),
    )
    powered = _power(runtime, y, -1)
    piece_condition = _and(
        runtime,
        _gt(runtime, 0),
        head_app(
            runtime.signature, StructuralHead.EQ, powered, powered
        ),
    )
    piece = RegionSpec(
        (runtime.variable, symbol),
        runtime_proposition(runtime, piece_condition, frame=frame.id),
        ((runtime.variable, S.REAL), (symbol, S.REAL)),
    )
    assert certify_covers(region, (piece,), runtime.signature) is None


def test_certify_covers_accepts_a_piece_that_proves_its_premise(runtime):
    region = _region(runtime, _gt(runtime, 0))
    powered = _power(runtime, T.number(2), -1)
    piece_condition = _and(
        runtime,
        _gt(runtime, 0),
        head_app(
            runtime.signature, StructuralHead.EQ, powered, powered
        ),
    )
    piece = _region(runtime, piece_condition)
    assert tuple(
        premise.term for premise in piece.condition.definedness
    ) == (
        head_app(
            runtime.signature,
            StructuralHead.NE,
            T.number(2),
            T.number(0),
        ),
    )
    certificate = certify_covers(
        region, (piece,), runtime.signature
    )
    assert isinstance(certificate, CoversCertificate)
    assert verify_region_certificate(certificate, runtime.signature)


def test_a_forged_certificate_over_a_partial_condition_is_rejected(runtime):
    powered = _power(runtime, variable(runtime), -1)
    condition = head_app(
        runtime.signature, StructuralHead.EQ, powered, powered
    )
    partial = _region(runtime, condition)
    outer = _region(runtime, _gt(runtime, 0))
    forged_subregion = SubregionCertificate(partial, outer, "forged")
    assert (
        verify_region_certificate(forged_subregion, runtime.signature)
        is False
    )
    forged_nonempty = NonemptyCertificate(partial, "forged")
    assert (
        verify_region_certificate(forged_nonempty, runtime.signature)
        is False
    )
    forged_covers = CoversCertificate(outer, (partial,), "forged")
    assert (
        verify_region_certificate(forged_covers, runtime.signature)
        is False
    )


def test_region_spec_records_canonical_binding_sorts(runtime):
    true = runtime_proposition(runtime, T.TRUE)
    region = RegionSpec(
        (runtime.variable,),
        true,
        ((runtime.variable, S.RATIONAL),),
    )
    assert region.sort_of(runtime.variable) is S.RATIONAL
    assert region.sort_of(999) is None
    assert region.sorts == ((runtime.variable, S.RATIONAL),)
    assert region.is_dense

    extra, frame = _child_frame(runtime, "sorted_region_y")
    condition = _gt(runtime, 0)
    proposition = runtime_proposition(runtime, condition, frame=frame.id)
    unordered = RegionSpec(
        (extra, runtime.variable),
        proposition,
        ((extra, S.REAL), (runtime.variable, S.RATIONAL)),
    )
    assert unordered.sorts == (
        (runtime.variable, S.RATIONAL),
        (extra, S.REAL),
    )
    assert unordered.is_dense
    assert unordered == RegionSpec(
        (extra, runtime.variable),
        proposition,
        ((runtime.variable, S.RATIONAL), (extra, S.REAL)),
    )


def test_region_spec_rejects_invalid_binding_sorts(runtime):
    true = runtime_proposition(runtime, T.TRUE)
    with pytest.raises(ValueError):
        RegionSpec(
            (runtime.variable,),
            true,
            ((runtime.variable, S.REAL), (runtime.variable, S.REAL)),
        )
    with pytest.raises(ValueError):
        RegionSpec(
            (runtime.variable,),
            true,
            ((runtime.variable, S.REAL), (999, S.REAL)),
        )
    with pytest.raises(ValueError):
        RegionSpec((runtime.variable,), true, ((999, S.REAL),))
    with pytest.raises(TypeError):
        RegionSpec((runtime.variable,), true, ((True, S.REAL),))
    with pytest.raises(TypeError):
        RegionSpec((runtime.variable,), true, ((runtime.variable,),))


def test_dense_order_certificates_are_refused_for_non_dense_regions(runtime):
    symbol, frame = _child_frame(runtime, "integer_region_y", S.INTEGER)
    y = T.symbol(symbol, "integer_region_y")
    between = _and(
        runtime,
        head_app(
            runtime.signature, StructuralHead.GT, T.number(0), y
        ),
        head_app(
            runtime.signature, StructuralHead.LT, y, T.number(1)
        ),
    )
    integer_region = RegionSpec(
        (symbol,),
        runtime_proposition(runtime, between, frame=frame.id),
        ((symbol, S.INTEGER),),
    )
    assert integer_region.is_dense is False
    # The raw interval fragment assumes a dense order and sees a nonempty
    # interval; the certificate layer must refuse before reading it.
    assert (
        condition_satisfiable(between, runtime.signature) is True
    )
    assert certify_nonempty(integer_region, runtime.signature) is None

    outer = RegionSpec(
        (symbol,),
        runtime_proposition(
            runtime,
            head_app(
                runtime.signature,
                StructuralHead.GT,
                y,
                T.number(0),
            ),
            frame=frame.id,
        ),
        ((symbol, S.INTEGER),),
    )
    assert certify_subregion(integer_region, outer, runtime.signature) is None
    forged_nonempty = NonemptyCertificate(integer_region, "forged")
    assert (
        verify_region_certificate(forged_nonempty, runtime.signature)
        is False
    )
    forged_subregion = SubregionCertificate(
        integer_region, outer, "forged"
    )
    assert (
        verify_region_certificate(forged_subregion, runtime.signature)
        is False
    )
    forged_covers = CoversCertificate(outer, (integer_region,), "forged")
    assert (
        verify_region_certificate(forged_covers, runtime.signature)
        is False
    )


def test_dense_order_certificates_are_refused_without_binding_sorts(runtime):
    region = RegionSpec(
        (runtime.variable,),
        runtime_proposition(runtime, _gt(runtime, 0)),
    )
    outer = _region(runtime, _gt(runtime, 0))
    assert region.is_dense is False
    assert certify_nonempty(region, runtime.signature) is None
    assert certify_subregion(region, outer, runtime.signature) is None
    assert certify_covers(outer, (region,), runtime.signature) is None
    assert (
        verify_region_certificate(
            NonemptyCertificate(region, "forged"), runtime.signature
        )
        is False
    )
    assert (
        verify_region_certificate(
            SubregionCertificate(region, outer, "forged"),
            runtime.signature,
        )
        is False
    )
    assert (
        verify_region_certificate(
            CoversCertificate(outer, (region,), "forged"),
            runtime.signature,
        )
        is False
    )


def test_rational_and_real_regions_still_certify(runtime):
    rational = RegionSpec(
        (runtime.variable,),
        runtime_proposition(runtime, _gt(runtime, 0)),
        ((runtime.variable, S.RATIONAL),),
    )
    real = _region(runtime, _gt(runtime, 0))
    for region in (rational, real):
        assert region.is_dense
        certificate = certify_nonempty(region, runtime.signature)
        assert isinstance(certificate, NonemptyCertificate)
        assert verify_region_certificate(
            certificate, runtime.signature
        )
