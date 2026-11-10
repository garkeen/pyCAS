"""Definedness records and the exactness evidence they carry."""

from dataclasses import replace

import pytest
from support import head_app, runtime_proposition, typed_in, variable, view_of

from cas.language import sorts as S
from cas.language.problems import Role
from cas.language.signatures import StructuralHead
from cas.math.calculus.integration.hermite_checker import HermiteChecker
from cas.semantics.bridge import (
    AlgebraView,
    ConversionWitness,
    SymbolBinding,
    _issue_view,
)
from cas.semantics.definedness import (
    Definedness,
    DefinednessExactness,
    _issue_definedness,
)
from cas.semantics.frames import Declaration
from cas.semantics.regions import (
    RegionSpec,
    SubregionCertificate,
    verify_region_certificate,
)
from cas.semantics.request import Interpretation
from cas.syntax import term as T


def _typed(runtime, term=None):
    source = variable(runtime) if term is None else term
    return typed_in(
        runtime.frames, runtime.frame.id, runtime.signature, source
    )


def _region(runtime, term):
    return RegionSpec(
        (runtime.variable,),
        runtime_proposition(runtime, term),
        ((runtime.variable, S.REAL),),
    )


def _ne(runtime):
    return head_app(
        runtime.signature,
        StructuralHead.NE,
        variable(runtime),
        T.number(0),
    )


def _gt(runtime, bound=0):
    return head_app(
        runtime.signature,
        StructuralHead.GT,
        variable(runtime),
        T.number(bound),
    )


def _power(runtime, base, exponent):
    return head_app(
        runtime.signature, StructuralHead.POWER, base, T.number(exponent)
    )


def test_total_definedness_carries_no_regions_or_certificate(runtime):
    source = _typed(runtime)
    record = _issue_definedness(
        source, None, None, DefinednessExactness.TOTAL
    )
    assert record.source is source
    assert record.domain is None
    assert record.valid_on is None
    assert record.certificate is None

    with pytest.raises(ValueError):
        _issue_definedness(
            source,
            _region(runtime, T.TRUE),
            None,
            DefinednessExactness.TOTAL,
        )
    with pytest.raises(ValueError):
        _issue_definedness(
            source,
            None,
            None,
            DefinednessExactness.TOTAL,
            SubregionCertificate(
                _region(runtime, T.TRUE),
                _region(runtime, T.TRUE),
                "unexpected",
            ),
        )


def test_exact_definedness_accepts_the_same_validity_region(runtime):
    source = _typed(runtime)
    domain = _region(runtime, _ne(runtime))
    without_validity = _issue_definedness(
        source, domain, None, DefinednessExactness.EXACT
    )
    assert without_validity.domain == domain
    assert without_validity.valid_on is None
    assert without_validity.certificate is None

    with_validity = _issue_definedness(
        source, domain, domain, DefinednessExactness.EXACT
    )
    assert with_validity.valid_on == domain
    assert with_validity.certificate is None

    with pytest.raises(ValueError):
        _issue_definedness(
            source,
            domain,
            _region(runtime, _gt(runtime)),
            DefinednessExactness.EXACT,
        )


def test_sufficient_definedness_requires_a_matching_certificate(runtime):
    source = _typed(runtime)
    domain = _region(runtime, T.TRUE)
    valid_on = _region(runtime, _ne(runtime))
    certificate = SubregionCertificate(valid_on, domain, "restricted")
    record = _issue_definedness(
        source,
        domain,
        valid_on,
        DefinednessExactness.SUFFICIENT,
        certificate,
    )
    assert record.certificate is certificate
    assert verify_region_certificate(certificate, runtime.signature)

    with pytest.raises(ValueError):
        _issue_definedness(
            source,
            domain,
            valid_on,
            DefinednessExactness.SUFFICIENT,
        )
    with pytest.raises(ValueError):
        _issue_definedness(
            source,
            domain,
            valid_on,
            DefinednessExactness.SUFFICIENT,
            SubregionCertificate(domain, valid_on, "swapped"),
        )
    with pytest.raises(ValueError):
        _issue_definedness(
            source,
            domain,
            domain,
            DefinednessExactness.SUFFICIENT,
            certificate,
        )
    with pytest.raises(ValueError):
        _issue_definedness(
            source,
            None,
            valid_on,
            DefinednessExactness.SUFFICIENT,
            certificate,
        )


def test_definedness_coordinates_must_contain_the_source_binding_view(runtime):
    source = _typed(runtime)
    empty_coordinates = RegionSpec(
        (), runtime_proposition(runtime, T.TRUE)
    )
    with pytest.raises(ValueError):
        _issue_definedness(
            source,
            empty_coordinates,
            None,
            DefinednessExactness.EXACT,
        )

    foreign_coordinate = RegionSpec(
        (999,), runtime_proposition(runtime, T.TRUE)
    )
    with pytest.raises(ValueError):
        _issue_definedness(
            source,
            foreign_coordinate,
            None,
            DefinednessExactness.EXACT,
        )

    extra = runtime.table.intern("definedness_extra")
    child = runtime.frames.create(
        runtime.frame.id,
        declarations=(Declaration(extra, "definedness_extra", S.REAL),),
    )
    condition = runtime_proposition(runtime, _ne(runtime), frame=child.id)
    larger = RegionSpec((extra, runtime.variable), condition)
    record = _issue_definedness(
        source, larger, None, DefinednessExactness.EXACT
    )
    assert record.domain == larger
    assert record.domain.coordinates == (extra, runtime.variable)


def test_a_polynomial_view_definedness_is_total(runtime):
    view = view_of(runtime, variable(runtime))
    record = view.definedness
    assert record.exactness is DefinednessExactness.TOTAL
    assert record.domain is None
    assert record.valid_on is None
    assert record.certificate is None


def test_a_rational_view_definedness_is_exact(runtime):
    found = runtime.store.checkers.get("calculus.hermite")
    assert isinstance(found, HermiteChecker)
    term = _power(runtime, variable(runtime), -1)
    view = view_of(
        runtime,
        term,
        bridge=found.bridge,
        request=found.request,
    )
    record = view.definedness
    assert record.exactness is DefinednessExactness.EXACT
    assert record.domain is not None
    assert record.valid_on is not None
    assert record.certificate is None
    assert record.domain.condition == view.source_domain
    assert record.valid_on.condition == view.valid_on
    assert record.domain.coordinates == (runtime.variable,)
    assert record.valid_on.coordinates == (runtime.variable,)


def test_a_synthetic_view_definedness_is_sufficient_with_certificate(runtime):
    source = _typed(runtime)
    domain = runtime_proposition(runtime, T.TRUE)
    valid_on = runtime_proposition(runtime, _ne(runtime))
    view = _issue_view(
        source,
        runtime.parent,
        runtime.ring.generator(0),
        (SymbolBinding(runtime.variable, Role.TARGET, 0),),
        Interpretation.FORMAL,
        ConversionWitness.representation_isomorphism(),
        domain,
        valid_on,
        signature=runtime.signature,
    )
    assert isinstance(view, AlgebraView)
    record = view.definedness
    assert record.exactness is DefinednessExactness.SUFFICIENT
    assert isinstance(record.certificate, SubregionCertificate)
    assert verify_region_certificate(
        record.certificate, runtime.signature
    )
    sorts = ((runtime.variable, S.REAL),)
    assert record.domain == RegionSpec(
        (runtime.variable,), domain, sorts
    )
    assert record.valid_on == RegionSpec(
        (runtime.variable,), valid_on, sorts
    )


def test_a_total_source_with_a_partial_representation_is_sufficient(runtime):
    source = _typed(runtime)
    valid_on = runtime_proposition(runtime, _ne(runtime))
    view = _issue_view(
        source,
        runtime.parent,
        runtime.ring.generator(0),
        (SymbolBinding(runtime.variable, Role.TARGET, 0),),
        Interpretation.FORMAL,
        ConversionWitness.representation_isomorphism(),
        None,
        valid_on,
        signature=runtime.signature,
    )
    assert isinstance(view, AlgebraView)
    assert view.source_domain is None
    assert view.valid_on == valid_on
    record = view.definedness
    assert record.exactness is DefinednessExactness.SUFFICIENT
    assert record.domain is None
    assert record.valid_on == RegionSpec(
        (runtime.variable,),
        valid_on,
        ((runtime.variable, S.REAL),),
    )
    assert record.certificate is None


def test_definedness_is_sealed_against_direct_construction_and_replace(runtime):
    source = _typed(runtime)
    with pytest.raises(ValueError, match="issued only"):
        Definedness(
            source, None, None, DefinednessExactness.TOTAL
        )
    record = _issue_definedness(
        source, None, None, DefinednessExactness.TOTAL
    )
    with pytest.raises(ValueError, match="issued only"):
        replace(record, exactness=DefinednessExactness.EXACT)
