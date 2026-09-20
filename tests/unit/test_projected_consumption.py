# -*- coding: utf-8 -*-
"""Projected-element consumption: the domain consumes its own element.

The projection ladder is open on the producer side (a domain registers a stage);
these nails pin the consumer side open as well: `is_zero` / `normalize` hand a
projected element back to the producing domain through `element_is_zero` /
`element_to_term`, so a brand-new representation is consumable without the
projection layer knowing it. The known cells (constant, polynomial,
rational-function) are pinned to the same answers as before, and a domain that
produces an element without implementing the two methods must refuse loudly and
name itself instead of failing with an anonymous error.

The polynomial views the consumers use are capability queries as well: the
classifier consumes `element_poly` (a polynomial sharing the element's
vanishing), while integration and the differentiation cross-check consume
`element_as_poly` (the element itself as a polynomial), so a domain either
answers a query or the consumer refuses honestly, never recognizing a
representation by Python type.

Terms are built with the syntax constructors (not the parser) so the test pins
the projection channel and not the surface grammar; the Q(i) generator is taken
from the assembled runtime.
"""

import pathlib
import re
from fractions import Fraction as Fr

import pytest

from cas.syntax import term as T
from cas.syntax.term import S
from cas.runtime import get_runtime
from cas.errors import IntegrateError
from cas.kernel.commit import StepProposal
from cas.kernel.evidence import Evidence
from cas.math import project as projection
from cas.math.calculus.differentiation.checkers import DiffChecker, _cross_diff
from cas.math.domains.base import Domain, domain_scope
from cas.math.domains.poly import Poly, poly_domain
from cas.math.domains.poly import from_term as poly_from_term
from cas.math.domains.ratfunc import ratfunc_domain, rf_from_term
from cas.math.domains.qarith import fold
from cas.math.tactics import _lin_core, solve_linear, TacticsError
from cas.math.integrate import integrate_term
from cas.workflow.command import Diff


X = S("x")
Y = S("y")


@pytest.fixture
def ladder():
    """A clean projection ladder, rebuilt through the public assembly API:
    `clear_stages` and `bind_domains` are module-level entry points, so the test
    needs no private state and the session ladder is restored afterwards."""
    projection.clear_stages()
    try:
        yield projection
    finally:
        projection.bind_domains(get_runtime().domains)


# ---------------------------------------------------------------------------
# The known cells keep their answers, and the normal form is the domain's own
# ---------------------------------------------------------------------------

def test_constant_cells_keep_their_answers():
    i = get_runtime().const_by_name("i").atom
    cases = (
        (T.N(0), True),
        (T.N(3), False),
        (T.N(Fr(1, 2)), False),
        (i, False),
        (T.plus(T.N(2), T.times(T.N(3), i)), False),
    )
    for term, zero in cases:
        hit = projection.project(term)
        assert hit is not None, term
        assert hit.element is None, "a constant cell carries no element"
        assert projection.is_zero(hit) is zero, term
        # the normal form is exactly what the domain path itself returns
        assert projection.normalize(hit) is hit.domain.normalize(term), term


def test_polynomial_cell_keeps_its_answers():
    zero_term = T.plus(X, T.neg(X))
    hit = projection.project(zero_term)
    assert hit is not None and hit.element is not None
    assert projection.is_zero(hit) is True
    assert projection.normalize(hit) is hit.domain.normalize(zero_term)

    nonzero_term = T.plus(T.pw(X, T.N(2)), T.neg(T.N(3)))       # x^2 - 3
    hit = projection.project(nonzero_term)
    assert hit is not None and hit.element is not None
    assert projection.is_zero(hit) is False
    assert projection.normalize(hit) is hit.domain.normalize(nonzero_term)


def test_ratfunc_cell_keeps_its_answers():
    x_minus_one = T.plus(X, T.neg(T.ONE))
    zero_term = T.times(T.N(0), T.pw(x_minus_one, T.N(-1)))     # 0/(x-1)
    hit = projection.project(zero_term)
    assert hit is not None and hit.element is not None
    assert projection.is_zero(hit) is True
    assert projection.normalize(hit) is hit.domain.normalize(zero_term)

    nonzero_term = T.div(T.ONE, x_minus_one)                    # 1/(x-1)
    hit = projection.project(nonzero_term)
    assert hit is not None and hit.element is not None
    assert projection.is_zero(hit) is False
    assert projection.normalize(hit) is hit.domain.normalize(nonzero_term)


# ---------------------------------------------------------------------------
# The consumer channel is genuinely open: a new representation is consumed
# ---------------------------------------------------------------------------

class _DualElement:
    """A representation the projection layer has never seen."""

    def __init__(self, value):
        self.value = value


class _DualDomain(Domain):
    """A domain with its own element type: vanishing and normal form defined by
    the domain, never by the projection layer."""

    name = "c5-dual"

    def normalize(self, t):
        return t

    def equal(self, a, b):
        return a is b

    def element_is_zero(self, element) -> bool:
        return element.value == 0

    def element_to_term(self, element):
        return T.N(element.value)


def _marker(head_name, value):
    return T.mk(T.S(head_name), (T.N(value),))


def test_new_representation_is_consumed_through_public_registration(ladder):
    """The property this change exists for: a domain registers a projection
    stage through the public API and hands over its own element type, and the
    consumer channel works without any representation knowledge."""
    dual = _DualDomain()

    def try_fn(t, vs):
        if isinstance(t, T.Expr) and t.head is T.S("C5DualMarker"):
            return projection.Projected(dual, _DualElement(t.args[0].v), t,
                                        dual.name)
        return None

    with domain_scope(dual):
        ladder.register_stage(projection.ProjectionStage("c5-dual", try_fn))
        hit_zero = ladder.project(_marker("C5DualMarker", 0))
        hit_two = ladder.project(_marker("C5DualMarker", 2))

        assert hit_zero is not None and hit_zero.domain is dual
        assert hit_two is not None and hit_two.domain is dual
        assert type(hit_two.element) is _DualElement

        assert ladder.is_zero(hit_zero) is True
        assert ladder.is_zero(hit_two) is False
        assert ladder.normalize(hit_zero) is T.N(0)
        assert ladder.normalize(hit_two) is T.N(2)


# ---------------------------------------------------------------------------
# A producing domain without the two methods refuses loudly and names itself
# ---------------------------------------------------------------------------

def test_producing_domain_without_consumption_refuses_and_names_itself(ladder):
    class OpaqueDomain(Domain):
        name = "c5-opaque"

        def normalize(self, t):
            return t

        def equal(self, a, b):
            return a is b

    opaque = OpaqueDomain()

    def try_fn(t, vs):
        if isinstance(t, T.Expr) and t.head is T.S("C5OpaqueMarker"):
            return projection.Projected(opaque, object(), t, opaque.name)
        return None

    with domain_scope(opaque):
        ladder.register_stage(projection.ProjectionStage("c5-opaque", try_fn))
        hit = ladder.project(_marker("C5OpaqueMarker", 1))
        assert hit is not None and hit.domain is opaque

        with pytest.raises(NotImplementedError, match="c5-opaque") as zero_err:
            ladder.is_zero(hit)
        assert "element_is_zero" in str(zero_err.value)

        with pytest.raises(NotImplementedError, match="c5-opaque") as nf_err:
            ladder.normalize(hit)
        assert "element_to_term" in str(nf_err.value)


# ---------------------------------------------------------------------------
# A protocol-only domain reaches the honest refusal, not an AttributeError
# ---------------------------------------------------------------------------

def test_protocol_only_domain_reaches_the_honest_refusal(ladder):
    """The integration and differentiation consumers used to read
    `hit.domain.vars` before checking the representation. A domain that
    implements only the documented protocol (`normalize` / `equal` /
    `element_is_zero` / `element_to_term`) owns no `vars` / `ring`, so the read
    raised AttributeError instead of reaching the honest refusal / undecided
    result; the representation-dependent reads now happen only on the branches
    that know the representation."""
    protocol = _DualDomain()

    def try_fn(t, vs):
        if isinstance(t, T.Expr) and t.head is T.S("C6ProtocolMarker"):
            return projection.Projected(protocol, _DualElement(t.args[0].v), t,
                                        protocol.name)
        return None

    with domain_scope(protocol):
        ladder.register_stage(projection.ProjectionStage("c6-protocol", try_fn))
        marker = _marker("C6ProtocolMarker", 7)
        with pytest.raises(IntegrateError, match="element representation"):
            integrate_term(marker, X)
        assert _cross_diff(marker, marker, X) is None
        proposal = StepProposal(
            scope=None, premises=(), conclusions=(marker,),
            evidence=Evidence("calculus.derivative", Diff(pred=None, var=X)),
            premise_propositions=(marker,))
        assert DiffChecker().check(proposal, None, None).is_unknown()


def test_element_variable_view_keeps_the_independent_integrand():
    """The `vars` capability is declared on the domain, so an integrand that does
    not involve the variable of integration is still integrated for every
    representation that exposes a variable view (a rational function here): the
    integral of `1/y` over `x` is `x * 1/y`.

    A domain that declares no variable view is refused by name; that refusal is
    pinned by the protocol-only test above, which no longer reads a field the
    domain may not have.
    """
    from cas.math.integrate import integrate_term
    from cas.syntax.term import S
    integrand = T.mk(S("Power"), (S("y"), T.N(-1)))
    assert integrate_term(integrand, X) == T.times(integrand, X)


# ---------------------------------------------------------------------------
# The projection layer itself carries no representation knowledge
# ---------------------------------------------------------------------------

def test_projection_layer_knows_no_representation():
    """Pin the removed defect statically: the projection layer may not mention a
    concrete element representation or dispatch on one."""
    root = next(p for p in pathlib.Path(__file__).resolve().parents
                if (p / "cas").is_dir())
    src = (root / "cas" / "math" / "project.py").read_text(encoding="utf-8")
    for forbidden in ("Poly", "RatFunc", "isinstance(hit.element"):
        assert forbidden not in src, forbidden


# ---------------------------------------------------------------------------
# C8: the polynomial view is a domain capability, not a Python type
# ---------------------------------------------------------------------------

def test_polynomial_and_ratfunc_domains_answer_the_polynomial_view_query():
    """Both built-in domains answer the same capability query: the polynomial
    domain with its element, the rational-function domain with the numerator of
    the reduced fraction (the denominator is nonzero by construction, so the
    view vanishes exactly where the fraction does)."""
    ring = poly_domain(X).ring
    p = poly_from_term(ring, T.plus(X, T.neg(T.TWO)), (X,))          # x - 2
    assert poly_domain(X).element_poly(p) is p

    x_sq_minus_one = T.plus(T.pw(X, T.TWO), T.neg(T.ONE))            # x^2 - 1
    rf = rf_from_term(ring, T.div(x_sq_minus_one, T.plus(X, T.neg(T.ONE))),
                      (X,))
    view = ratfunc_domain(X).element_poly(rf)
    assert isinstance(view, Poly)
    assert view.monos == poly_from_term(ring, T.plus(X, T.ONE), (X,)).monos


def test_linear_solve_consumes_a_rational_function_through_the_view():
    """The end-to-end consumer path: 1/(x-2) = 1 is solved on the polynomial view
    of the rational function, with no isinstance dispatch in the tactic."""
    x_minus_two = T.plus(X, T.neg(T.TWO))
    solved = solve_linear(T.eq(T.div(T.ONE, x_minus_two), T.ONE), X)
    assert solved is T.N(3)
    # a zero fraction is an identity through the same view
    zero_fraction = T.times(T.N(0), T.pw(x_minus_two, T.N(-1)))
    with pytest.raises(TacticsError, match="identity"):
        solve_linear(T.eq(zero_fraction, T.N(0)), X)


class _OpaqueViewElement:
    """A representation the tactics layer has never seen."""

    def __init__(self, poly):
        self.poly = poly


class _ViewDomain(Domain):
    """A domain exposing the polynomial view only through the capability query:
    its element type stays private to the domain."""

    name = "c8-view"

    def __init__(self, ring):
        self.ring = ring

    def normalize(self, t):
        return t

    def equal(self, a, b):
        return a is b

    def element_poly(self, element):
        return element.poly


def test_new_representation_is_consumed_through_the_polynomial_view(ladder):
    """A domain that answers the query is consumable even though its element type
    is unknown to the tactics layer."""
    view = _ViewDomain(poly_domain(X).ring)
    p = poly_from_term(view.ring, T.plus(X, T.neg(T.TWO)), (X,))     # x - 2

    def try_fn(t, vs):
        if isinstance(t, T.Expr) and t.head is T.S("C8ViewMarker"):
            return projection.Projected(view, _OpaqueViewElement(p), t, view.name)
        return None

    with domain_scope(view):
        ladder.register_stage(projection.ProjectionStage("c8-view", try_fn))
        kind, payload = _lin_core(_marker("C8ViewMarker", 0), X)

    assert kind == "linear"
    assert payload is T.N(2)                 # x - 2 = 0 -> x = 2


class _NoViewDomain(Domain):
    """A domain with no polynomial view: the capability query's base answer is
    None and the consumer refuses honestly."""

    name = "c8-no-view"

    def normalize(self, t):
        return t

    def equal(self, a, b):
        return a is b


def test_domain_without_the_polynomial_view_refuses_honestly(ladder):
    no_view = _NoViewDomain()

    def try_fn(t, vs):
        if isinstance(t, T.Expr) and t.head is T.S("C8NoViewMarker"):
            return projection.Projected(no_view, object(), t, no_view.name)
        return None

    with domain_scope(no_view):
        ladder.register_stage(projection.ProjectionStage("c8-no-view", try_fn))
        kind, reason = _lin_core(_marker("C8NoViewMarker", 1), X)

    assert no_view.element_poly(object()) is None    # the protocol default: no view
    assert kind == "refuse"
    assert "polynomial view" in reason


def test_tactics_layer_dispatches_by_capability_not_representation():
    """Pin the removed defect statically: the linear core names no concrete
    element representation and dispatches on none."""
    root = next(p for p in pathlib.Path(__file__).resolve().parents
                if (p / "cas").is_dir())
    src = (root / "cas" / "math" / "tactics.py").read_text(encoding="utf-8")
    for forbidden in ("Poly", "RatFunc", "rf_reduce", "isinstance(el"):
        assert forbidden not in src, forbidden


# ---------------------------------------------------------------------------
# C8 (continued): the element-as-polynomial view is a second, distinct query
# ---------------------------------------------------------------------------

def test_builtin_domains_answer_the_element_as_polynomial_query():
    """`element_as_poly` answers "the element IS this polynomial", a different
    question from `element_poly`'s "it shares this polynomial's vanishing": the
    rational-function domain returns the value (the numerator scaled by a
    constant denominator) for a fraction that is a polynomial, and None for a
    genuine fraction whose `element_poly` view is the denominator-cleared
    numerator."""
    ring = poly_domain(X).ring
    p = poly_from_term(ring, T.plus(X, T.neg(T.TWO)), (X,))          # x - 2
    assert poly_domain(X).element_as_poly(p) is p
    assert poly_domain(X).element_poly(p) is p                       # the same here

    x_sq_minus_one = T.plus(T.pw(X, T.TWO), T.neg(T.ONE))            # x^2 - 1
    x_minus_one = T.plus(X, T.neg(T.ONE))                            # x - 1
    rfd = ratfunc_domain(X)
    as_poly = rfd.element_as_poly(rf_from_term(
        ring, T.div(x_sq_minus_one, x_minus_one), (X,)))
    assert as_poly is not None
    assert as_poly.monos == poly_from_term(ring, T.plus(X, T.ONE), (X,)).monos

    fraction = rf_from_term(ring, T.div(T.ONE, x_minus_one), (X,))
    assert rfd.element_as_poly(fraction) is None
    # the vanishing view still answers for the same genuine fraction: the two
    # queries are distinct, and the cleared numerator is not the value
    assert rfd.element_poly(fraction).monos == \
        poly_from_term(ring, T.ONE, (X,)).monos


def test_constant_denominator_fraction_keeps_the_scaled_value():
    """A reduced fraction is a polynomial exactly when its denominator has no
    variable part, and its value is then the numerator scaled by the inverse of
    the constant. The multivariate domain is where reduction leaves a non-unit
    constant denominator in place, so the scaling is what makes the answer the
    value rather than just the vanishing."""
    ring = poly_domain(X, Y).ring
    rfd = ratfunc_domain(X, Y)
    fraction = rf_from_term(ring, T.div(T.times(T.N(2), X, Y), T.N(2)), (X, Y))
    as_poly = rfd.element_as_poly(fraction)
    assert as_poly is not None
    assert as_poly.monos == poly_from_term(ring, T.times(X, Y), (X, Y)).monos
    # the denominator-cleared vanishing view keeps the constant factor
    assert rfd.element_poly(fraction).monos == \
        poly_from_term(ring, T.times(T.N(2), X, Y), (X, Y)).monos

    genuine = rf_from_term(ring, T.div(T.times(T.N(2), X, Y),
                                       T.plus(X, Y)), (X, Y))
    assert rfd.element_as_poly(genuine) is None


def test_absent_element_views_answer_none():
    """Both optional element views default to an honest absence rather than a
    loud failure: a domain that declares neither is a legitimate domain."""
    no_view = _NoViewDomain()
    assert no_view.element_poly(object()) is None
    assert no_view.element_as_poly(object()) is None


def test_integrate_term_consumes_a_polynomial_valued_fraction():
    """The integrand is taken through the element-as-polynomial capability: a
    rational function whose value is a polynomial is integrated (it used to be
    refused as a proper fraction), while a genuine fraction still refuses
    honestly, naming the missing fragment."""
    x_minus_one = T.plus(X, T.neg(T.ONE))
    integrand = T.div(T.plus(T.pw(X, T.TWO), T.neg(T.ONE)), x_minus_one)
    got = integrate_term(integrand, X)                       # x^2/2 + x
    want = fold(T.plus(T.times(T.N(Fr(1, 2)), T.pw(X, T.TWO)), X))
    assert fold(got) == want

    with pytest.raises(IntegrateError, match="Hermite"):
        integrate_term(T.div(T.ONE, x_minus_one), X)


class _AsPolyElement:
    """A representation the projection consumers have never seen."""

    def __init__(self, poly):
        self.poly = poly


class _AsPolyDomain(Domain):
    """A domain whose element type stays private and whose polynomial denotation
    is available only through the element-as-polynomial capability query."""

    name = "c8-as-poly"

    def __init__(self, vars_, ring):
        self.vars = tuple(vars_)
        self.ring = ring

    def normalize(self, t):
        return t

    def equal(self, a, b):
        return a is b

    def element_as_poly(self, element):
        return element.poly


def test_new_representation_is_consumed_through_the_element_as_polynomial_query(ladder):
    """Both capability consumers take the polynomial denotation without ever
    naming the element type: integration builds the antiderivative of a private
    representation, and the differentiation cross-check rebuilds the derivative
    through the same query."""
    ring = poly_domain(X).ring
    domain = _AsPolyDomain((X,), ring)
    p = poly_from_term(ring, T.plus(T.pw(X, T.TWO), T.neg(T.N(3))), (X,))   # x^2 - 3

    def try_fn(t, vs):
        if isinstance(t, T.Expr) and t.head is T.S("C8AsPolyMarker"):
            return projection.Projected(domain, _AsPolyElement(p), t, domain.name)
        return None

    with domain_scope(domain):
        ladder.register_stage(projection.ProjectionStage("c8-as-poly", try_fn))
        marker = _marker("C8AsPolyMarker", 1)
        got = integrate_term(marker, X)                              # x^3/3 - 3x
        want = fold(T.plus(T.times(T.N(Fr(1, 3)), T.pw(X, T.N(3))),
                          T.neg(T.times(T.N(3), X))))
        assert fold(got) == want
        assert _cross_diff(marker, T.times(T.N(2), X), X) is True
        assert _cross_diff(marker, T.N(1), X) is False


def test_capability_consumers_name_no_concrete_element_representation():
    """Pin the removed defect statically: neither the integration solver nor the
    differentiation cross-check may recognize the polynomial / rational-function
    representation by Python type."""
    root = next(p for p in pathlib.Path(__file__).resolve().parents
                if (p / "cas").is_dir())
    pattern = re.compile(r"isinstance\([^)]*\b(Poly|RatFunc)\b")
    for rel in ("cas/math/integrate.py",
                "cas/math/calculus/differentiation/checkers.py"):
        src = (root / rel).read_text(encoding="utf-8")
        hit = pattern.search(src)
        assert hit is None, (rel, hit.group(0))
