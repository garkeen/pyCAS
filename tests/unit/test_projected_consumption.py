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

Terms are built with the syntax constructors (not the parser) so the test pins
the projection channel and not the surface grammar; the Q(i) generator is taken
from the assembled runtime.
"""

import pathlib
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
from cas.math.integrate import integrate_term
from cas.workflow.command import Diff


X = S("x")


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
