"""Parameterized assembly accepts an explicit base field, not a hardcoded Q."""

from fractions import Fraction

from support import head_app, variable

from cas.algebra.parents import ParentSpec
from cas.algebra.protocols import Field
from cas.language.signatures import StructuralHead
from cas.math.calculus.differentiation.specification import parse_has_derivative
from cas.runtime.bootstrap import bootstrap_parameterized_over, new_workspace
from cas.syntax import term as T
from cas.workflow.records import OperationStatus

Representation = tuple[Fraction, str]


class TaggedRationalField(Field[Representation]):
    """A field isomorphic to Q with a distinct representation and parent kind."""

    def zero(self) -> Representation:
        return (Fraction(0), "tagged")

    def one(self) -> Representation:
        return (Fraction(1), "tagged")

    def add(
        self, left: Representation, right: Representation
    ) -> Representation:
        return (left[0] + right[0], "tagged")

    def neg(self, value: Representation) -> Representation:
        return (-value[0], "tagged")

    def mul(
        self, left: Representation, right: Representation
    ) -> Representation:
        return (left[0] * right[0], "tagged")

    def contains(self, value: object) -> bool:
        return (
            isinstance(value, tuple)
            and len(value) == 2
            and isinstance(value[0], Fraction)
            and value[1] == "tagged"
        )

    def equal(
        self, left: Representation, right: Representation
    ) -> bool:
        return left[0] == right[0]

    def inv(self, value: Representation) -> Representation:
        if value[0] == 0:
            raise ZeroDivisionError("zero has no inverse")
        return (Fraction(1) / value[0], "tagged")

    def div_exact(
        self, left: Representation, right: Representation
    ) -> Representation:
        return self.div(left, right)

    def div_int(
        self, value: Representation, factor: int
    ) -> Representation:
        if factor == 0:
            raise ZeroDivisionError("division by zero")
        return (value[0] / factor, "tagged")

    @property
    def characteristic(self) -> int:
        return 0

    @property
    def parent_kind(self) -> str:
        return "tagged_Q"

    @property
    def parent_requires_base(self) -> bool:
        return False

    @property
    def parent_options(self) -> tuple[tuple[str, str], ...]:
        return ()


def embed(value: Fraction) -> Representation:
    return (value, "tagged")


def render(value: Representation) -> T.Term:
    return T.number(value[0])


def test_a_parameterized_runtime_can_be_built_over_a_custom_field():
    field = TaggedRationalField()
    runtime = bootstrap_parameterized_over(
        field,
        ParentSpec("tagged_Q"),
        ("a",),
        embed_rational=embed,
        render_base=render,
    )
    assert runtime.request.coefficient.ring is field
    assert runtime.ring.coefficients.generators == runtime.request.parameters
    workspace = new_workspace(runtime)
    a, x = runtime.request.parameters[0], runtime.variable
    source_term = head_app(
        runtime.signature,
        StructuralHead.TIMES,
        T.symbol(a, "a"),
        head_app(runtime.signature, StructuralHead.POWER, variable(runtime), T.number(2)),
    )
    source = workspace.intake(source_term, "a*x^2")
    result = workspace.differentiate(source, x)
    assert result.status is OperationStatus.VERIFIED
    assert result.result is not None
    claim = parse_has_derivative(
        runtime.vocabulary, result.verifications[0].specification.term
    )
    assert claim is not None
    assert claim.variable.symbol_id == x
    assert claim.source == source.term
    assert claim.candidate == result.result.term


def test_integration_works_over_the_custom_field():
    field = TaggedRationalField()
    runtime = bootstrap_parameterized_over(
        field,
        ParentSpec("tagged_Q"),
        ("a",),
        embed_rational=embed,
        render_base=render,
    )
    workspace = new_workspace(runtime)
    a, x = runtime.request.parameters[0], runtime.variable
    source_term = head_app(
        runtime.signature,
        StructuralHead.TIMES,
        T.symbol(a, "a"),
        variable(runtime),
    )
    source = workspace.intake(source_term, "a*x")
    result = workspace.integrate(source, x)
    assert result.status is OperationStatus.VERIFIED
    assert result.result is not None
    claim = parse_has_derivative(
        runtime.vocabulary, result.verifications[0].specification.term
    )
    assert claim is not None
    assert claim.source == result.result.term
    assert claim.candidate == source.term
