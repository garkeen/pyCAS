"""Type inference: sorts, structural rules and declared operators."""

from fractions import Fraction

from support import MapEnvironment, head_app

from cas.language import sorts as S
from cas.language import typing as Ty
from cas.language.signatures import OperatorSignature, StructuralHead
from cas.semantics.symbols import SymbolTable, standard_language
from cas.syntax import term as T


class World:
    def __init__(self, operators=None):
        self.table = SymbolTable()
        self.signature = standard_language(self.table, operators=operators)
        self.environment = MapEnvironment()
        self.x = self.environment.declare(self.table.intern("x"), S.REAL)
        self.n = self.environment.declare(self.table.intern("n"), S.INTEGER)
        self.z = self.environment.declare(self.table.intern("z"), S.COMPLEX)
        self.u = self.table.intern("u")

    def infer(self, term: T.Term) -> Ty.Typing:
        return Ty.infer(term, self.signature, self.environment)

    def app(self, head: StructuralHead, *arguments: T.Term) -> T.Apply:
        return head_app(self.signature, head, *arguments)

    def symbol(self, identifier) -> T.SymbolRef:
        return T.symbol(identifier, self.table.name_of(identifier))


def test_literals_have_their_exact_sorts():
    world = World()
    assert world.infer(T.number(2)) == Ty.Typed(S.INTEGER)
    assert world.infer(T.number(Fraction(1, 2))) == Ty.Typed(S.RATIONAL)
    assert world.infer(T.TRUE) == Ty.Typed(S.PROPOSITION)
    assert world.infer(T.quote(T.BoundVar(0))) == Ty.Typed(S.SYNTAX)


def test_declared_and_undeclared_symbols():
    world = World()
    assert world.infer(world.symbol(world.x)) == Ty.Typed(S.REAL)
    outcome = world.infer(world.symbol(world.u))
    assert isinstance(outcome, Ty.NeedsDeclaration)
    assert outcome.symbol_id == world.u


def test_a_bound_variable_has_no_sort_outside_its_binder():
    assert isinstance(World().infer(T.BoundVar(0)), Ty.IllTyped)


def test_a_binder_needs_elaboration_to_type_its_variables():
    binder = T.binder("Lam", 1, T.BoundVar(0))
    outcome = World().infer(binder)
    assert isinstance(outcome, Ty.Unsupported)


def test_arithmetic_joins_scalar_sorts():
    world = World()
    x, n = world.symbol(world.x), world.symbol(world.n)
    assert world.infer(world.app(StructuralHead.PLUS, n, T.number(2))) == Ty.Typed(
        S.INTEGER
    )
    assert world.infer(
        world.app(StructuralHead.PLUS, n, T.number(Fraction(1, 2)))
    ) == Ty.Typed(S.RATIONAL)
    assert world.infer(world.app(StructuralHead.PLUS, x, n)) == Ty.Typed(S.REAL)
    assert world.infer(world.app(StructuralHead.TIMES, n, x)) == Ty.Typed(S.REAL)


def test_arithmetic_rejects_non_scalars_and_bad_arity():
    world = World()
    x = world.symbol(world.x)
    assert isinstance(
        world.infer(world.app(StructuralHead.PLUS, x, T.TRUE)), Ty.IllTyped
    )
    assert isinstance(
        world.infer(world.app(StructuralHead.PLUS, x)), Ty.IllTyped
    )


def test_power_with_a_nonnegative_integer_exponent_keeps_the_base_sort():
    world = World()
    x, n = world.symbol(world.x), world.symbol(world.n)
    assert world.infer(
        world.app(StructuralHead.POWER, x, T.number(2))
    ) == Ty.Typed(S.REAL)
    assert world.infer(
        world.app(StructuralHead.POWER, n, T.number(0))
    ) == Ty.Typed(S.INTEGER)


def test_power_rejects_a_non_exact_exponent_and_a_non_scalar_base():
    world = World()
    x = world.symbol(world.x)
    assert isinstance(
        world.infer(world.app(StructuralHead.POWER, x, x)), Ty.IllTyped
    )
    assert isinstance(
        world.infer(world.app(StructuralHead.POWER, T.TRUE, T.number(2))),
        Ty.IllTyped,
    )


def test_a_negative_or_symbolic_exponent_may_need_an_inverse():
    world = World()
    x, n = world.symbol(world.x), world.symbol(world.n)
    assert world.infer(
        world.app(StructuralHead.POWER, n, T.number(-1))
    ) == Ty.Typed(S.RATIONAL)
    assert world.infer(
        world.app(StructuralHead.POWER, x, T.number(-1))
    ) == Ty.Typed(S.REAL)
    assert world.infer(world.app(StructuralHead.POWER, n, n)) == Ty.Typed(
        S.RATIONAL
    )
    assert world.infer(world.app(StructuralHead.POWER, x, n)) == Ty.Typed(
        S.REAL
    )


def test_a_rational_exponent_can_leave_the_real_line():
    world = World()
    x, n = world.symbol(world.x), world.symbol(world.n)
    half = T.number(Fraction(1, 2))
    assert world.infer(
        world.app(StructuralHead.POWER, n, half)
    ) == Ty.Typed(S.COMPLEX)
    assert world.infer(
        world.app(StructuralHead.POWER, x, half)
    ) == Ty.Typed(S.COMPLEX)


def test_quoted_syntax_does_not_require_its_content_to_be_typed():
    world = World()
    undeclared = world.symbol(world.u)
    application = world.app(StructuralHead.QUOTE, undeclared)
    assert world.infer(application) == Ty.Typed(S.SYNTAX)
    assert world.infer(T.quote(undeclared)) == Ty.Typed(S.SYNTAX)


def test_comparisons_need_a_common_sort_and_order_needs_an_ordered_one():
    world = World()
    x, n, z = world.symbol(world.x), world.symbol(world.n), world.symbol(world.z)
    assert world.infer(world.app(StructuralHead.EQ, x, T.number(1))) == Ty.Typed(
        S.PROPOSITION
    )
    assert world.infer(world.app(StructuralHead.EQ, x, z)) == Ty.Typed(
        S.PROPOSITION
    )
    assert world.infer(world.app(StructuralHead.LT, x, n)) == Ty.Typed(
        S.PROPOSITION
    )
    assert isinstance(
        world.infer(world.app(StructuralHead.LT, z, n)), Ty.IllTyped
    )
    assert isinstance(
        world.infer(world.app(StructuralHead.EQ, x, T.TRUE)), Ty.IllTyped
    )


def test_logic_accepts_only_propositions():
    world = World()
    x = world.symbol(world.x)
    condition = world.app(StructuralHead.EQ, x, T.number(1))
    assert world.infer(world.app(StructuralHead.AND, condition, condition)) == (
        Ty.Typed(S.PROPOSITION)
    )
    assert world.infer(world.app(StructuralHead.OR, condition, condition)) == (
        Ty.Typed(S.PROPOSITION)
    )
    assert world.infer(world.app(StructuralHead.NOT, condition)) == Ty.Typed(
        S.PROPOSITION
    )
    assert world.infer(world.app(StructuralHead.IMPLIES, condition, condition)) == (
        Ty.Typed(S.PROPOSITION)
    )
    assert isinstance(
        world.infer(world.app(StructuralHead.AND, condition, x)), Ty.IllTyped
    )
    assert isinstance(world.infer(world.app(StructuralHead.NOT, x)), Ty.IllTyped)
    assert isinstance(
        world.infer(world.app(StructuralHead.NOT, condition, condition)),
        Ty.IllTyped,
    )


def test_guarded_takes_a_condition_and_returns_the_body_sort():
    world = World()
    x = world.symbol(world.x)
    condition = world.app(StructuralHead.EQ, x, T.number(1))
    assert world.infer(world.app(StructuralHead.GUARDED, condition, x)) == Ty.Typed(
        S.REAL
    )
    assert isinstance(
        world.infer(world.app(StructuralHead.GUARDED, x, condition)), Ty.IllTyped
    )


def test_piecewise_joins_branch_values_and_requires_conditions():
    world = World()
    x, n = world.symbol(world.x), world.symbol(world.n)
    condition = world.app(StructuralHead.EQ, x, T.number(1))
    assert world.infer(
        world.app(StructuralHead.PIECEWISE, x, condition, n, condition)
    ) == Ty.Typed(S.REAL)
    assert isinstance(
        world.infer(world.app(StructuralHead.PIECEWISE, x, condition, n)),
        Ty.IllTyped,
    )
    assert isinstance(
        world.infer(world.app(StructuralHead.PIECEWISE, x, x, n, condition)),
        Ty.IllTyped,
    )


def test_quoted_syntax_has_syntax_sort():
    world = World()
    assert world.infer(T.quote(world.symbol(world.x))) == Ty.Typed(S.SYNTAX)


def test_an_applied_expression_needs_a_symbol_operator():
    world = World()
    applied = T.app(world.app(StructuralHead.PLUS, T.number(1), T.number(2)), T.number(3))
    assert isinstance(world.infer(applied), Ty.Unsupported)


def test_an_unregistered_operator_needs_a_declaration():
    world = World()
    applied = T.app(world.symbol(world.u), T.number(1))
    outcome = world.infer(applied)
    assert isinstance(outcome, Ty.NeedsDeclaration)
    assert outcome.symbol_id == world.u


def test_a_declared_operator_checks_arity_and_argument_sorts():
    table = SymbolTable()
    predicate = table.intern("P")
    signature = standard_language(
        table, operators={predicate: OperatorSignature((S.REAL,), S.PROPOSITION)}
    )
    environment = MapEnvironment()
    x = environment.declare(table.intern("x"), S.REAL)
    n = environment.declare(table.intern("n"), S.INTEGER)
    z = environment.declare(table.intern("z"), S.COMPLEX)
    u = table.intern("u")
    symbol = T.symbol(predicate, "P")

    def infer(term: T.Term) -> Ty.Typing:
        return Ty.infer(term, signature, environment)

    assert infer(T.app(symbol, T.symbol(x, "x"))) == Ty.Typed(S.PROPOSITION)
    # integers embed into the expected real argument
    assert infer(T.app(symbol, T.symbol(n, "n"))) == Ty.Typed(S.PROPOSITION)
    assert isinstance(infer(T.app(symbol, T.symbol(z, "z"))), Ty.IllTyped)
    assert isinstance(
        infer(T.app(symbol, T.symbol(x, "x"), T.symbol(x, "x"))), Ty.IllTyped
    )
    outcome = infer(T.app(symbol, T.symbol(u, "u")))
    assert isinstance(outcome, Ty.NeedsDeclaration)
    assert outcome.symbol_id == u


def test_typing_exposes_a_single_typed_predicate():
    assert Ty.Typed(S.REAL).is_typed()
    assert not Ty.IllTyped("no").is_typed()
