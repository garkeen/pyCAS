"""Problem specifications: fixed requests, no hidden completeness."""

import dataclasses

import pytest
from support import (
    MapEnvironment,
    head_app,
    multivariate_setup,
    proposition_in,
    runtime_proposition,
    typed_in,
)

from cas.foundation.ids import FrameId, SymbolId, WorldId
from cas.language import sorts as S
from cas.language import typing as Ty
from cas.language.functions import (
    FunctionParameter,
    FunctionRepresentation,
    FunctionValue,
)
from cas.language.meaning import MeaningKey
from cas.language.problems import (
    Coverage,
    DomainRequirement,
    Exactness,
    InterpretationRequirement,
    ParameterMode,
    ProblemSpec,
    ResultLanguage,
    ValueDomain,
    VariableRoles,
    shared_variable_sort,
    value_domain_of_sort,
)
from cas.language.signatures import StructuralHead
from cas.runtime.bootstrap import bootstrap
from cas.semantics.frames import Declaration
from cas.semantics.symbols import SymbolTable, standard_language
from cas.syntax import term as T

_SIGNATURE = standard_language(SymbolTable())
_MEANING = MeaningKey(WorldId(0), FrameId(0))
_MISSING = object()


def typed(term: T.Term) -> Ty.TypedExpr:
    outcome = Ty.typed(term, _SIGNATURE, MapEnvironment(), _MEANING)
    assert isinstance(outcome, Ty.TypedExpr), outcome
    return outcome


def specification(runtime=None, **overrides) -> ProblemSpec:
    target = overrides.pop("target", None)
    parameters = overrides.pop("parameters", ())
    parameter_mode = overrides.pop(
        "parameter_mode", ParameterMode.SPECIFIED_VALUES
    )
    world = overrides.pop("world", None)
    target_sort = overrides.pop("target_sort", None)
    parameter_sorts = overrides.pop("parameter_sorts", ())
    variables = overrides.pop("variables", ())
    variable_sorts = overrides.pop("variable_sorts", ())
    inputs = overrides.pop("inputs", None)
    function_inputs = overrides.pop("function_inputs", ())
    domain_requirement = overrides.pop("domain_requirement", _MISSING)
    if inputs is None:
        if runtime is None:
            inputs = (typed(T.number(1)),)
            if world is None:
                world = WorldId(0)
        else:
            inputs = (
                typed_in(
                    runtime.frames,
                    runtime.frame.id,
                    runtime.signature,
                    T.number(1),
                ),
            )
            if world is None:
                world = runtime.world.id
    elif world is None:
        first = inputs[0] if inputs else None
        world = (
            first.meaning.world
            if isinstance(first, Ty.TypedExpr)
            else WorldId(0)
        )
    if domain_requirement is _MISSING:
        if target is not None:
            assert target_sort is not None
            domain_requirement = DomainRequirement(
                ValueDomain.RATIONAL,
                value_domain_of_sort(target_sort),
            )
        elif function_inputs:
            domain_requirement = DomainRequirement(
                None, ValueDomain.REAL
            )
        elif variables:
            domain_requirement = DomainRequirement(
                ValueDomain.RATIONAL,
                value_domain_of_sort(variable_sorts[0]),
            )
        else:
            domain_requirement = None
    values = dict(
        operation="differentiate",
        inputs=inputs,
        roles=VariableRoles(
            target,
            parameters,
            parameter_mode,
            world,
            target_sort,
            parameter_sorts,
            variables,
            variable_sorts,
        ),
        region=None,
        result_language=ResultLanguage.EXPRESSION,
        coverage=Coverage.ONE_VERIFIED,
        function_inputs=function_inputs,
        domain_requirement=domain_requirement,
    )
    values.update(overrides)
    return ProblemSpec(**values)


def function_value(runtime, domain):
    return FunctionValue(
        (FunctionParameter(runtime.variable, S.REAL),),
        domain,
        S.REAL,
        (
            FunctionRepresentation(
                T.symbol(runtime.variable, "x"),
                domain,
            ),
        ),
    )


def test_a_problem_fixes_operation_inputs_and_coverage():
    problem = specification()
    assert problem.operation == "differentiate"
    assert tuple(item.term for item in problem.inputs) == (T.number(1),)
    assert problem.coverage is Coverage.ONE_VERIFIED
    assert problem.allows_unresolved() is False


def test_a_problem_needs_an_operation_and_an_input():
    with pytest.raises(ValueError):
        specification(operation="")
    with pytest.raises(ValueError):
        specification(inputs=())


def test_a_problem_validates_field_kinds():
    with pytest.raises(TypeError):
        specification(inputs=(1,))
    with pytest.raises(TypeError):
        specification(coverage="one_verified")
    with pytest.raises(TypeError):
        specification(result_language="expression")
    with pytest.raises(TypeError):
        specification(externalizable=(T.number(1),))


def test_a_problem_region_must_be_a_total_condition(runtime):
    x = T.symbol(runtime.variable, "x")
    partial = proposition_in(
        runtime.frames,
        runtime.frame.id,
        runtime.signature,
        head_app(
            runtime.signature,
            StructuralHead.EQ,
            head_app(
                runtime.signature,
                StructuralHead.POWER,
                x,
                T.number(-1),
            ),
            T.number(1),
        ),
    )
    assert partial.definedness
    with pytest.raises(ValueError, match="total condition"):
        specification(
            runtime,
            target=runtime.variable,
            target_sort=S.REAL,
            region=partial,
        )
    total = proposition_in(
        runtime.frames,
        runtime.frame.id,
        runtime.signature,
        head_app(
            runtime.signature, StructuralHead.GT, x, T.number(0)
        ),
    )
    problem = specification(
        runtime,
        target=runtime.variable,
        target_sort=S.REAL,
        region=total,
    )
    assert problem.region is total


def test_a_complete_set_request_cannot_externalize_premises(runtime):
    x = T.symbol(runtime.variable, "x")
    condition = proposition_in(
        runtime.frames,
        runtime.frame.id,
        runtime.signature,
        head_app(runtime.signature, StructuralHead.EQ, x, T.number(1)),
    )
    with pytest.raises(ValueError):
        specification(
            runtime,
            coverage=Coverage.COMPLETE_SET,
            externalizable=(condition,),
        )


def test_a_sound_set_may_carry_externalized_premises(runtime):
    x = T.symbol(runtime.variable, "x")
    condition = proposition_in(
        runtime.frames,
        runtime.frame.id,
        runtime.signature,
        head_app(runtime.signature, StructuralHead.NE, x, T.number(0)),
    )
    problem = specification(
        runtime,
        target=runtime.variable,
        target_sort=S.REAL,
        coverage=Coverage.SOUND_SET,
        externalizable=(condition,),
    )
    assert problem.allows_unresolved() is True
    assert problem.externalizable == (condition,)


def test_a_problem_is_an_immutable_value():
    problem = specification()
    with pytest.raises(dataclasses.FrozenInstanceError):
        problem.operation = "integrate"


def test_a_region_from_another_world_is_rejected(runtime):
    other = bootstrap()
    foreign = runtime_proposition(other, T.TRUE)
    with pytest.raises(ValueError, match="region"):
        specification(runtime, region=foreign)


def test_an_externalizable_premise_from_another_world_is_rejected(runtime):
    other = bootstrap()
    foreign = runtime_proposition(other, T.TRUE)
    with pytest.raises(ValueError, match="externalizable"):
        specification(
            runtime,
            coverage=Coverage.SOUND_SET,
            externalizable=(foreign,),
        )


def test_problem_roles_must_name_the_input_world(runtime):
    other = bootstrap()
    with pytest.raises(ValueError, match="world"):
        specification(runtime, world=other.world.id)


def test_problem_roles_from_another_runtime_are_rejected(runtime):
    other = bootstrap()
    assert other.world.id != runtime.world.id
    assert other.variable == runtime.variable
    with pytest.raises(ValueError, match="world"):
        specification(runtime, roles=other.request.roles)


def test_a_function_problem_binds_its_function_inputs(runtime):
    domain = runtime_proposition(runtime, T.TRUE)
    value = function_value(runtime, domain)
    problem = specification(
        runtime,
        operation="compare_functions",
        result_language=ResultLanguage.PROPOSITION,
        function_inputs=(value, value),
    )
    assert problem.function_inputs == (value, value)
    assert problem.target is None


def test_a_function_problem_has_no_scalar_target(runtime):
    domain = runtime_proposition(runtime, T.TRUE)
    value = function_value(runtime, domain)
    with pytest.raises(ValueError, match="target"):
        specification(
            runtime,
            operation="compare_functions",
            target=runtime.variable,
            target_sort=S.REAL,
            function_inputs=(value,),
        )


def test_function_inputs_must_be_function_values(runtime):
    with pytest.raises(TypeError):
        specification(
            runtime,
            operation="compare_functions",
            function_inputs=(T.number(1),),
        )
    with pytest.raises(TypeError):
        specification(
            runtime,
            operation="compare_functions",
            function_inputs=[],  # type: ignore[arg-type]
        )


def test_a_function_input_domain_from_another_world_is_rejected(runtime):
    other = bootstrap()
    foreign_domain = runtime_proposition(other, T.TRUE)
    value = FunctionValue(
        (FunctionParameter(other.variable, S.REAL),),
        foreign_domain,
        S.REAL,
        (
            FunctionRepresentation(
                T.symbol(other.variable, "x"),
                foreign_domain,
            ),
        ),
    )
    with pytest.raises(ValueError, match="function input"):
        specification(
            runtime,
            operation="compare_functions",
            function_inputs=(value,),
        )


def test_a_function_representation_region_from_another_world_is_rejected(
    runtime,
):
    local = runtime_proposition(runtime, T.TRUE)
    other = bootstrap()
    foreign = runtime_proposition(other, T.TRUE)
    value = FunctionValue(
        (FunctionParameter(runtime.variable, S.REAL),),
        local,
        S.REAL,
        (
            FunctionRepresentation(
                T.symbol(runtime.variable, "x"),
                foreign,
            ),
        ),
    )
    with pytest.raises(ValueError, match="function input"):
        specification(
            runtime,
            operation="compare_functions",
            function_inputs=(value,),
        )


def test_an_approximate_problem_is_refused_at_construction():
    with pytest.raises(ValueError, match="approximate"):
        specification(exactness=Exactness.APPROXIMATE)
    assert specification().exactness is Exactness.EXACT


def test_a_function_problem_cannot_require_an_algebra_interpretation(
    runtime,
):
    domain = runtime_proposition(runtime, T.TRUE)
    value = function_value(runtime, domain)
    with pytest.raises(ValueError, match="interpretation"):
        specification(
            runtime,
            operation="compare_functions",
            result_language=ResultLanguage.PROPOSITION,
            function_inputs=(value,),
            interpretation_requirement=InterpretationRequirement.FORMAL,
        )


def test_a_target_problem_needs_a_domain_requirement(runtime):
    with pytest.raises(ValueError, match="domain requirement"):
        specification(
            runtime,
            target=runtime.variable,
            target_sort=S.REAL,
            domain_requirement=None,
        )


def test_a_target_problem_needs_a_coefficient_domain(runtime):
    with pytest.raises(ValueError, match="coefficient domain"):
        specification(
            runtime,
            target=runtime.variable,
            target_sort=S.REAL,
            domain_requirement=DomainRequirement(None, ValueDomain.REAL),
        )


def test_a_target_problem_value_domain_must_match_the_target_sort(runtime):
    with pytest.raises(ValueError, match="value domain"):
        specification(
            runtime,
            target=runtime.variable,
            target_sort=S.REAL,
            domain_requirement=DomainRequirement(
                ValueDomain.RATIONAL, ValueDomain.INTEGER
            ),
        )


def test_a_function_problem_fixes_real_values_and_no_coefficient(runtime):
    domain = runtime_proposition(runtime, T.TRUE)
    value = function_value(runtime, domain)
    with pytest.raises(ValueError, match="coefficient domain"):
        specification(
            runtime,
            operation="compare_functions",
            result_language=ResultLanguage.PROPOSITION,
            function_inputs=(value,),
            domain_requirement=DomainRequirement(
                ValueDomain.RATIONAL, ValueDomain.REAL
            ),
        )
    with pytest.raises(ValueError, match="real-valued"):
        specification(
            runtime,
            operation="compare_functions",
            result_language=ResultLanguage.PROPOSITION,
            function_inputs=(value,),
            domain_requirement=DomainRequirement(
                None, ValueDomain.RATIONAL
            ),
        )


def test_a_problem_without_a_target_cannot_carry_a_domain_requirement(
    runtime,
):
    with pytest.raises(ValueError, match="without a target"):
        specification(
            runtime,
            domain_requirement=DomainRequirement(
                ValueDomain.RATIONAL, ValueDomain.REAL
            ),
        )


def test_a_domain_requirement_validates_its_fields():
    with pytest.raises(TypeError):
        DomainRequirement("rational", ValueDomain.REAL)  # type: ignore[arg-type]
    with pytest.raises(TypeError):
        DomainRequirement(ValueDomain.RATIONAL, "real")  # type: ignore[arg-type]
    with pytest.raises(ValueError):
        DomainRequirement()


def test_an_integer_target_problem_is_admitted_without_a_region(runtime):
    integer = SymbolId(10_002)
    problem = specification(
        runtime,
        target=integer,
        target_sort=S.INTEGER,
    )
    assert problem.domain_requirement == DomainRequirement(
        ValueDomain.RATIONAL, ValueDomain.INTEGER
    )
    child = runtime.frames.create(
        runtime.frame.id,
        declarations=(Declaration(integer, "n", S.INTEGER),),
    )
    condition = proposition_in(
        runtime.frames,
        child.id,
        runtime.signature,
        head_app(
            runtime.signature,
            StructuralHead.GT,
            T.symbol(integer, "n"),
            T.number(0),
        ),
    )
    with pytest.raises(ValueError, match="dense"):
        specification(
            runtime,
            target=integer,
            target_sort=S.INTEGER,
            region=condition,
        )


def test_an_input_role_sort_must_match_the_binding_view(runtime):
    with pytest.raises(ValueError, match="target role sort"):
        specification(
            runtime,
            target=runtime.variable,
            target_sort=S.RATIONAL,
            inputs=(
                typed_in(
                    runtime.frames,
                    runtime.frame.id,
                    runtime.signature,
                    T.symbol(runtime.variable, "x"),
                ),
            ),
        )


def test_a_problem_region_free_symbol_must_be_bound(runtime):
    unknown = runtime.table.intern("w")
    child = runtime.frames.create(
        runtime.frame.id,
        declarations=(Declaration(unknown, "w", S.REAL),),
    )
    condition = proposition_in(
        runtime.frames,
        child.id,
        runtime.signature,
        head_app(
            runtime.signature,
            StructuralHead.GT,
            T.symbol(unknown, "w"),
            T.number(0),
        ),
    )
    with pytest.raises(ValueError, match="not bound"):
        specification(runtime, region=condition)


def test_a_problem_region_free_symbol_must_be_dense(runtime):
    integer = SymbolId(10_001)
    child = runtime.frames.create(
        runtime.frame.id,
        declarations=(Declaration(integer, "n", S.INTEGER),),
    )
    condition = proposition_in(
        runtime.frames,
        child.id,
        runtime.signature,
        head_app(
            runtime.signature,
            StructuralHead.GT,
            T.symbol(integer, "n"),
            T.number(0),
        ),
    )
    with pytest.raises(ValueError, match="dense"):
        specification(
            runtime,
            parameters=(integer,),
            parameter_sorts=(S.INTEGER,),
            region=condition,
        )


def test_a_problem_region_with_a_bound_dense_symbol_is_admitted(runtime):
    condition = proposition_in(
        runtime.frames,
        runtime.frame.id,
        runtime.signature,
        head_app(
            runtime.signature,
            StructuralHead.GT,
            T.symbol(runtime.variable, "x"),
            T.number(0),
        ),
    )
    problem = specification(
        runtime,
        target=runtime.variable,
        target_sort=S.REAL,
        region=condition,
    )
    assert problem.region is condition


def generator_inputs(runtime, setup, index=0):
    symbol = setup.symbols[index]
    return (
        typed_in(
            runtime.frames,
            setup.frame,
            runtime.signature,
            T.symbol(symbol, runtime.table.name_of(symbol)),
        ),
    )


def test_a_generator_problem_binds_ordered_generators(runtime):
    setup = multivariate_setup(runtime)
    problem = specification(
        runtime,
        operation="groebner_basis",
        variables=setup.symbols,
        variable_sorts=(S.REAL, S.REAL),
        inputs=generator_inputs(runtime, setup),
    )
    assert problem.target is None
    assert problem.variables == setup.symbols
    assert problem.variable_sorts == (S.REAL, S.REAL)
    assert problem.domain_requirement == DomainRequirement(
        ValueDomain.RATIONAL, ValueDomain.REAL
    )


def test_a_generator_problem_needs_a_domain_requirement(runtime):
    setup = multivariate_setup(runtime)
    with pytest.raises(ValueError, match="domain requirement"):
        specification(
            runtime,
            variables=setup.symbols,
            variable_sorts=(S.REAL, S.REAL),
            inputs=generator_inputs(runtime, setup),
            domain_requirement=None,
        )


def test_a_generator_problem_needs_a_coefficient_domain(runtime):
    setup = multivariate_setup(runtime)
    with pytest.raises(ValueError, match="coefficient domain"):
        specification(
            runtime,
            variables=setup.symbols,
            variable_sorts=(S.REAL, S.REAL),
            inputs=generator_inputs(runtime, setup),
            domain_requirement=DomainRequirement(None, ValueDomain.REAL),
        )


def test_a_generator_problem_value_domain_must_match_the_generator_sort(
    runtime,
):
    setup = multivariate_setup(runtime)
    with pytest.raises(ValueError, match="value domain"):
        specification(
            runtime,
            variables=setup.symbols,
            variable_sorts=(S.REAL, S.REAL),
            inputs=generator_inputs(runtime, setup),
            domain_requirement=DomainRequirement(
                ValueDomain.RATIONAL, ValueDomain.INTEGER
            ),
        )


def test_a_generator_problem_needs_one_shared_dense_sort(runtime):
    setup = multivariate_setup(runtime)
    with pytest.raises(ValueError, match="same sort"):
        specification(
            runtime,
            variables=setup.symbols,
            variable_sorts=(S.REAL, S.RATIONAL),
            inputs=generator_inputs(runtime, setup),
        )
    with pytest.raises(ValueError, match="dense"):
        specification(
            runtime,
            variables=setup.symbols,
            variable_sorts=(S.INTEGER, S.INTEGER),
            inputs=generator_inputs(runtime, setup),
        )


def test_a_generator_problem_cannot_require_a_parameter_family(runtime):
    setup = multivariate_setup(runtime)
    with pytest.raises(ValueError, match="parameter-family"):
        specification(
            runtime,
            variables=setup.symbols,
            variable_sorts=(S.REAL, S.REAL),
            inputs=generator_inputs(runtime, setup),
            interpretation_requirement=(
                InterpretationRequirement.PARAMETER_FAMILY
            ),
        )
    for requirement in (
        InterpretationRequirement.FORMAL,
        InterpretationRequirement.EMBEDDED,
    ):
        problem = specification(
            runtime,
            variables=setup.symbols,
            variable_sorts=(S.REAL, S.REAL),
            inputs=generator_inputs(runtime, setup),
            interpretation_requirement=requirement,
        )
        assert problem.interpretation_requirement is requirement


def test_a_function_problem_cannot_carry_generator_roles(runtime):
    setup = multivariate_setup(runtime)
    domain = runtime_proposition(runtime, T.TRUE)
    value = function_value(runtime, domain)
    with pytest.raises(ValueError, match="generator roles"):
        specification(
            runtime,
            operation="compare_functions",
            result_language=ResultLanguage.PROPOSITION,
            variables=setup.symbols,
            variable_sorts=(S.REAL, S.REAL),
            inputs=generator_inputs(runtime, setup),
            function_inputs=(value,),
        )


def test_a_generator_role_sort_must_match_the_input_binding(runtime):
    setup = multivariate_setup(runtime)
    with pytest.raises(ValueError, match="generator role sort"):
        specification(
            runtime,
            variables=(setup.symbols[0],),
            variable_sorts=(S.RATIONAL,),
            inputs=generator_inputs(runtime, setup),
            domain_requirement=DomainRequirement(
                ValueDomain.RATIONAL, ValueDomain.RATIONAL
            ),
        )


def test_a_generator_problem_region_binds_its_generators(runtime):
    setup = multivariate_setup(runtime)
    x = T.symbol(setup.symbols[0], runtime.table.name_of(setup.symbols[0]))
    condition = proposition_in(
        runtime.frames,
        setup.frame,
        runtime.signature,
        head_app(runtime.signature, StructuralHead.GT, x, T.number(0)),
    )
    problem = specification(
        runtime,
        variables=setup.symbols,
        variable_sorts=(S.REAL, S.REAL),
        inputs=generator_inputs(runtime, setup),
        region=condition,
    )
    assert problem.region is condition

    extra = runtime.table.intern("z")
    child = runtime.frames.create(
        setup.frame,
        declarations=(Declaration(extra, "z", S.REAL),),
    )
    foreign_condition = proposition_in(
        runtime.frames,
        child.id,
        runtime.signature,
        head_app(
            runtime.signature,
            StructuralHead.GT,
            T.symbol(extra, "z"),
            T.number(0),
        ),
    )
    with pytest.raises(ValueError, match="not bound"):
        specification(
            runtime,
            variables=(setup.symbols[0],),
            variable_sorts=(S.REAL,),
            inputs=generator_inputs(runtime, setup),
            region=foreign_condition,
        )


def test_the_shared_variable_sort_requires_one_dense_generator_sort():
    empty = VariableRoles(
        None, (), ParameterMode.SPECIFIED_VALUES, WorldId(0)
    )
    with pytest.raises(ValueError, match="at least one variable"):
        shared_variable_sort(empty)
    mixed = VariableRoles(
        None,
        (),
        ParameterMode.SPECIFIED_VALUES,
        WorldId(0),
        None,
        (),
        (SymbolId(1), SymbolId(2)),
        (S.REAL, S.RATIONAL),
    )
    with pytest.raises(ValueError, match="same sort"):
        shared_variable_sort(mixed)
    nondense = VariableRoles(
        None,
        (),
        ParameterMode.SPECIFIED_VALUES,
        WorldId(0),
        None,
        (),
        (SymbolId(1),),
        (S.INTEGER,),
    )
    with pytest.raises(ValueError, match="dense"):
        shared_variable_sort(nondense)
    rational = VariableRoles(
        None,
        (),
        ParameterMode.SPECIFIED_VALUES,
        WorldId(0),
        None,
        (),
        (SymbolId(1), SymbolId(2)),
        (S.RATIONAL, S.RATIONAL),
    )
    assert shared_variable_sort(rational) == S.RATIONAL
