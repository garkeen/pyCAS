"""Runtime assembly: everything is explicit and nothing leaks between worlds."""

import pytest

from cas.foundation.ids import SymbolId
from cas.language import sorts as S
from cas.language.problems import ParameterMode
from cas.language.signatures import StructuralHead
from cas.runtime.bootstrap import (
    Runtime,
    bootstrap,
    bootstrap_parameterized,
    new_workspace,
)
from cas.semantics.bridge import ParameterPolynomialBridge
from cas.semantics.request import Interpretation, Role
from cas.workflow.workspace import Workspace


def test_bootstrap_wires_the_world_explicitly():
    runtime = bootstrap()
    assert isinstance(runtime, Runtime)
    assert runtime.variable == runtime.table.lookup("x")
    assert runtime.table.name_of(runtime.variable) == "x"
    assert runtime.signature.head_of(runtime.variable) is None
    assert runtime.frames.world is runtime.world
    assert runtime.world.language is runtime.signature
    assert runtime.frame.world == runtime.world.id
    assert runtime.frames.sort_of(runtime.frame.id, runtime.variable) is S.REAL
    assert runtime.ring.generators == (runtime.variable,)
    assert runtime.parent.ring is runtime.ring
    assert runtime.differential.parent is runtime.parent
    assert runtime.vocabulary.symbol == runtime.table.lookup("HasDerivative")
    assert runtime.signature.operator_of(
        runtime.vocabulary.symbol
    ) == runtime.vocabulary.signature
    assert runtime.store.frames is runtime.frames
    assert runtime.store.checkers.get(runtime.checker.id) is runtime.checker
    assert runtime.checker.id == "calculus.derivative"
    assert runtime.store.stats()["judgments"] == 0
    assert runtime.signature.symbol_of(StructuralHead.PLUS) is not None
    assert runtime.request.parameters == ()
    assert runtime.request.target == runtime.variable
    assert runtime.request.parameter_ring is None
    assert runtime.request.parameter_mode is ParameterMode.SPECIFIED_VALUES
    assert runtime.request.interpretation is Interpretation.FORMAL
    assert runtime.request.role_of(runtime.variable) is Role.TARGET


def test_parameterized_bootstrap_separates_roles():
    runtime = bootstrap_parameterized()
    parameter = runtime.request.parameters[0]
    assert runtime.table.name_of(parameter) == "a"
    assert runtime.variable not in runtime.request.parameters
    assert runtime.ring.generators == (runtime.variable,)
    assert set(runtime.ring.generators).isdisjoint(runtime.request.parameters)
    assert runtime.request.target == runtime.variable
    assert runtime.request.parameter_mode is ParameterMode.GENERIC_PARAMETERS
    assert runtime.request.interpretation is Interpretation.PARAMETER_FAMILY
    assert runtime.request.role_of(runtime.variable) is Role.TARGET
    assert runtime.request.role_of(parameter) is Role.PARAMETER
    assert runtime.frames.sort_of(runtime.frame.id, parameter) is S.REAL
    assert isinstance(runtime.bridge, ParameterPolynomialBridge)
    assert runtime.parent.ring is runtime.ring
    assert runtime.differential.parent is runtime.parent
    assert runtime.store.stats()["judgments"] == 0


def test_multiple_parameters_keep_the_target_separate():
    runtime = bootstrap_parameterized(("a", "b"))
    assert len(runtime.request.parameters) == 2
    assert runtime.ring.generators == (runtime.variable,)
    for parameter in runtime.request.parameters:
        assert runtime.frames.sort_of(runtime.frame.id, parameter) is S.REAL
        assert runtime.request.role_of(parameter) is Role.PARAMETER
    assert runtime.request.role_of(runtime.variable) is Role.TARGET


def test_parameterized_bootstrap_validates_names():
    with pytest.raises(ValueError):
        bootstrap_parameterized(())
    with pytest.raises(ValueError):
        bootstrap_parameterized(("a", "a"))
    with pytest.raises(ValueError):
        bootstrap_parameterized(("x",))
    with pytest.raises(ValueError):
        bootstrap_parameterized(("Plus",))
    with pytest.raises(ValueError):
        bootstrap_parameterized(("HasDerivative",))


def test_separate_assemblies_share_no_state():
    first = bootstrap()
    second = bootstrap()
    assert first.store is not second.store
    assert first.frames is not second.frames
    assert first.table is not second.table
    assert first.parent is not second.parent
    assert first.store.stats()["judgments"] == 0
    assert second.store.stats()["judgments"] == 0
    assert first.frames.count() == second.frames.count() == 2
    assert first.variable == second.variable
    assert first.world is not second.world


def test_new_workspace_starts_at_the_runtime_frame():
    runtime = bootstrap()
    workspace = new_workspace(runtime)
    assert isinstance(workspace, Workspace)
    assert workspace.frame == runtime.frame.id
    assert workspace.expressions() == ()
    assert workspace.links() == ()
    assert workspace.events() == ()
    assert workspace.revision.label == "start"


def test_structural_head_ids_are_not_math_semantics(runtime):
    assert runtime.signature.head_of(runtime.variable) is None
    assert runtime.signature.head_of(runtime.vocabulary.symbol) is None
    assert runtime.signature.symbol_of(StructuralHead.PLUS) not in {
        runtime.variable,
        runtime.vocabulary.symbol,
        SymbolId(10_000),
    }
