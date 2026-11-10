"""Explicit assembly of the runtime.

One call builds a world, a coefficient structure, a polynomial ring, a chosen
derivation, a bridge between terms and ring elements, the `HasDerivative`
predicate and checker, a frame, and the kernel ledger. Nothing is installed into
module-level state; consumers receive the returned value.

The plain assembly has coefficients in Q and target `x`. The parameterized
assembly separates roles explicitly: formal parameters generate the coefficient
ring, while `x` remains the target, so parameter symbols never become target
generators by accident.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass
from fractions import Fraction
from typing import Any, Generic, TypeVar

from cas.algebra.parents import Parent, ParentRegistry, ParentSpec
from cas.algebra.polynomial import (
    MonomialOrder,
    Polynomial,
    PolynomialRing,
    UnivariatePolynomialRing,
)
from cas.algebra.protocols import Field
from cas.algebra.rational import RationalFunctionField
from cas.algebra.rationals import RationalField
from cas.foundation.ids import SymbolId, WorldId
from cas.kernel.case_merge import (
    CaseMergeCertificate,
    CaseMergeChecker,
    JudgmentLookup,
)
from cas.kernel.condition_checker import ConditionChecker
from cas.kernel.consistency import ContradictionChecker
from cas.kernel.context_rules import HypothesisChecker
from cas.kernel.evidence import Checker, CheckerRegistry, CheckerSpec
from cas.kernel.store import KernelStore
from cas.kernel.trust import (
    BasisKind,
    BasisRef,
    BasisRegistry,
    CertificateSchema,
)
from cas.language import sorts as S
from cas.language.declarations import DeclarationSet, build_language
from cas.language.problems import ParameterMode, ValueDomain, VariableRoles
from cas.language.signatures import LanguageSignature, StructuralHead
from cas.math.algebra.gcd_checker import PolynomialGcdChecker
from cas.math.algebra.gcd_operation import PolynomialGcdOperation
from cas.math.algebra.gcd_specification import (
    GcdCertificate,
    GcdVocabulary,
)
from cas.math.algebra.resultant_checker import ResultantChecker
from cas.math.algebra.resultant_operation import ResultantOperation
from cas.math.algebra.resultant_specification import (
    ResultantCertificate,
    ResultantVocabulary,
)
from cas.math.algebra.root_count_checker import RootCountChecker
from cas.math.algebra.root_count_operation import RootCountOperation
from cas.math.algebra.root_count_specification import (
    RootCountCertificate,
    RootCountVocabulary,
)
from cas.math.calculus.differentiation.certificate import (
    DerivativeCertificate,
)
from cas.math.calculus.differentiation.checker import DerivativeChecker
from cas.math.calculus.differentiation.elementary import (
    ElementaryDifferentiator,
)
from cas.math.calculus.differentiation.elementary_checker import (
    ElementaryDerivativeChecker,
)
from cas.math.calculus.differentiation.operation import (
    DifferentiationOperation,
)
from cas.math.calculus.differentiation.services import (
    ElementaryDerivativeService,
    PolynomialDerivativeService,
)
from cas.math.calculus.differentiation.specialization_operation import (
    SpecializationOperation,
)
from cas.math.calculus.differentiation.specification import DerivativeVocabulary
from cas.math.calculus.differentiation.view import (
    DifferentiationView,
    SpecializationView,
)
from cas.math.calculus.integration.hermite_checker import HermiteChecker
from cas.math.calculus.integration.hermite_operation import (
    HermiteReductionOperation,
)
from cas.math.calculus.integration.hermite_specification import (
    HermiteCertificate,
    HermiteVocabulary,
)
from cas.math.calculus.integration.hermite_view import HermiteView
from cas.math.calculus.integration.operation import IntegrationOperation
from cas.math.calculus.integration.service import (
    PolynomialAntiderivativeService,
)
from cas.math.calculus.integration.view import IntegrationView
from cas.math.elementary.declarations import (
    ElementaryLibrary,
    build_elementary,
    default_elementary_declarations,
)
from cas.math.functions.checker import FunctionEqualityChecker
from cas.math.functions.equality import (
    FunctionEqualityCertificate,
    FunctionEqualityVocabulary,
)
from cas.math.functions.operation import (
    FunctionComparisonOperation,
    FunctionExtensionOperation,
)
from cas.math.solving.linear_checker import LinearSolutionChecker
from cas.math.solving.linear_operation import LinearSolveOperation
from cas.math.solving.linear_specification import (
    LinearSolutionCertificate,
    SolutionSetVocabulary,
)
from cas.operations.capabilities import (
    Capability,
    CapabilityRequirements,
)
from cas.operations.registry import OperationRegistry
from cas.semantics.bridge import (
    ParameterPolynomialBridge,
    PolynomialBridge,
    RationalFunctionBridge,
    SimplePolynomialBridge,
)
from cas.semantics.differential import DifferentialStructure, polynomial_structure
from cas.semantics.frames import (
    Declaration,
    Frame,
    FrameStore,
    World,
    new_world,
)
from cas.semantics.request import AlgebraRequest, Interpretation
from cas.semantics.services import DerivativeService
from cas.semantics.symbols import SymbolTable, standard_language
from cas.syntax import term as T
from cas.workflow.workspace import Workspace

E = TypeVar("E")

# Structures the Q[x] assemblies actually construct: `bootstrap` and
# `bootstrap_elementary` both build a field-backed polynomial ring, its
# rational-function field for Hermite reduction, explicit function values for
# equality, and the finite linear solution set.  Neither registers
# specialization.
_POLYNOMIAL_RUNTIME_CAPABILITIES: CapabilityRequirements = frozenset(
    {
        Capability.FIELD,
        Capability.FUNCTION_VALUE,
        Capability.ORDERED_FIELD,
        Capability.POLYNOMIAL_RING,
        Capability.RATIONAL_FUNCTION_FIELD,
    }
)

# Structures the parameterized assembly actually constructs: field-backed
# polynomial rings and explicit function values, plus point specialization of
# verified generic results.  It does not build a rational-function field or a
# finite-set solver.
_PARAMETERIZED_RUNTIME_CAPABILITIES: CapabilityRequirements = frozenset(
    {
        Capability.FIELD,
        Capability.FUNCTION_VALUE,
        Capability.GENERIC_RESULT,
        Capability.POLYNOMIAL_RING,
    }
)


@dataclass(frozen=True, slots=True, eq=False)
class Runtime(Generic[E]):
    """One assembled world, its algebra view, ledger and supported operation."""

    def __post_init__(self) -> None:
        for operation in self.operations:
            for binding in operation.checker_bindings:
                spec = self.store.checkers.spec(binding.checker_id)
                if spec is None:
                    raise ValueError(
                        f"operation {operation.id!r} names an unregistered "
                        f"checker {binding.checker_id!r}"
                    )
                if spec.world != self.frames.world.id:
                    raise ValueError(
                        f"operation {operation.id!r} binds a checker from "
                        "another world"
                    )
                if binding.problem_kind not in spec.accepted_problem_kinds:
                    raise ValueError(
                        f"operation {operation.id!r} binds a checker that "
                        "does not accept its problem kind"
                    )
                if (
                    binding.specification_kind
                    not in spec.accepted_specification_kinds
                ):
                    raise ValueError(
                        f"operation {operation.id!r} binds a checker that "
                        "does not accept its specification kind"
                    )

    table: SymbolTable
    signature: LanguageSignature
    world: World
    frames: FrameStore
    frame: Frame
    variable: SymbolId
    ring: PolynomialRing[E]
    parent: Parent[Polynomial[E]]
    differential: DifferentialStructure[Polynomial[E]]
    vocabulary: DerivativeVocabulary
    checker: Checker
    store: KernelStore
    bridge: PolynomialBridge[E]
    request: AlgebraRequest
    derivative: DerivativeService
    operations: OperationRegistry
    views: tuple[DifferentiationView[Any], ...]
    specialization: SpecializationView | None = None
    elementary: ElementaryLibrary | None = None

    def view_for(self, target: SymbolId) -> DifferentiationView[Any] | None:
        """The pre-assembled view for one request-local target."""
        for view in self.views:
            if view.target == target:
                return view
        return None


def _core_specs(
    frames: FrameStore, signature: LanguageSignature
) -> dict[str, CheckerSpec]:
    """The scope and condition rules every assembled runtime admits."""
    return {
        ConditionChecker.id: CheckerSpec(
            ConditionChecker(frames, signature),
            CertificateSchema("condition", "1", type(None)),
            frozenset({"discharge"}),
            frozenset({"Condition"}),
            frames.world.id,
        ),
        HypothesisChecker.id: CheckerSpec(
            HypothesisChecker(frames),
            CertificateSchema("hypothesis", "1", type(None)),
            frozenset({"assume"}),
            frozenset({"Hypothesis"}),
            frames.world.id,
        ),
        ContradictionChecker.id: CheckerSpec(
            ContradictionChecker(frames, signature),
            CertificateSchema("contradiction", "1", type(None)),
            frozenset({"consistency"}),
            frozenset({"Contradiction"}),
            frames.world.id,
        ),
    }


def _start(
    *,
    table: SymbolTable | None = None,
    declarations: DeclarationSet | None = None,
) -> tuple[
    SymbolTable,
    DerivativeVocabulary,
    HermiteVocabulary,
    FunctionEqualityVocabulary,
    SolutionSetVocabulary,
    GcdVocabulary,
    ResultantVocabulary,
    RootCountVocabulary,
    LanguageSignature,
    FrameStore,
]:
    """The common world and frame store every assembled runtime starts with.

    With declarations, the language is assembled by the declaration DSL; without
    them it contains only the structural heads and the derivative, Hermite and
    function-equality predicates.
    """
    actual = SymbolTable() if table is None else table
    predicate = actual.intern("HasDerivative")
    vocabulary = DerivativeVocabulary(predicate, "HasDerivative")
    hermite_predicate = actual.intern("HasHermiteReduction")
    hermite_vocabulary = HermiteVocabulary(
        hermite_predicate, "HasHermiteReduction"
    )
    equal_on = actual.intern("EqualOn")
    same_partial = actual.intern("SamePartialFunction")
    function_vocabulary = FunctionEqualityVocabulary(
        equal_on,
        "EqualOn",
        same_partial,
        "SamePartialFunction",
    )
    complete_solutions = actual.intern("HasSolutionSet")
    sound_solutions = actual.intern("HasSolutionSubset")
    solution_vocabulary = SolutionSetVocabulary(
        complete_solutions,
        "HasSolutionSet",
        sound_solutions,
        "HasSolutionSubset",
    )
    gcd_symbol = actual.intern("HasPolynomialGCD")
    gcd_vocabulary = GcdVocabulary(gcd_symbol, "HasPolynomialGCD")
    resultant_symbol = actual.intern("HasResultant")
    resultant_vocabulary = ResultantVocabulary(
        resultant_symbol, "HasResultant"
    )
    root_count_symbol = actual.intern("HasRootCount")
    root_count_vocabulary = RootCountVocabulary(
        root_count_symbol, "HasRootCount"
    )
    extras = {
        predicate: vocabulary.signature,
        hermite_predicate: hermite_vocabulary.signature,
        equal_on: function_vocabulary.equal_on_signature,
        same_partial: function_vocabulary.same_signature,
        complete_solutions: solution_vocabulary.signature,
        sound_solutions: solution_vocabulary.signature,
        gcd_symbol: gcd_vocabulary.signature,
        resultant_symbol: resultant_vocabulary.signature,
        root_count_symbol: root_count_vocabulary.signature,
    }
    signature = (
        standard_language(actual, operators=extras)
        if declarations is None
        else build_language(actual.intern, declarations, extras)
    )
    world = new_world(signature)
    return (
        actual,
        vocabulary,
        hermite_vocabulary,
        function_vocabulary,
        solution_vocabulary,
        gcd_vocabulary,
        resultant_vocabulary,
        root_count_vocabulary,
        signature,
        FrameStore(world),
    )


def _derivative_spec(
    checker: Checker,
    world: WorldId,
    *,
    problem_kind: str = "differentiate",
    extra_problem_kinds: tuple[str, ...] = (),
    dependencies: tuple[BasisRef, ...] = (),
) -> CheckerSpec:
    """The one trust registration shared by derivative checkers."""
    return CheckerSpec(
        checker,
        CertificateSchema("derivative", "1", DerivativeCertificate),
        frozenset({problem_kind, *extra_problem_kinds}),
        frozenset({"HasDerivative"}),
        world,
        dependencies,
        requires_problem=True,
    )


def _case_spec(
    checker: Checker,
    world: WorldId,
) -> CheckerSpec:
    """The trust registration for the kernel case-analysis rule."""
    return CheckerSpec(
        checker,
        CertificateSchema("case_merge", "1", CaseMergeCertificate),
        frozenset({"case_merge"}),
        frozenset({"CaseAnalysis"}),
        world,
    )


def _case_merge(
    frames: FrameStore,
    signature: LanguageSignature,
) -> tuple[JudgmentLookup, CaseMergeChecker]:
    lookup = JudgmentLookup()
    return lookup, CaseMergeChecker(frames, signature, lookup)


def _function_spec(
    checker: Checker,
    world: WorldId,
) -> CheckerSpec:
    """The trust registration for function-equality checkers."""
    return CheckerSpec(
        checker,
        CertificateSchema(
            "function_equality", "1", FunctionEqualityCertificate
        ),
        frozenset({"extend_function", "compare_functions"}),
        frozenset({"EqualOn", "SamePartialFunction"}),
        world,
        requires_problem=True,
    )


def _function_operations(
    signature: LanguageSignature,
    frames: FrameStore,
    vocabulary: FunctionEqualityVocabulary,
    checker_id: str,
    roles: VariableRoles,
) -> tuple[
    FunctionExtensionOperation,
    FunctionComparisonOperation,
]:
    return (
        FunctionExtensionOperation(
            signature, frames, vocabulary, checker_id, roles
        ),
        FunctionComparisonOperation(
            signature, frames, vocabulary, checker_id, roles
        ),
    )


def _function_roles(world: WorldId) -> VariableRoles:
    """The role value for operations that have no target or parameters."""
    return VariableRoles(
        None, (), ParameterMode.SPECIFIED_VALUES, world
    )


def _solution_spec(
    checker: Checker,
    world: WorldId,
) -> CheckerSpec:
    """The trust registration for finite solution-set checkers."""
    return CheckerSpec(
        checker,
        CertificateSchema(
            "linear_solution", "1", LinearSolutionCertificate
        ),
        frozenset({"solve_linear"}),
        frozenset({"HasSolutionSet", "HasSolutionSubset"}),
        world,
        requires_problem=True,
    )


def _solution_operation(
    signature: LanguageSignature,
    frames: FrameStore,
    vocabulary: SolutionSetVocabulary,
    checker_id: str,
    ring: UnivariatePolynomialRing[Fraction],
    bridge: PolynomialBridge[Fraction],
    name_of: Callable[[SymbolId], str],
    request: AlgebraRequest,
) -> LinearSolveOperation:
    return LinearSolveOperation(
        signature,
        frames,
        vocabulary,
        checker_id,
        ring,
        bridge,
        name_of,
        request,
    )


def _gcd_spec(
    checker: Checker,
    world: WorldId,
) -> CheckerSpec:
    """The trust registration for polynomial-gcd checkers."""
    return CheckerSpec(
        checker,
        CertificateSchema("polynomial_gcd", "1", GcdCertificate),
        frozenset({"polynomial_gcd"}),
        frozenset({"HasPolynomialGCD"}),
        world,
        requires_problem=True,
    )


def _gcd_operation(
    signature: LanguageSignature,
    frames: FrameStore,
    vocabulary: GcdVocabulary,
    checker_id: str,
    ring: UnivariatePolynomialRing[Any],
    bridge: PolynomialBridge[Any],
    name_of: Callable[[SymbolId], str],
    request: AlgebraRequest,
) -> PolynomialGcdOperation[Any]:
    return PolynomialGcdOperation(
        signature,
        frames,
        vocabulary,
        checker_id,
        ring,
        bridge,
        name_of,
        request,
    )


def _resultant_spec(
    checker: Checker,
    world: WorldId,
) -> CheckerSpec:
    """The trust registration for resultant checkers."""
    return CheckerSpec(
        checker,
        CertificateSchema("resultant", "1", ResultantCertificate),
        frozenset({"resultant"}),
        frozenset({"HasResultant"}),
        world,
        requires_problem=True,
    )


def _resultant_operation(
    signature: LanguageSignature,
    frames: FrameStore,
    vocabulary: ResultantVocabulary,
    checker_id: str,
    ring: UnivariatePolynomialRing[Fraction],
    bridge: PolynomialBridge[Fraction],
    name_of: Callable[[SymbolId], str],
    request: AlgebraRequest,
) -> ResultantOperation:
    return ResultantOperation(
        signature,
        frames,
        vocabulary,
        checker_id,
        ring,
        bridge,
        name_of,
        request,
    )


def _root_count_spec(
    checker: Checker,
    world: WorldId,
) -> CheckerSpec:
    """The trust registration for real-root-count checkers."""
    return CheckerSpec(
        checker,
        CertificateSchema("root_count", "1", RootCountCertificate),
        frozenset({"root_count"}),
        frozenset({"HasRootCount"}),
        world,
        requires_problem=True,
    )


def _root_count_operation(
    signature: LanguageSignature,
    frames: FrameStore,
    vocabulary: RootCountVocabulary,
    checker_id: str,
    ring: UnivariatePolynomialRing[Any],
    bridge: PolynomialBridge[Any],
    request: AlgebraRequest,
) -> RootCountOperation[Any]:
    return RootCountOperation(
        signature,
        frames,
        vocabulary,
        checker_id,
        ring,
        bridge,
        request,
    )


def _q_coefficient(
    registry: ParentRegistry,
) -> tuple[RationalField, Parent[Fraction]]:
    rationals = RationalField()
    coefficient = registry.intern(ParentSpec("Q"), rationals)
    return rationals, coefficient


def _polynomial_spec(
    base: ParentSpec | None,
    generators: tuple[SymbolId, ...],
    order: MonomialOrder = MonomialOrder.LEX,
) -> ParentSpec:
    """A polynomial description that states every representation choice."""
    return ParentSpec(
        "polynomial",
        base=base,
        generators=generators,
        options=(("monomial_order", order.value),),
    )


def _q_polynomial(
    registry: ParentRegistry,
    variable: SymbolId,
) -> tuple[
    RationalField,
    Parent[Fraction],
    UnivariatePolynomialRing[Fraction],
    Parent[Polynomial[Fraction]],
    DifferentialStructure[Polynomial[Fraction]],
]:
    rationals, coefficient = _q_coefficient(registry)
    ring = UnivariatePolynomialRing(variable, rationals)
    parent = registry.intern(
        _polynomial_spec(coefficient.spec, (variable,)),
        ring,
    )
    differential = polynomial_structure(parent, 0)
    return rationals, coefficient, ring, parent, differential


def _integration_views(
    views: tuple[DifferentiationView[Any], ...],
    *,
    checker_id: str | None = None,
) -> tuple[IntegrationView[Any], ...]:
    """One integration view per differentiation target.

    The antiderivative service uses the same bridge as differentiation, and
    integration is verified by the derivative relation, not by a second trust
    path.  By default the view binds the derivative checker its service names.
    An assembly whose differentiation checker verifies a different fragment
    (the elementary runtime) passes the registered polynomial checker explicitly
    so integration uses the polynomial subfragment without changing the
    differentiation trust path.
    """
    return tuple(
        IntegrationView(
            view.request,
            view.ring,
            view.bridge,
            PolynomialAntiderivativeService(
                view.bridge,
                view.service.checker_id if checker_id is None else checker_id,
                "HasDerivative",
            ),
            view.service.checker_id if checker_id is None else checker_id,
        )
        for view in views
    )


def bootstrap() -> Runtime[Fraction]:
    """Assemble Q[x] with target `x` and no formal parameters."""
    (
        table,
        vocabulary,
        hermite_vocabulary,
        function_vocabulary,
        solution_vocabulary,
        gcd_vocabulary,
        resultant_vocabulary,
        root_count_vocabulary,
        signature,
        frames,
    ) = _start()
    variable = table.intern("x")
    frame = frames.create(
        frames.root.id,
        declarations=(Declaration(variable, "x", S.REAL),),
    )
    registry = ParentRegistry()
    _, coefficient, ring, parent, differential = _q_polynomial(
        registry, variable
    )
    bridge = SimplePolynomialBridge(
        ring,
        parent,
        frames.world.id,
        signature,
        table.name_of,
        T.number,
    )
    request = AlgebraRequest(
        coefficient=coefficient,
        coefficient_domain=ValueDomain.RATIONAL,
        parameter_ring=None,
        roles=VariableRoles(
            variable,
            (),
            ParameterMode.SPECIFIED_VALUES,
            frames.world.id,
            S.REAL,
        ),
        interpretation=Interpretation.FORMAL,
        differential=differential,
    )
    checker = DerivativeChecker(
        ring, signature, vocabulary, bridge, frames, request
    )
    service = PolynomialDerivativeService(
        bridge, differential, checker.id, "HasDerivative"
    )
    view = DifferentiationView(
        request, ring, parent, differential, bridge, service, checker
    )
    hermite_field = RationalFunctionField(ring)
    hermite_parent = registry.intern(
        ParentSpec(
            "rational_function",
            base=parent.spec,
            generators=ring.generators,
            options=(),
        ),
        hermite_field,
    )
    hermite_bridge = RationalFunctionBridge(
        hermite_field,
        hermite_parent,
        frames.world.id,
        signature,
        frames,
        table.name_of,
        T.number,
    )
    hermite_checker = HermiteChecker(
        hermite_bridge,
        hermite_vocabulary,
        request,
    )
    function_checker = FunctionEqualityChecker(
        ring, signature, function_vocabulary, bridge, frames, request
    )
    case_lookup, case_checker = _case_merge(frames, signature)
    solution_checker = LinearSolutionChecker(
        ring, signature, solution_vocabulary, bridge, frames, request
    )
    gcd_checker = PolynomialGcdChecker(
        ring, signature, gcd_vocabulary, bridge, frames, request
    )
    resultant_checker = ResultantChecker(
        ring, signature, resultant_vocabulary, bridge, frames, request
    )
    root_count_checker = RootCountChecker(
        ring, signature, root_count_vocabulary, bridge, frames, request
    )
    specs = {
        checker.id: _derivative_spec(
            checker, frames.world.id, extra_problem_kinds=("integrate",)
        ),
        hermite_checker.id: CheckerSpec(
            hermite_checker,
            CertificateSchema("hermite", "1", HermiteCertificate),
            frozenset({"hermite_reduce"}),
            frozenset({"HasHermiteReduction"}),
            frames.world.id,
            requires_problem=True,
        ),
        function_checker.id: _function_spec(
            function_checker, frames.world.id
        ),
        solution_checker.id: _solution_spec(
            solution_checker, frames.world.id
        ),
        gcd_checker.id: _gcd_spec(gcd_checker, frames.world.id),
        resultant_checker.id: _resultant_spec(
            resultant_checker, frames.world.id
        ),
        root_count_checker.id: _root_count_spec(
            root_count_checker, frames.world.id
        ),
        case_checker.id: _case_spec(case_checker, frames.world.id),
        **_core_specs(frames, signature),
    }
    store = KernelStore(frames, CheckerRegistry(specs))
    case_lookup.bind(store)
    differentiation = DifferentiationOperation(
        signature,
        frames,
        vocabulary,
        (view,),
        table.name_of,
        variable,
    )
    integration = IntegrationOperation(
        signature,
        frames,
        vocabulary,
        _integration_views((view,)),
        table.name_of,
        variable,
    )
    hermite = HermiteReductionOperation(
        signature,
        frames,
        hermite_vocabulary,
        (
            HermiteView(
                request,
                hermite_field,
                hermite_parent,
                hermite_bridge,
                hermite_checker.id,
            ),
        ),
        table.name_of,
        variable,
    )
    function_extension, function_comparison = _function_operations(
        signature,
        frames,
        function_vocabulary,
        function_checker.id,
        _function_roles(frames.world.id),
    )
    solution = _solution_operation(
        signature,
        frames,
        solution_vocabulary,
        solution_checker.id,
        ring,
        bridge,
        table.name_of,
        request,
    )
    gcd_operation = _gcd_operation(
        signature,
        frames,
        gcd_vocabulary,
        gcd_checker.id,
        ring,
        bridge,
        table.name_of,
        request,
    )
    resultant_operation = _resultant_operation(
        signature,
        frames,
        resultant_vocabulary,
        resultant_checker.id,
        ring,
        bridge,
        table.name_of,
        request,
    )
    root_count_operation = _root_count_operation(
        signature,
        frames,
        root_count_vocabulary,
        root_count_checker.id,
        ring,
        bridge,
        request,
    )
    operations = OperationRegistry(
        {
            differentiation.id: differentiation,
            integration.id: integration,
            hermite.id: hermite,
            function_extension.id: function_extension,
            function_comparison.id: function_comparison,
            solution.id: solution,
            gcd_operation.id: gcd_operation,
            resultant_operation.id: resultant_operation,
            root_count_operation.id: root_count_operation,
        },
        provided_capabilities=_POLYNOMIAL_RUNTIME_CAPABILITIES,
    )
    return Runtime(
        table,
        signature,
        frames.world,
        frames,
        frame,
        variable,
        ring,
        parent,
        differential,
        vocabulary,
        checker,
        store,
        bridge,
        request,
        derivative=service,
        operations=operations,
        views=(view,),
    )


def _assemble_parameterized(
    base_field: Field[E],
    base_spec: ParentSpec,
    parameters: tuple[str, ...],
    *,
    parameter_mode: ParameterMode,
    embed_rational: Callable[[Fraction], E],
    render_base: Callable[[E], T.Term],
    target_name: str,
) -> Runtime[Polynomial[E]]:
    """Assemble `K[parameters][target]` over an explicit base field `K`.

    Parameters are ordinary declared symbols, but their role in this request is
    coefficient generator; the target is `target_name`. The bridge maps each
    role explicitly, so the two namespaces cannot be confused.
    """
    if not parameters:
        raise ValueError("a parameterized runtime needs at least one parameter")
    if len(set(parameters)) != len(parameters):
        raise ValueError("parameter names must be distinct")
    if target_name in parameters:
        raise ValueError(
            "the target name cannot also be a parameter"
        )
    if parameter_mode not in {
        ParameterMode.GENERIC_PARAMETERS,
        ParameterMode.ALL_PARAMETER_VALUES,
    }:
        raise ValueError(
            "a formal parameter family needs generic or all-values coverage"
        )
    reserved = {head.value for head in StructuralHead} | {"HasDerivative"}
    for name in parameters:
        if name in reserved:
            raise ValueError(f"parameter name is reserved: {name}")
    (
        table,
        vocabulary,
        _hermite_vocabulary,
        function_vocabulary,
        _solution_vocabulary,
        _gcd_vocabulary,
        _resultant_vocabulary,
        _root_count_vocabulary,
        signature,
        frames,
    ) = _start()
    variable = table.intern(target_name)
    parameter_ids = tuple(table.intern(name) for name in parameters)
    declarations = (Declaration(variable, target_name, S.REAL),) + tuple(
        Declaration(identifier, name, S.REAL)
        for identifier, name in zip(parameter_ids, parameters)
    )
    frame = frames.create(frames.root.id, declarations=declarations)

    registry = ParentRegistry()
    coefficient = registry.intern(base_spec, base_field)
    all_symbols = (variable,) + parameter_ids

    views: list[DifferentiationView[Polynomial[E]]] = []
    specs: dict[str, CheckerSpec] = {}
    ring_cache: dict[
        tuple[SymbolId, ...], PolynomialRing[E]
    ] = {}

    def coefficient_ring_for(
        generators: tuple[SymbolId, ...],
    ) -> PolynomialRing[E]:
        known = ring_cache.get(generators)
        if known is not None:
            return known
        if len(generators) == 1:
            created: PolynomialRing[E] = UnivariatePolynomialRing(
                generators[0], base_field
            )
        else:
            created = PolynomialRing(generators, base_field)
        ring_cache[generators] = created
        return created

    for target in all_symbols:
        coefficient_generators = tuple(
            symbol for symbol in all_symbols if symbol != target
        )
        if not coefficient_generators:
            raise AssertionError(
                "a parameterized view needs a coefficient generator"
            )
        coefficient_ring = coefficient_ring_for(coefficient_generators)
        coefficient_parent = registry.intern(
            _polynomial_spec(coefficient.spec, coefficient_generators),
            coefficient_ring,
        )
        target_ring = PolynomialRing((target,), coefficient_ring)
        target_parent = registry.intern(
            _polynomial_spec(coefficient_parent.spec, (target,)),
            target_ring,
        )

        def embed_coefficient(
            value: Fraction,
            ring: PolynomialRing[E] = coefficient_ring,
        ) -> Polynomial[E]:
            return ring.constant(embed_rational(value))

        bridge = ParameterPolynomialBridge(
            target_ring,
            target_parent,
            coefficient_ring,
            coefficient_parent,
            frames.world.id,
            {
                identifier: index
                for index, identifier in enumerate(
                    coefficient_generators
                )
            },
            signature,
            table.name_of,
            embed_coefficient,
            render_base,
        )
        parameter_parent = coefficient_parent
        view_parameters = coefficient_generators

        differential = polynomial_structure(target_parent, 0)
        checker_id = (
            "calculus.derivative"
            if target == variable
            else f"calculus.derivative.{table.name_of(target)}"
        )
        request = AlgebraRequest(
            coefficient=coefficient,
            coefficient_domain=ValueDomain.RATIONAL,
            parameter_ring=parameter_parent,
            roles=VariableRoles(
                target,
                view_parameters,
                parameter_mode,
                frames.world.id,
                S.REAL,
                tuple(S.REAL for _ in view_parameters),
            ),
            interpretation=Interpretation.PARAMETER_FAMILY,
            differential=differential,
        )
        checker = DerivativeChecker(
            target_ring,
            signature,
            vocabulary,
            bridge,
            frames,
            request,
            identifier=checker_id,
        )
        service = PolynomialDerivativeService(
            bridge, differential, checker.id, "HasDerivative"
        )
        views.append(
            DifferentiationView(
                request,
                target_ring,
                target_parent,
                differential,
                bridge,
                service,
                checker,
            )
        )
        specs[checker.id] = _derivative_spec(
            checker, frames.world.id, extra_problem_kinds=("integrate",)
        )

    base_ring = coefficient_ring_for((variable,))
    if not isinstance(base_ring, UnivariatePolynomialRing):
        raise AssertionError("the specialization view needs K[x]")
    base_parent = registry.intern(
        _polynomial_spec(coefficient.spec, (variable,)),
        base_ring,
    )
    base_differential = polynomial_structure(base_parent, 0)
    base_bridge = SimplePolynomialBridge(
        base_ring,
        base_parent,
        frames.world.id,
        signature,
        table.name_of,
        render_base,
    )
    specialized_request = AlgebraRequest(
        coefficient=coefficient,
        coefficient_domain=ValueDomain.RATIONAL,
        parameter_ring=None,
        roles=VariableRoles(
            variable,
            (),
            ParameterMode.SPECIFIED_VALUES,
            frames.world.id,
            S.REAL,
        ),
        interpretation=Interpretation.EMBEDDED,
        differential=base_differential,
    )
    base_checker = DerivativeChecker(
        base_ring,
        signature,
        vocabulary,
        base_bridge,
        frames,
        specialized_request,
        identifier="calculus.derivative.specialized",
    )
    specs[base_checker.id] = _derivative_spec(
        base_checker, frames.world.id, problem_kind="specialize"
    )
    function_checker = FunctionEqualityChecker(
        base_ring,
        signature,
        function_vocabulary,
        base_bridge,
        frames,
        specialized_request,
    )
    case_lookup, case_checker = _case_merge(frames, signature)
    specs[function_checker.id] = _function_spec(
        function_checker, frames.world.id
    )
    gcd_checker = PolynomialGcdChecker(
        base_ring,
        signature,
        _gcd_vocabulary,
        base_bridge,
        frames,
        specialized_request,
    )
    specs[gcd_checker.id] = _gcd_spec(
        gcd_checker, frames.world.id
    )
    specs[case_checker.id] = _case_spec(
        case_checker, frames.world.id
    )
    specs.update(_core_specs(frames, signature))
    store = KernelStore(frames, CheckerRegistry(specs))
    case_lookup.bind(store)
    specialization_view = SpecializationView(
        base_ring,
        base_parent,
        base_differential,
        base_bridge,
        base_checker,
        specialized_request,
    )
    default = views[0]
    request = default.request
    default_service = default.service
    default_checker = default.checker
    differentiation = DifferentiationOperation(
        signature,
        frames,
        vocabulary,
        tuple(views),
        table.name_of,
        variable,
    )
    integration = IntegrationOperation(
        signature,
        frames,
        vocabulary,
        _integration_views(tuple(views)),
        table.name_of,
        variable,
    )
    specialization_operation = SpecializationOperation(
        signature,
        frames,
        vocabulary,
        table.name_of,
        specialization_view,
        request,
    )
    function_extension, function_comparison = _function_operations(
        signature,
        frames,
        function_vocabulary,
        function_checker.id,
        _function_roles(frames.world.id),
    )
    gcd_operation = _gcd_operation(
        signature,
        frames,
        _gcd_vocabulary,
        gcd_checker.id,
        base_ring,
        base_bridge,
        table.name_of,
        specialized_request,
    )
    operations = OperationRegistry(
        {
            differentiation.id: differentiation,
            integration.id: integration,
            specialization_operation.id: specialization_operation,
            function_extension.id: function_extension,
            function_comparison.id: function_comparison,
            gcd_operation.id: gcd_operation,
        },
        provided_capabilities=_PARAMETERIZED_RUNTIME_CAPABILITIES,
    )
    return Runtime(
        table,
        signature,
        frames.world,
        frames,
        frame,
        variable,
        default.ring,
        default.parent,
        default.differential,
        vocabulary,
        default_checker,
        store,
        default.bridge,
        request,
        derivative=default_service,
        operations=operations,
        views=tuple(views),
        specialization=specialization_view,
    )


def bootstrap_parameterized(
    parameters: tuple[str, ...] = ("a",),
    *,
    parameter_mode: ParameterMode = ParameterMode.ALL_PARAMETER_VALUES,
) -> Runtime[Polynomial[Fraction]]:
    """Assemble Q[parameters][x] with formal parameters as coefficients.

    This is the rational base-field instance of the generic assembly.  The
    ordinary parameter-family request asks for all declared parameter values;
    the polynomial derivative introduces no denominator or branch, so its
    generic result is unconditional and can meet that request.  A caller may
    still ask for `GENERIC_PARAMETERS`, in which case the result claims only the
    formal family.  `SPECIFIED_VALUES` is rejected: this assembly has no exact
    values to fix.
    """
    return _assemble_parameterized(
        RationalField(),
        ParentSpec("Q"),
        parameters,
        parameter_mode=parameter_mode,
        embed_rational=lambda value: Fraction(value),
        render_base=T.number,
        target_name="x",
    )


def bootstrap_parameterized_over(
    base_field: Field[E],
    base_spec: ParentSpec,
    parameters: tuple[str, ...] = ("a",),
    *,
    embed_rational: Callable[[Fraction], E],
    render_base: Callable[[E], T.Term],
    parameter_mode: ParameterMode = ParameterMode.ALL_PARAMETER_VALUES,
    target_name: str = "x",
) -> Runtime[Polynomial[E]]:
    """Assemble `K[parameters][target]` over an explicit base field `K`.

    `embed_rational` maps a rational literal into `K`; `render_base` renders a
    `K` member in the language.  The base field is a parameter of the assembly,
    not a hardcoded Q, so the same code serves a number field or another
    explicitly admitted field.  The base parent is interned from `base_spec`.
    """
    return _assemble_parameterized(
        base_field,
        base_spec,
        parameters,
        parameter_mode=parameter_mode,
        embed_rational=embed_rational,
        render_base=render_base,
        target_name=target_name,
    )


def bootstrap_elementary() -> Runtime[Fraction]:
    """Assemble the declared elementary fragment with target `x` over Q.

    The Q[x] fields are the algebra view of the polynomial subfragment. The
    active candidate generator and checker are the elementary ones; every
    function and law comes from the declaration file admitted at assembly.
    """
    source = default_elementary_declarations()
    table = SymbolTable()
    (
        table,
        vocabulary,
        hermite_vocabulary,
        function_vocabulary,
        solution_vocabulary,
        gcd_vocabulary,
        resultant_vocabulary,
        root_count_vocabulary,
        signature,
        frames,
    ) = _start(table=table, declarations=source)
    basis = BasisRef(
        source.name,
        BasisKind.DECLARATION_FILE,
        "1",
        source.digest,
        frames.world.id,
    )
    library = build_elementary(
        table.intern,
        source,
        reserved=frozenset({"x", "HasDerivative"}),
        basis=basis,
    )
    variable = table.intern("x")
    declarations = (Declaration(variable, "x", S.REAL),) + tuple(
        Declaration(constant.symbol, constant.name, constant.sort)
        for constant in library.constants.values()
    )
    frame = frames.create(frames.root.id, declarations=declarations)

    registry = ParentRegistry()
    _, coefficient, ring, parent, differential = _q_polynomial(
        registry, variable
    )
    bridge = SimplePolynomialBridge(
        ring,
        parent,
        frames.world.id,
        signature,
        table.name_of,
        T.number,
    )
    request = AlgebraRequest(
        coefficient=coefficient,
        coefficient_domain=ValueDomain.RATIONAL,
        parameter_ring=None,
        roles=VariableRoles(
            variable,
            (),
            ParameterMode.SPECIFIED_VALUES,
            frames.world.id,
            S.REAL,
        ),
        interpretation=Interpretation.FORMAL,
        differential=differential,
    )

    checker = ElementaryDerivativeChecker(
        library,
        signature,
        vocabulary,
        variable,
        frames,
        request,
    )
    # Integration of the polynomial subfragment produces a plain derivative
    # certificate, not a rule-instance derivation.  It therefore binds the
    # polynomial derivative checker over the same Q[x] bridge and request;
    # differentiation keeps the elementary checker and its declaration basis.
    polynomial_checker = DerivativeChecker(
        ring,
        signature,
        vocabulary,
        bridge,
        frames,
        request,
        identifier="calculus.derivative.polynomial",
    )
    hermite_field = RationalFunctionField(ring)
    hermite_parent = registry.intern(
        ParentSpec(
            "rational_function",
            base=parent.spec,
            generators=ring.generators,
            options=(),
        ),
        hermite_field,
    )
    hermite_bridge = RationalFunctionBridge(
        hermite_field,
        hermite_parent,
        frames.world.id,
        signature,
        frames,
        table.name_of,
        T.number,
    )
    hermite_checker = HermiteChecker(
        hermite_bridge,
        hermite_vocabulary,
        request,
    )
    function_checker = FunctionEqualityChecker(
        ring, signature, function_vocabulary, bridge, frames, request
    )
    case_lookup, case_checker = _case_merge(frames, signature)
    solution_checker = LinearSolutionChecker(
        ring, signature, solution_vocabulary, bridge, frames, request
    )
    gcd_checker = PolynomialGcdChecker(
        ring, signature, gcd_vocabulary, bridge, frames, request
    )
    resultant_checker = ResultantChecker(
        ring, signature, resultant_vocabulary, bridge, frames, request
    )
    root_count_checker = RootCountChecker(
        ring, signature, root_count_vocabulary, bridge, frames, request
    )
    specs = {
        checker.id: _derivative_spec(
            checker,
            frames.world.id,
            dependencies=(basis,),
        ),
        polynomial_checker.id: _derivative_spec(
            polynomial_checker,
            frames.world.id,
            problem_kind="integrate",
        ),
        hermite_checker.id: CheckerSpec(
            hermite_checker,
            CertificateSchema("hermite", "1", HermiteCertificate),
            frozenset({"hermite_reduce"}),
            frozenset({"HasHermiteReduction"}),
            frames.world.id,
            requires_problem=True,
        ),
        function_checker.id: _function_spec(
            function_checker, frames.world.id
        ),
        solution_checker.id: _solution_spec(
            solution_checker, frames.world.id
        ),
        gcd_checker.id: _gcd_spec(gcd_checker, frames.world.id),
        resultant_checker.id: _resultant_spec(
            resultant_checker, frames.world.id
        ),
        root_count_checker.id: _root_count_spec(
            root_count_checker, frames.world.id
        ),
        case_checker.id: _case_spec(case_checker, frames.world.id),
        **_core_specs(frames, signature),
    }
    store = KernelStore(
        frames,
        CheckerRegistry(specs),
        bases=BasisRegistry((basis,)),
    )
    case_lookup.bind(store)
    differentiator = ElementaryDifferentiator(
        library, signature, variable, table.name_of
    )
    service = ElementaryDerivativeService(
        differentiator, checker.id, "HasDerivative"
    )
    view = DifferentiationView(
        request, ring, parent, differential, bridge, service, checker
    )
    differentiation = DifferentiationOperation(
        signature,
        frames,
        vocabulary,
        (view,),
        table.name_of,
        variable,
    )
    integration = IntegrationOperation(
        signature,
        frames,
        vocabulary,
        _integration_views((view,), checker_id=polynomial_checker.id),
        table.name_of,
        variable,
    )
    hermite = HermiteReductionOperation(
        signature,
        frames,
        hermite_vocabulary,
        (
            HermiteView(
                request,
                hermite_field,
                hermite_parent,
                hermite_bridge,
                hermite_checker.id,
            ),
        ),
        table.name_of,
        variable,
    )
    function_extension, function_comparison = _function_operations(
        signature,
        frames,
        function_vocabulary,
        function_checker.id,
        _function_roles(frames.world.id),
    )
    solution = _solution_operation(
        signature,
        frames,
        solution_vocabulary,
        solution_checker.id,
        ring,
        bridge,
        table.name_of,
        request,
    )
    gcd_operation = _gcd_operation(
        signature,
        frames,
        gcd_vocabulary,
        gcd_checker.id,
        ring,
        bridge,
        table.name_of,
        request,
    )
    resultant_operation = _resultant_operation(
        signature,
        frames,
        resultant_vocabulary,
        resultant_checker.id,
        ring,
        bridge,
        table.name_of,
        request,
    )
    root_count_operation = _root_count_operation(
        signature,
        frames,
        root_count_vocabulary,
        root_count_checker.id,
        ring,
        bridge,
        request,
    )
    operations = OperationRegistry(
        {
            differentiation.id: differentiation,
            integration.id: integration,
            hermite.id: hermite,
            function_extension.id: function_extension,
            function_comparison.id: function_comparison,
            solution.id: solution,
            gcd_operation.id: gcd_operation,
            resultant_operation.id: resultant_operation,
            root_count_operation.id: root_count_operation,
        },
        provided_capabilities=_POLYNOMIAL_RUNTIME_CAPABILITIES,
    )
    return Runtime(
        table,
        signature,
        frames.world,
        frames,
        frame,
        variable,
        ring,
        parent,
        differential,
        vocabulary,
        checker,
        store,
        bridge,
        request,
        derivative=service,
        operations=operations,
        views=(view,),
        elementary=library,
    )


def new_workspace(runtime: Runtime[Any]) -> Workspace:
    """Start an empty workspace over an assembled runtime."""
    return Workspace(runtime)


__all__ = [
    "Runtime",
    "bootstrap",
    "bootstrap_elementary",
    "bootstrap_parameterized",
    "bootstrap_parameterized_over",
    "new_workspace",
]
