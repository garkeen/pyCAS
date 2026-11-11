"""Problem specifications: what is being computed, and to what standard.

A problem is not a command and not a belief. It fixes the typed inputs, the
roles of the free symbols, the region, the result language, the parameter
promise and the coverage demanded of an answer. Budget and execution attempts
are not part of it.

The inputs are `TypedExpr` values: a problem never carries a bare term that has
not been scoped and typed.  All inputs must be read in one meaning world; they
may come from different frames of that world, because a later frame may extend
the environment in which an earlier input keeps its meaning.

Operation-specific parameters (for example an integration method or an
elimination order) belong to the operation's own spec record; they are added
with that operation rather than guessed here.

`VariableRoles` is the single authoritative role value.  A problem and the
algebra request that resolves it share the same immutable value; an operation
selects a pre-assembled request and never invents a second target or parameter
mode.  The role set is world-scoped: its `SymbolId` values are local to the
meaning world it names, so the same integer is not a global symbol identity
across worlds.  Binding positions and binder-aware roles need a
typed-expression consumer and are deliberately not fields here yet.

A function problem fixes its `FunctionValue` objects, not only their
representation terms.  The intrinsic domain, parameter binding and every
representation region are part of the function object identity; a bare term
does not identify the function whose relation is being proved.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import StrEnum

from cas.foundation.ids import SymbolId, WorldId
from cas.language import sorts as S
from cas.language.functions import FunctionValue
from cas.language.propositions import Proposition
from cas.language.typing import TypedExpr
from cas.syntax import binding as B


class ParameterMode(StrEnum):
    """What a result may assume about parameters."""

    SPECIFIED_VALUES = "specified_values"
    GENERIC_PARAMETERS = "generic_parameters"
    ALL_PARAMETER_VALUES = "all_parameter_values"


class Exactness(StrEnum):
    """Whether a result is required to be exact or may be approximate.

    Only exact problems are admitted in this fragment: no approximate checker
    exists, and silently accepting an approximate request would let an exact
    answer masquerade as the requested standard.
    """

    EXACT = "exact"
    APPROXIMATE = "approximate"


class InterpretationRequirement(StrEnum):
    """The language-level interpretation an algebra problem requires.

    This is deliberately language-owned.  `AlgebraRequest` maps its own
    `Interpretation` onto this value; `language` never imports `semantics`.
    """

    FORMAL = "formal"
    PARAMETER_FAMILY = "parameter_family"
    EMBEDDED = "embedded"


class ValueDomain(StrEnum):
    """The numeric range a problem admits for coefficients or values.

    These are declared requirements, not representations.  A problem may
    require integer values while the resolved parent is Q[x]; the parent lives
    in `AlgebraRequest` and is never inferred from this label.  There is no
    `ANY` escape value: a request either names a domain or leaves the
    requirement absent.
    """

    INTEGER = "integer"
    RATIONAL = "rational"
    REAL = "real"
    COMPLEX = "complex"


def value_domain_of_sort(sort: S.Sort) -> ValueDomain:
    """The value domain a scalar target sort denotes.

    This is the single sort-to-domain mapping shared by `ProblemSpec` and
    `AlgebraRequest`.  A non-scalar sort has no admitted value domain in this
    fragment; the precise `ValueError` keeps the refusal honest instead of
    inventing a domain.
    """
    if sort == S.INTEGER:
        return ValueDomain.INTEGER
    if sort == S.RATIONAL:
        return ValueDomain.RATIONAL
    if sort == S.REAL:
        return ValueDomain.REAL
    if sort == S.COMPLEX:
        return ValueDomain.COMPLEX
    raise ValueError(f"the sort {sort!r} has no scalar value domain")


@dataclass(frozen=True, slots=True)
class DomainRequirement:
    """The language-level coefficient range and allowed value domain.

    `coefficient` is the coefficient range the problem requires; the resolved
    coefficient parent lives in `AlgebraRequest`, never here.  `values` is the
    allowed value (target/result) domain.  A function problem fixes
    `coefficient=None` because function equality in this fragment is
    real-valued and has no coefficient structure.  A requirement that names
    neither field is not a requirement and is rejected.
    """

    coefficient: ValueDomain | None = None
    values: ValueDomain | None = None

    def __post_init__(self) -> None:
        if self.coefficient is not None and not isinstance(
            self.coefficient, ValueDomain
        ):
            raise TypeError(
                "a domain requirement coefficient must be a ValueDomain or "
                "None"
            )
        if self.values is not None and not isinstance(
            self.values, ValueDomain
        ):
            raise TypeError(
                "a domain requirement value domain must be a ValueDomain or "
                "None"
            )
        if self.coefficient is None and self.values is None:
            raise ValueError(
                "a domain requirement needs a coefficient range or a value "
                "domain"
            )


class Coverage(StrEnum):
    """How much of the answer set the request demands."""

    ONE_VERIFIED = "one_verified"
    SOUND_SET = "sound_set"
    COMPLETE_SET = "complete_set"


class ResultLanguage(StrEnum):
    """The shape an accepted result must take."""

    EXPRESSION = "expression"
    PROPOSITION = "proposition"
    SET = "set"
    DECOMPOSITION = "decomposition"


class Role(StrEnum):
    """A symbol's role inside one fixed request.

    `TARGET` names the single variable a univariate request differentiates,
    integrates or solves for.  `GENERATOR` names the ordered variables of a
    multivariate request (a polynomial ring's generators); the order is the
    ring's generator order, never inferred from names.  `PARAMETER` names the
    formal parameters of a parameter family.  A request uses exactly one of the
    target/generator shapes in this slice.
    """

    TARGET = "target"
    GENERATOR = "generator"
    PARAMETER = "parameter"


@dataclass(frozen=True, slots=True)
class VariableRoles:
    """The target, generator and parameter roles fixed for one request.

    The value is language-owned and immutable.  A `ProblemSpec` and its matching
    `AlgebraRequest` hold the very same value, so a target, generator set or
    parameter mode cannot be chosen twice with different results.  `target` is
    optional only because a multivariate problem binds `variables` instead and
    a problem without an algebra view (for example function equality) has no
    target role; an algebra request requires one of the two shapes.

    `variables` is the ordered generator role tuple of a multivariate request.
    Its order is the ring's generator order and is never inferred from symbol
    names.  `target` and `variables` are mutually exclusive, and this slice
    does not combine generator roles with formal parameters: a multivariate
    request over a parameter family needs the parameterized algebra assembly,
    which is not wired yet.  `variable_sorts` records each generator's sort and
    is present exactly when `variables` is nonempty.

    `world` is the meaning world whose symbol namespace the target, generator
    and parameter `SymbolId` values belong to.  A bare integer id is not a
    global identity: the same integer may name different symbols in two worlds.
    `None` means the role set has not yet been bound to a world; `ProblemSpec`
    and `AlgebraRequest` reject that unbound state at their own boundaries.

    `target_sort`/`parameter_sorts`/`variable_sorts` are the binding sorts of
    the world-scoped role symbols.  They are required exactly when the
    corresponding role is present.  Full binding positions remain open with
    binder-aware typing; these fields only make the current fragment's role
    symbols sortable and keep the region-density check honest.
    """

    target: SymbolId | None
    parameters: tuple[SymbolId, ...] = ()
    parameter_mode: ParameterMode = ParameterMode.SPECIFIED_VALUES
    world: WorldId | None = None
    target_sort: S.Sort | None = None
    parameter_sorts: tuple[S.Sort, ...] = ()
    variables: tuple[SymbolId, ...] = ()
    variable_sorts: tuple[S.Sort, ...] = ()

    def __post_init__(self) -> None:
        if self.world is not None and (
            isinstance(self.world, bool)
            or not isinstance(self.world, int)
        ):
            raise TypeError("a role set world must be a WorldId or None")
        if self.target is not None and (
            isinstance(self.target, bool)
            or not isinstance(self.target, int)
        ):
            raise TypeError("a target role must be a SymbolId or None")
        if not isinstance(self.parameters, tuple):
            raise TypeError("parameter roles must be a tuple")
        if any(
            isinstance(symbol, bool) or not isinstance(symbol, int)
            for symbol in self.parameters
        ):
            raise TypeError("parameter roles must be SymbolId values")
        if len(set(self.parameters)) != len(self.parameters):
            raise ValueError("parameters must be distinct")
        if self.target is not None and self.target in self.parameters:
            raise ValueError("a symbol cannot be both the target and a parameter")
        if not isinstance(self.variables, tuple):
            raise TypeError("generator roles must be a tuple")
        if any(
            isinstance(symbol, bool) or not isinstance(symbol, int)
            for symbol in self.variables
        ):
            raise TypeError("generator roles must be SymbolId values")
        if len(set(self.variables)) != len(self.variables):
            raise ValueError("generator roles must be distinct")
        if self.target is not None and self.variables:
            raise ValueError(
                "a role set cannot have both a target and generator roles"
            )
        if self.variables and self.parameters:
            raise ValueError(
                "a role set cannot have both generator roles and parameters"
            )
        if not isinstance(self.parameter_mode, ParameterMode):
            raise TypeError("a role set needs a parameter mode")
        if (
            self.parameter_mode is not ParameterMode.SPECIFIED_VALUES
            and not self.parameters
        ):
            raise ValueError("generic parameter modes need declared parameters")
        if self.target is None:
            if self.target_sort is not None:
                raise ValueError(
                    "a role set without a target cannot carry a target sort"
                )
        elif self.target_sort is None:
            raise ValueError("a target role needs a target sort")
        elif not isinstance(self.target_sort, S.Sort):
            raise TypeError("a target role needs a Sort target sort")
        if not isinstance(self.parameter_sorts, tuple):
            raise TypeError("parameter role sorts must be a tuple")
        if not self.parameters:
            if self.parameter_sorts:
                raise ValueError(
                    "a role set without parameters cannot carry parameter sorts"
                )
        else:
            if len(self.parameter_sorts) != len(self.parameters):
                raise ValueError(
                    "parameter sorts must match the parameter roles"
                )
            if any(
                not isinstance(sort, S.Sort)
                for sort in self.parameter_sorts
            ):
                raise TypeError(
                    "parameter role sorts must be Sort values"
                )
        if not isinstance(self.variable_sorts, tuple):
            raise TypeError("variable role sorts must be a tuple")
        if not self.variables:
            if self.variable_sorts:
                raise ValueError(
                    "a role set without generator roles cannot carry variable "
                    "sorts"
                )
        else:
            if len(self.variable_sorts) != len(self.variables):
                raise ValueError(
                    "variable sorts must match the generator roles"
                )
            if any(
                not isinstance(sort, S.Sort)
                for sort in self.variable_sorts
            ):
                raise TypeError("variable role sorts must be Sort values")

    def role_of(self, symbol_id: SymbolId) -> Role | None:
        """The role of `symbol_id` in this request, if it has one."""
        if self.target is not None and symbol_id == self.target:
            return Role.TARGET
        if symbol_id in self.parameters:
            return Role.PARAMETER
        if symbol_id in self.variables:
            return Role.GENERATOR
        return None


def shared_variable_sort(roles: VariableRoles) -> S.Sort:
    """The one dense scalar sort shared by a generator-mode role set.

    A multivariate request over the current region fragment needs every
    generator to carry the same `RATIONAL` or `REAL` sort: the region
    certificates only reason over dense rational/real coordinates, and a mixed
    generator sort would make the bridge's per-generator sort agreement check
    meaningless.  This is the single rule `ProblemSpec` and `AlgebraRequest`
    share; a role set with no generators is refused rather than returning a
    vacuous sort.
    """
    if not roles.variables:
        raise ValueError("a generator role set needs at least one variable")
    sorts = roles.variable_sorts
    if len(sorts) != len(roles.variables):
        raise ValueError("variable sorts must match the generator roles")
    if any(sort != sorts[0] for sort in sorts):
        raise ValueError(
            "every generator of one request needs the same sort"
        )
    if sorts[0] != S.RATIONAL and sorts[0] != S.REAL:
        raise ValueError(
            "generator sorts must be rational or real; the current region "
            "fragment is dense"
        )
    return sorts[0]


@dataclass(frozen=True, slots=True)
class ProblemSpec:
    """A fixed problem statement.

    `roles` fixes the target, generator and parameter roles once.  `target`,
    `variables`, `parameters` and `parameter_mode` are derived views, not
    independently constructible fields.  This slice admits either a single
    target role or an ordered, nonempty generator tuple; the two shapes are
    mutually exclusive and generator roles do not combine with parameters.

    `externalizable` lists premises the request explicitly allows to remain
    outside the answer. A complete-set request may not externalize anything:
    an unhandled case cannot be moved into an external obligation.

    `region` is a total condition in this batch.  The current region consumers
    (`problem_mismatch`, the differentiation/integration proposal builders and
    the workspace) read `region.term`; a partial condition would have its
    definedness premises silently ignored.  Until those consumers move to
    `RegionSpec`, a region with premises is rejected at construction.

    `function_inputs` fixes the explicit function objects a function problem is
    about.  A `FunctionValue` carries its parameter binding, intrinsic domain
    and every representation region, and those are part of the function's
    identity; two values with the same representation term but different
    domains are different functions.  The checker therefore binds its
    certificate to these values, not to bare terms.  A function problem has no
    scalar target, and every function domain/representation region must be read
    in the same meaning world as the typed inputs.

    `exactness` fixes the answer standard.  Only `EXACT` is admitted in this
    fragment: there is no approximate checker, so accepting `APPROXIMATE` would
    silently claim a standard no consumer can verify.

    `interpretation_requirement` is the language-owned interpretation an algebra
    problem requires.  It must be `None` for a function problem, and
    `ProblemBuilt`/`ExecutionRequest` require it to match the resolved
    `AlgebraRequest`.  A generator problem cannot require the parameter-family
    interpretation: this slice has no multivariate parameter assembly, so
    accepting the claim would misdescribe the request.  `ProblemSpec` itself
    never imports `semantics`.

    `domain_requirement` is the language-level domain binding.  A problem with a
    target role or with generator roles fixes both the coefficient range and
    the allowed value domain; the value domain is the same sort-to-domain
    mapping `AlgebraRequest` exposes, so a problem and its resolved parent
    cannot disagree.  A generator-mode problem requires all generator sorts to
    be identical and dense (`RATIONAL`/`REAL`); `shared_variable_sort` is the
    single rule the problem and its algebra request share.  A function problem
    fixes `coefficient=None` and real values: function equality is real-valued
    in this fragment and has no coefficient structure.  A core or utility
    problem without a target, generator roles or function input leaves the
    requirement `None`; the resolved parent, when one exists, stays in
    `AlgebraRequest`.

    Every free variable of `region` and of each `externalizable` premise must be
    bound by an input binding, a role, or a function parameter, and its sort must
    be `RATIONAL` or `REAL`.  This is the current dense-region fragment: it makes
    the existing dense `problem_mismatch` region inclusion sound for problems and
    deliberately refuses unknown, integer, complex or unbound coordinates.  It is
    not a general semialgebraic region or value-domain algebra.
    """

    operation: str
    inputs: tuple[TypedExpr, ...]
    roles: VariableRoles
    region: Proposition | None
    result_language: ResultLanguage
    coverage: Coverage
    externalizable: tuple[Proposition, ...] = ()
    function_inputs: tuple[FunctionValue, ...] = ()
    exactness: Exactness = Exactness.EXACT
    interpretation_requirement: InterpretationRequirement | None = None
    domain_requirement: DomainRequirement | None = None

    def __post_init__(self) -> None:
        if not self.operation:
            raise ValueError("a problem needs an operation identifier")
        if not self.inputs:
            raise ValueError("a problem needs at least one input")
        if any(not isinstance(item, TypedExpr) for item in self.inputs):
            raise TypeError("problem inputs must be typed expressions")
        world = self.inputs[0].meaning.world
        if len({item.meaning.world for item in self.inputs}) != 1:
            raise ValueError(
                "problem inputs must share one meaning world"
            )
        if not isinstance(self.roles, VariableRoles):
            raise TypeError("a problem needs fixed variable roles")
        if self.roles.world is None:
            raise ValueError(
                "a problem needs a world-scoped role set"
            )
        if self.roles.world != world:
            raise ValueError(
                "the problem roles belong to another meaning world"
            )
        if self.roles.target is not None and self.roles.target_sort is None:
            raise ValueError(
                "a problem with a target role needs its target sort"
            )
        if self.roles.parameters and not self.roles.parameter_sorts:
            raise ValueError(
                "a problem with parameter roles needs their parameter sorts"
            )
        if self.region is not None:
            if not isinstance(self.region, Proposition):
                raise TypeError("a problem region must be a proposition")
            if self.region.definedness:
                raise ValueError(
                    "a problem region must be a total condition; this batch's "
                    "region consumers compare condition terms and do not "
                    "account for definedness premises"
                )
            if self.region.meaning.world != world:
                raise ValueError(
                    "the problem region was read in another meaning world"
                )
        if not isinstance(self.result_language, ResultLanguage):
            raise TypeError("a problem needs a result language")
        if not isinstance(self.coverage, Coverage):
            raise TypeError("a problem needs a coverage requirement")
        if not isinstance(self.exactness, Exactness):
            raise TypeError("a problem needs an exactness requirement")
        if self.exactness is not Exactness.EXACT:
            raise ValueError(
                "this runtime has no approximate checker; only exact problems "
                "are admitted"
            )
        if self.interpretation_requirement is not None and not isinstance(
            self.interpretation_requirement, InterpretationRequirement
        ):
            raise TypeError(
                "a problem interpretation requirement must be an "
                "InterpretationRequirement or None"
            )
        if self.roles.variables and (
            self.interpretation_requirement
            is InterpretationRequirement.PARAMETER_FAMILY
        ):
            raise ValueError(
                "a generator problem cannot require a parameter-family "
                "interpretation"
            )
        if any(
            not isinstance(item, Proposition)
            for item in self.externalizable
        ):
            raise TypeError("externalizable premises must be propositions")
        for premise in self.externalizable:
            if premise.meaning.world != world:
                raise ValueError(
                    "an externalizable premise was read in another meaning "
                    "world"
                )
        if self.externalizable and self.coverage is Coverage.COMPLETE_SET:
            raise ValueError(
                "a complete-set request cannot externalize premises: "
                "unhandled cases would masquerade as coverage"
            )
        if not isinstance(self.function_inputs, tuple):
            raise TypeError("problem function inputs must be a tuple")
        if any(
            not isinstance(item, FunctionValue)
            for item in self.function_inputs
        ):
            raise TypeError(
                "problem function inputs must be FunctionValue values"
            )
        if self.function_inputs:
            if self.roles.variables:
                raise ValueError(
                    "a function problem cannot carry generator roles"
                )
            if self.roles.target is not None:
                raise ValueError(
                    "a function problem has no scalar target"
                )
            if self.interpretation_requirement is not None:
                raise ValueError(
                    "a function problem has no algebra interpretation "
                    "requirement"
                )
            for value in self.function_inputs:
                if value.intrinsic_domain.meaning.world != world:
                    raise ValueError(
                        "a function input intrinsic domain was read in "
                        "another meaning world"
                    )
                for representation in value.representations:
                    if representation.valid_on.meaning.world != world:
                        raise ValueError(
                            "a function input representation region was read "
                            "in another meaning world"
                        )
        self._check_domain_requirement()
        self._check_region_bindings()

    def _check_domain_requirement(self) -> None:
        """Bind the language-level domain requirement to the role structure."""
        requirement = self.domain_requirement
        if requirement is not None and not isinstance(
            requirement, DomainRequirement
        ):
            raise TypeError(
                "a problem domain requirement must be a DomainRequirement or "
                "None"
            )
        if self.roles.target is not None:
            if requirement is None:
                raise ValueError(
                    "a problem with a target role needs a domain requirement"
                )
            if requirement.coefficient is None:
                raise ValueError(
                    "a target problem needs a coefficient domain"
                )
            target_sort = self.roles.target_sort
            if target_sort is None:
                raise ValueError(
                    "a problem with a target role needs its target sort"
                )
            if requirement.values != value_domain_of_sort(target_sort):
                raise ValueError(
                    "the problem value domain does not match the target sort"
                )
            return
        if self.roles.variables:
            if requirement is None:
                raise ValueError(
                    "a generator problem needs a domain requirement"
                )
            if requirement.coefficient is None:
                raise ValueError(
                    "a generator problem needs a coefficient domain"
                )
            sort = shared_variable_sort(self.roles)
            if requirement.values != value_domain_of_sort(sort):
                raise ValueError(
                    "the problem value domain does not match the generator "
                    "sort"
                )
            return
        if self.function_inputs:
            if requirement is None:
                raise ValueError(
                    "a function problem needs a domain requirement"
                )
            if requirement.coefficient is not None:
                raise ValueError(
                    "a function problem has no coefficient domain"
                )
            if requirement.values is not ValueDomain.REAL:
                raise ValueError(
                    "function equality is stated for real-valued functions"
                )
            return
        if requirement is not None:
            raise ValueError(
                "a problem without a target, generator roles or function "
                "inputs cannot carry a domain requirement"
            )

    def _check_region_bindings(self) -> None:
        """Bind every region coordinate to a dense declared role/input sort."""
        known: dict[SymbolId, S.Sort] = {}

        def bind(symbol: SymbolId, sort: S.Sort) -> None:
            previous = known.get(symbol)
            if previous is not None and previous != sort:
                raise ValueError(
                    "the problem binds one symbol with two different sorts"
                )
            known[symbol] = sort

        for item in self.inputs:
            for free in item.bindings.symbols:
                bind(free.symbol_id, free.sort)

        target = self.roles.target
        target_sort = self.roles.target_sort
        if target is not None:
            if target_sort is None:
                raise ValueError(
                    "a problem with a target role needs its target sort"
                )
            previous = known.get(target)
            if previous is not None and previous != target_sort:
                raise ValueError(
                    "the target role sort does not match the input binding"
                )
            bind(target, target_sort)

        parameters = self.roles.parameters
        parameter_sorts = self.roles.parameter_sorts
        if parameters:
            if len(parameter_sorts) != len(parameters):
                raise ValueError(
                    "the parameter role sorts must match the parameter roles"
                )
            for symbol, sort in zip(parameters, parameter_sorts):
                previous = known.get(symbol)
                if previous is not None and previous != sort:
                    raise ValueError(
                        "a parameter role sort does not match the input "
                        "binding"
                    )
                bind(symbol, sort)

        variables = self.roles.variables
        variable_sorts = self.roles.variable_sorts
        if variables:
            if len(variable_sorts) != len(variables):
                raise ValueError(
                    "the variable role sorts must match the generator roles"
                )
            for symbol, sort in zip(variables, variable_sorts):
                previous = known.get(symbol)
                if previous is not None and previous != sort:
                    raise ValueError(
                        "a generator role sort does not match the input "
                        "binding"
                    )
                bind(symbol, sort)

        for value in self.function_inputs:
            for parameter in value.parameters:
                previous = known.get(parameter.symbol)
                if previous is not None and previous != parameter.sort:
                    raise ValueError(
                        "a function parameter sort does not match the problem "
                        "binding"
                    )
                bind(parameter.symbol, parameter.sort)

        def check(proposition: Proposition, label: str) -> None:
            pending = [proposition]
            while pending:
                current = pending.pop()
                for symbol in B.variable_symbols(current.term):
                    sort = known.get(symbol)
                    if sort is None:
                        raise ValueError(
                            f"a {label} free symbol is not bound by the "
                            "problem inputs, roles or function parameters"
                        )
                    if sort != S.RATIONAL and sort != S.REAL:
                        raise ValueError(
                            f"a {label} free symbol must have a rational or "
                            "real sort; the current region fragment is dense"
                        )
                pending.extend(current.definedness)

        if self.region is not None:
            check(self.region, "problem region")
        for premise in self.externalizable:
            check(premise, "externalizable premise")

    @property
    def target(self) -> SymbolId | None:
        """The target role fixed by this problem."""
        return self.roles.target

    @property
    def parameters(self) -> tuple[SymbolId, ...]:
        """The parameter roles fixed by this problem."""
        return self.roles.parameters

    @property
    def variables(self) -> tuple[SymbolId, ...]:
        """The ordered generator roles fixed by this problem."""
        return self.roles.variables

    @property
    def variable_sorts(self) -> tuple[S.Sort, ...]:
        """The generator sorts fixed by this problem."""
        return self.roles.variable_sorts

    @property
    def parameter_mode(self) -> ParameterMode:
        """The parameter promise fixed by this problem."""
        return self.roles.parameter_mode

    def allows_unresolved(self) -> bool:
        """Whether the request accepts an answer with open premises."""
        return bool(self.externalizable)


__all__ = [
    "Coverage",
    "DomainRequirement",
    "Exactness",
    "InterpretationRequirement",
    "ParameterMode",
    "ProblemSpec",
    "ResultLanguage",
    "Role",
    "ValueDomain",
    "VariableRoles",
    "shared_variable_sort",
    "value_domain_of_sort",
]
