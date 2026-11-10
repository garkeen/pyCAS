"""Explicit function values keep their intrinsic domain and representation region."""

import pytest
from support import (
    head_app,
    runtime_proposition,
    typed_in,
    variable,
    verification_context,
)

from cas.kernel.commit import (
    CommitProposal,
    Rejected,
    RejectedKind,
    ValidatedCommitBatch,
    validate_commit,
)
from cas.kernel.evidence import (
    CheckRequest,
    InvalidEvidence,
    Unverified,
    Verified,
)
from cas.language import sorts as S
from cas.language.decisions import Reason
from cas.language.functions import (
    FunctionEquality,
    FunctionParameter,
    FunctionRepresentation,
    FunctionValue,
    same_parameter_shape,
    same_parameter_signature,
    same_representation_multiset,
)
from cas.language.problems import (
    Coverage,
    DomainRequirement,
    ParameterMode,
    ProblemSpec,
    ResultLanguage,
    ValueDomain,
    VariableRoles,
)
from cas.language.roles import CandidateRole
from cas.language.signatures import StructuralHead
from cas.math.functions.equality import (
    FunctionEqualityCertificate,
    FunctionEqualityVocabulary,
    coverage_matches_value,
    equal_on,
    function_coverage_certificate,
    function_region,
    same_partial_function,
)
from cas.operations.protocols import FunctionExtensionInput
from cas.runtime.bootstrap import new_workspace
from cas.semantics.conditions import is_subregion
from cas.semantics.frames import Declaration
from cas.semantics.regions import (
    CoversCertificate,
    proved_subregion,
    verify_region_certificate,
)
from cas.syntax import term as T
from cas.workflow.records import (
    FunctionDefined,
    FunctionRefused,
    OperationStatus,
    TaskState,
)


def nonnegative(runtime):
    x = variable(runtime)
    return runtime_proposition(
        runtime,
        head_app(runtime.signature, StructuralHead.GE, x, T.number(0)),
    )


def square(runtime):
    return head_app(
        runtime.signature,
        StructuralHead.POWER,
        variable(runtime),
        T.number(2),
    )


def _or(runtime, *terms):
    return head_app(runtime.signature, StructuralHead.OR, *terms)


def _gt(runtime, bound):
    return head_app(
        runtime.signature,
        StructuralHead.GT,
        variable(runtime),
        T.number(bound),
    )


def _lt(runtime, bound):
    return head_app(
        runtime.signature,
        StructuralHead.LT,
        variable(runtime),
        T.number(bound),
    )


def function_value(runtime, domain):
    return FunctionValue(
        (FunctionParameter(runtime.variable, S.REAL),),
        domain,
        S.REAL,
        (FunctionRepresentation(square(runtime), domain),),
    )


def function_vocabulary(runtime):
    equal = runtime.table.lookup("EqualOn")
    same = runtime.table.lookup("SamePartialFunction")
    assert equal is not None and same is not None
    return FunctionEqualityVocabulary(
        equal, "EqualOn", same, "SamePartialFunction"
    )


def test_function_value_substitutes_arguments_into_all_representations(runtime):
    domain = nonnegative(runtime)
    value = function_value(runtime, domain)
    applications = value.applications((T.number(3),))
    assert len(applications) == 1
    assert applications[0].term == head_app(
        runtime.signature,
        StructuralHead.POWER,
        T.number(3),
        T.number(2),
    )
    assert applications[0].valid_on == head_app(
        runtime.signature,
        StructuralHead.GE,
        T.number(3),
        T.number(0),
    )
    with pytest.raises(ValueError):
        value.applications(())


def test_function_value_keeps_multiple_representations(runtime):
    domain = nonnegative(runtime)
    value = function_value(runtime, domain)
    extended = value.with_representation(
        head_app(
            runtime.signature,
            StructuralHead.TIMES,
            variable(runtime),
            variable(runtime),
        ),
        domain,
    )
    assert len(value.representations) == 1
    assert len(extended.representations) == 2
    assert extended.representations[0] is value.representations[0]


def test_the_checker_requires_the_candidate_role(runtime):
    domain = nonnegative(runtime)
    value = function_value(runtime, domain)
    representation = value.representations[0].term
    vocabulary = function_vocabulary(runtime)
    claim = runtime_proposition(
        runtime,
        equal_on(vocabulary, domain.term, representation, representation),
    )
    certificate = FunctionEqualityCertificate(domain.term, value, value, 0, 0)
    checker = runtime.store.checkers.get("functions.equality")
    assert checker is not None
    for role in (None, CandidateRole.RESULT):
        outcome = checker.check(
            CheckRequest(
                runtime.frame.id,
                (claim,),
                (),
                certificate,
                candidate=claim.term,
                candidate_role=role,
                context=verification_context(runtime),
            )
        )
        assert isinstance(outcome, InvalidEvidence)
        assert "candidate role" in outcome.detail
    for candidate in (None, T.number(0)):
        outcome = checker.check(
            CheckRequest(
                runtime.frame.id,
                (claim,),
                (),
                certificate,
                candidate=candidate,
                candidate_role=CandidateRole.CONCLUSION,
                context=verification_context(runtime),
            )
        )
        assert isinstance(outcome, InvalidEvidence)
        assert "candidate" in outcome.detail
    verified = checker.check(
        CheckRequest(
            runtime.frame.id,
            (claim,),
            (),
            certificate,
            candidate=claim.term,
            candidate_role=CandidateRole.CONCLUSION,
            context=verification_context(runtime),
        )
    )
    assert isinstance(verified, Verified)


def test_the_checker_requires_a_trusted_verification_context(runtime):
    domain = nonnegative(runtime)
    value = function_value(runtime, domain)
    representation = value.representations[0].term
    vocabulary = function_vocabulary(runtime)
    claim = runtime_proposition(
        runtime,
        equal_on(vocabulary, domain.term, representation, representation),
    )
    certificate = FunctionEqualityCertificate(domain.term, value, value, 0, 0)
    problem = ProblemSpec(
        "compare_functions",
        (
            typed_in(
                runtime.frames,
                runtime.frame.id,
                runtime.signature,
                representation,
            ),
            typed_in(
                runtime.frames,
                runtime.frame.id,
                runtime.signature,
                representation,
            ),
        ),
        VariableRoles(
            None,
            (),
            ParameterMode.SPECIFIED_VALUES,
            runtime.world.id,
        ),
        None,
        ResultLanguage.PROPOSITION,
        Coverage.ONE_VERIFIED,
        function_inputs=(value, value),
        domain_requirement=DomainRequirement(
            coefficient=None, values=ValueDomain.REAL
        ),
    )
    checker = runtime.store.checkers.get("functions.equality")
    assert checker is not None
    outcome = checker.check(
        CheckRequest(
            runtime.frame.id,
            (claim,),
            (),
            certificate,
            problem=problem,
            candidate=claim.term,
            candidate_role=CandidateRole.CONCLUSION,
        )
    )
    assert isinstance(outcome, InvalidEvidence)
    assert outcome.detail == (
        "the check request has no trusted verification context"
    )


def test_a_function_check_request_with_an_algebra_snapshot_is_invalid(runtime):
    domain = nonnegative(runtime)
    value = function_value(runtime, domain)
    representation = value.representations[0].term
    vocabulary = function_vocabulary(runtime)
    claim = runtime_proposition(
        runtime,
        equal_on(vocabulary, domain.term, representation, representation),
    )
    certificate = FunctionEqualityCertificate(domain.term, value, value, 0, 0)
    checker = runtime.store.checkers.get("functions.equality")
    assert checker is not None
    outcome = checker.check(
        CheckRequest(
            runtime.frame.id,
            (claim,),
            (),
            certificate,
            candidate=claim.term,
            candidate_role=CandidateRole.CONCLUSION,
            context=verification_context(
                runtime, algebra=runtime.request
            ),
        )
    )
    assert isinstance(outcome, InvalidEvidence)
    assert outcome.detail == "a function problem has no algebra request"


def test_the_right_role_publishes_the_new_representation(runtime):
    domain = nonnegative(runtime)
    value = function_value(runtime, domain)
    left = value.representations[0].term
    right = head_app(
        runtime.signature,
        StructuralHead.TIMES,
        variable(runtime),
        variable(runtime),
    )
    extended = value.with_representation(right, domain)
    vocabulary = function_vocabulary(runtime)
    claim = runtime_proposition(
        runtime,
        equal_on(vocabulary, domain.term, left, right),
    )
    certificate = FunctionEqualityCertificate(
        domain.term, value, extended, 0, 1
    )
    checker = runtime.store.checkers.get("functions.equality")
    assert checker is not None
    wrong = checker.check(
        CheckRequest(
            runtime.frame.id,
            (claim,),
            (),
            certificate,
            candidate=claim.term,
            candidate_role=CandidateRole.RIGHT,
            context=verification_context(runtime),
        )
    )
    assert isinstance(wrong, InvalidEvidence)
    verified = checker.check(
        CheckRequest(
            runtime.frame.id,
            (claim,),
            (),
            certificate,
            candidate=right,
            candidate_role=CandidateRole.RIGHT,
            context=verification_context(runtime),
        )
    )
    assert isinstance(verified, Verified)


def unrelated_frame(runtime):
    return runtime.frames.create(runtime.frames.root.id)


def check_equality(runtime, claim, certificate):
    checker = runtime.store.checkers.get("functions.equality")
    assert checker is not None
    return checker.check(
        CheckRequest(
            runtime.frame.id,
            (claim,),
            (),
            certificate,
            candidate=claim.term,
            candidate_role=CandidateRole.CONCLUSION,
            context=verification_context(runtime),
        )
    )


def test_an_intrinsic_domain_from_an_unrelated_frame_is_invalid_evidence(runtime):
    visible = runtime_proposition(runtime, T.TRUE)
    foreign = runtime_proposition(
        runtime, T.TRUE, frame=unrelated_frame(runtime).id
    )
    value = FunctionValue(
        (FunctionParameter(runtime.variable, S.REAL),),
        foreign,
        S.REAL,
        (FunctionRepresentation(square(runtime), visible),),
    )
    vocabulary = function_vocabulary(runtime)
    claim = runtime_proposition(
        runtime,
        equal_on(vocabulary, T.TRUE, square(runtime), square(runtime)),
    )
    certificate = FunctionEqualityCertificate(T.TRUE, value, value, 0, 0)
    outcome = check_equality(runtime, claim, certificate)
    assert isinstance(outcome, InvalidEvidence)
    assert outcome.detail == (
        "the certificate's left intrinsic domain belongs to another scope"
    )


def test_a_representation_region_from_an_unrelated_frame_is_invalid_evidence(runtime):
    visible = runtime_proposition(runtime, T.TRUE)
    foreign = runtime_proposition(
        runtime, T.TRUE, frame=unrelated_frame(runtime).id
    )
    left = FunctionValue(
        (FunctionParameter(runtime.variable, S.REAL),),
        visible,
        S.REAL,
        (FunctionRepresentation(square(runtime), visible),),
    )
    right = FunctionValue(
        (FunctionParameter(runtime.variable, S.REAL),),
        visible,
        S.REAL,
        (FunctionRepresentation(square(runtime), foreign),),
    )
    vocabulary = function_vocabulary(runtime)
    claim = runtime_proposition(
        runtime,
        equal_on(vocabulary, T.TRUE, square(runtime), square(runtime)),
    )
    certificate = FunctionEqualityCertificate(T.TRUE, left, right, 0, 0)
    outcome = check_equality(runtime, claim, certificate)
    assert isinstance(outcome, InvalidEvidence)
    assert outcome.detail == (
        "the certificate's right representation region belongs to another scope"
    )


def test_same_partial_function_checks_every_representation_scope(runtime):
    visible = runtime_proposition(runtime, T.TRUE)
    foreign = runtime_proposition(
        runtime, T.TRUE, frame=unrelated_frame(runtime).id
    )
    left = FunctionValue(
        (FunctionParameter(runtime.variable, S.REAL),),
        visible,
        S.REAL,
        (
            FunctionRepresentation(square(runtime), visible),
            FunctionRepresentation(square(runtime), foreign),
        ),
    )
    right = FunctionValue(
        (FunctionParameter(runtime.variable, S.REAL),),
        visible,
        S.REAL,
        (FunctionRepresentation(square(runtime), visible),),
    )
    vocabulary = function_vocabulary(runtime)
    claim = runtime_proposition(
        runtime,
        same_partial_function(vocabulary, square(runtime), square(runtime)),
    )
    certificate = FunctionEqualityCertificate(None, left, right, 0, 0)
    outcome = check_equality(runtime, claim, certificate)
    assert isinstance(outcome, InvalidEvidence)
    assert outcome.detail == (
        "the certificate's left representation 1 region belongs to "
        "another scope"
    )


def test_components_from_an_ancestor_frame_remain_visible(runtime):
    ancestor = runtime_proposition(
        runtime, T.TRUE, frame=runtime.frames.root.id
    )
    left = FunctionValue(
        (FunctionParameter(runtime.variable, S.REAL),),
        ancestor,
        S.REAL,
        (FunctionRepresentation(square(runtime), ancestor),),
    )
    right = FunctionValue(
        (FunctionParameter(runtime.variable, S.REAL),),
        ancestor,
        S.REAL,
        (FunctionRepresentation(product(runtime), ancestor),),
    )
    vocabulary = function_vocabulary(runtime)
    claim = runtime_proposition(
        runtime,
        equal_on(vocabulary, T.TRUE, square(runtime), product(runtime)),
    )
    certificate = FunctionEqualityCertificate(T.TRUE, left, right, 0, 0)
    outcome = check_equality(runtime, claim, certificate)
    assert isinstance(outcome, Verified)


def test_partial_function_equality_is_conservative(runtime):
    domain = nonnegative(runtime)
    value = function_value(runtime, domain)
    assert value.same_partial_function(value) is FunctionEquality.SAME
    assert value.equal_on(domain, value) is FunctionEquality.SAME
    two_arguments = FunctionValue(
        (
            FunctionParameter(runtime.variable, S.REAL),
            FunctionParameter(runtime.table.intern("y"), S.REAL),
        ),
        domain,
        S.REAL,
        (FunctionRepresentation(square(runtime), domain),),
    )
    assert (
        value.same_partial_function(two_arguments)
        is FunctionEquality.DIFFERENT
    )
    different_domain = function_value(runtime, runtime_proposition(
        runtime,
        head_app(
            runtime.signature,
            StructuralHead.GE,
            variable(runtime),
            T.number(1),
        ),
    ))
    assert (
        value.same_partial_function(different_domain)
        is FunctionEquality.UNKNOWN
    )
    different_representation = FunctionValue(
        (FunctionParameter(runtime.variable, S.REAL),),
        domain,
        S.REAL,
        (FunctionRepresentation(variable(runtime), domain),),
    )
    assert (
        value.equal_on(domain, different_representation)
        is FunctionEquality.UNKNOWN
    )


def test_workspace_application_records_neutral_expressions_and_conditions(runtime):
    workspace = new_workspace(runtime)
    domain = nonnegative(runtime)
    outcome = workspace.define_function(
        (FunctionParameter(runtime.variable, S.REAL),),
        domain,
        S.REAL,
        square(runtime),
        domain,
        "f",
    )
    assert isinstance(outcome, FunctionDefined)
    result = workspace.apply_function(outcome.function, (T.number(3),))
    assert result.status is OperationStatus.APPLIED
    assert len(result.applications) == 1
    assert result.applications[0].term == head_app(
        runtime.signature,
        StructuralHead.POWER,
        T.number(3),
        T.number(2),
    )
    assert result.conditions == (
        head_app(
            runtime.signature,
            StructuralHead.GE,
            T.number(3),
            T.number(0),
        ),
    )
    wrong_arity = workspace.apply_function(outcome.function, ())
    assert wrong_arity.status is OperationStatus.INVALID


def test_workspace_extension_records_a_new_function_version(runtime):
    workspace = new_workspace(runtime)
    domain = nonnegative(runtime)
    defined = workspace.define_function(
        (FunctionParameter(runtime.variable, S.REAL),),
        domain,
        S.REAL,
        square(runtime),
        domain,
        "f",
    )
    assert isinstance(defined, FunctionDefined)
    true = runtime_proposition(runtime, T.TRUE)
    representation = workspace.intake(square(runtime), "extension")
    extended = workspace.extend_function(
        defined.function, representation, true, true
    )
    assert isinstance(extended, FunctionDefined)
    assert extended.function.id == defined.function.id
    assert extended.function.version != defined.function.version
    assert extended.function.value.intrinsic_domain is true
    assert len(extended.function.value.representations) == 2
    assert extended.function.representation_index == 1
    assert workspace.functions() == (defined.function, extended.function)
    assert defined.function.value.intrinsic_domain is domain


def test_a_function_value_keeps_its_domain_and_representation_region(runtime):
    workspace = new_workspace(runtime)
    domain = nonnegative(runtime)
    outcome = workspace.define_function(
        (FunctionParameter(runtime.variable, S.REAL),),
        domain,
        S.REAL,
        square(runtime),
        domain,
        "f",
    )
    assert isinstance(outcome, FunctionDefined)
    function = outcome.function
    assert function.value.intrinsic_domain is domain
    assert function.value.representations[0].valid_on is domain
    assert workspace.functions() == (function,)

    result = workspace.differentiate_function(function, runtime.variable)
    assert result.status is OperationStatus.CONDITIONAL
    assert result.candidate is not None
    assert result.candidate.problem.region is domain
    assert result.region is not None
    assert result.region.term == domain.term
    assert result.verifications[0].status is OperationStatus.VERIFIED
    assert result.verifications[0].condition is not None
    assert result.verifications[0].condition.term == domain.term
    assert workspace.functions() == (function,)
    assert function.value.intrinsic_domain is domain


def test_a_representation_cannot_exceed_the_intrinsic_domain(runtime):
    workspace = new_workspace(runtime)
    domain = nonnegative(runtime)
    true = runtime_proposition(runtime, T.TRUE)
    outcome = workspace.define_function(
        (FunctionParameter(runtime.variable, S.REAL),),
        domain,
        S.REAL,
        square(runtime),
        true,
        "f",
    )
    assert isinstance(outcome, FunctionRefused)
    assert "intrinsic domain" in outcome.detail
    assert workspace.functions() == ()
    assert workspace.expressions() == ()
    assert runtime.store.stats()["judgments"] == 0


def test_a_neutral_expression_is_differentiated_independently(runtime):
    workspace = new_workspace(runtime)
    domain = nonnegative(runtime)
    defined = workspace.define_function(
        (FunctionParameter(runtime.variable, S.REAL),),
        domain,
        S.REAL,
        square(runtime),
        domain,
        "f",
    )
    assert isinstance(defined, FunctionDefined)

    neutral = workspace.intake(square(runtime), "neutral")
    result = workspace.differentiate(neutral, runtime.variable)
    assert result.status is OperationStatus.VERIFIED
    assert result.region is None
    assert workspace.functions() == (defined.function,)


def shifted(runtime):
    return head_app(
        runtime.signature,
        StructuralHead.PLUS,
        variable(runtime),
        T.number(1),
    )


def product(runtime):
    return head_app(
        runtime.signature,
        StructuralHead.TIMES,
        variable(runtime),
        variable(runtime),
    )


def define(workspace, runtime, term, domain, label):
    outcome = workspace.define_function(
        (FunctionParameter(runtime.variable, S.REAL),),
        domain,
        S.REAL,
        term,
        domain,
        label,
    )
    assert isinstance(outcome, FunctionDefined)
    return outcome.function


def test_compare_functions_proves_same_partial_function(runtime):
    workspace = new_workspace(runtime)
    domain = nonnegative(runtime)
    left = define(workspace, runtime, square(runtime), domain, "f")
    right = define(workspace, runtime, square(runtime), domain, "g")
    result = workspace.compare_functions(left, right)
    assert result.status is OperationStatus.VERIFIED
    assert result.result is not None
    assert result.candidate is not None
    assert result.candidate.algebra is None
    assert result.candidate.problem.result_language.value == "proposition"
    assert result.verifications[0].judgment is not None


def test_equal_on_uses_polynomial_identity_on_a_region(runtime):
    workspace = new_workspace(runtime)
    true = runtime_proposition(runtime, T.TRUE)
    left = define(workspace, runtime, square(runtime), true, "f")
    right = define(workspace, runtime, product(runtime), true, "g")
    same = workspace.compare_functions(left, right)
    assert same.status is OperationStatus.UNSUPPORTED
    on_true = workspace.compare_functions(left, right, region=true)
    assert on_true.status is OperationStatus.VERIFIED
    wrong = define(workspace, runtime, shifted(runtime), true, "h")
    refuted = workspace.compare_functions(left, wrong, region=true)
    assert refuted.status is OperationStatus.REFUTED
    assert refuted.candidate is not None
    assert refuted.candidate.state.value == "refuted"


def test_extension_requires_agreement_on_the_old_domain(runtime):
    workspace = new_workspace(runtime)
    domain = nonnegative(runtime)
    true = runtime_proposition(runtime, T.TRUE)
    function = define(workspace, runtime, square(runtime), domain, "f")
    bad = workspace.intake(shifted(runtime), "bad extension")
    refused = workspace.extend_function(function, bad, true, true)
    assert isinstance(refused, FunctionRefused)
    assert "not proved" in refused.detail
    assert workspace.functions() == (function,)
    good = workspace.intake(product(runtime), "good extension")
    extended = workspace.extend_function(function, good, true, true)
    assert isinstance(extended, FunctionDefined)
    assert len(extended.function.value.representations) == 2


def test_extension_records_a_verified_representation_cover(runtime):
    workspace = new_workspace(runtime)
    old_domain = nonnegative(runtime)
    function = define(workspace, runtime, square(runtime), old_domain, "f")
    bigger = runtime_proposition(
        runtime,
        _or(runtime, old_domain.term, _lt(runtime, -1)),
    )
    representation = workspace.intake(product(runtime), "extension")
    extended = workspace.extend_function(
        function, representation, bigger, bigger
    )
    assert isinstance(extended, FunctionDefined)
    assert extended.function.value.intrinsic_domain is bigger
    assert len(extended.function.value.representations) == 2
    assert extended.function.representation_index == 1

    link = workspace.links()[0]
    assert link.status is OperationStatus.VERIFIED
    assert link.judgment is not None
    candidate = workspace.candidates()[-1]
    certificate = candidate.certificate
    assert isinstance(certificate, FunctionEqualityCertificate)
    assert isinstance(certificate.coverage, CoversCertificate)
    assert certificate.right.intrinsic_domain is bigger
    assert certificate.right.representations[-1].valid_on is bigger
    assert certificate.coverage.region.coordinates == (runtime.variable,)
    assert certificate.coverage.region.sorts == (
        (runtime.variable, S.REAL),
    )
    assert certificate.coverage.pieces[0].coordinates == (runtime.variable,)
    assert certificate.coverage.pieces[0].sorts == (
        (runtime.variable, S.REAL),
    )
    assert verify_region_certificate(certificate.coverage, runtime.signature)
    assert coverage_matches_value(certificate.coverage, certificate.right)
    assert certificate.coverage.region.condition is bigger
    assert certificate.coverage.pieces == (
        function_region(certificate.right, old_domain),
        function_region(certificate.right, bigger),
    )


def test_an_uncovered_extension_domain_is_refused_without_a_version(runtime):
    workspace = new_workspace(runtime)
    old_domain = nonnegative(runtime)
    function = define(workspace, runtime, square(runtime), old_domain, "f")
    bigger = runtime_proposition(runtime, _gt(runtime, -2))
    representation = workspace.intake(product(runtime), "extension")
    refused = workspace.extend_function(
        function, representation, bigger, old_domain
    )
    assert isinstance(refused, FunctionRefused)
    assert "not covered" in refused.detail
    assert workspace.functions() == (function,)
    assert workspace.construction_relations() == ()
    assert workspace.links() == ()
    assert workspace.candidates() == ()
    assert runtime.store.stats()["judgments"] == 0
    task = workspace.tasks()[-1]
    assert task.state is TaskState.BLOCKED
    assert task.candidates == ()
    assert task.blocker is not None
    assert task.blocker.reason is Reason.GUARDED
    assert task.blocker.missing == frozenset({"representation_coverage"})
    assert task.blocker.conditions == (old_domain, old_domain)


def test_extension_cannot_shrink_the_intrinsic_domain(runtime):
    workspace = new_workspace(runtime)
    domain = nonnegative(runtime)
    smaller = runtime_proposition(
        runtime,
        head_app(
            runtime.signature,
            StructuralHead.GE,
            variable(runtime),
            T.number(1),
        ),
    )
    function = define(workspace, runtime, square(runtime), domain, "f")
    representation = workspace.intake(square(runtime), "extension")
    refused = workspace.extend_function(
        function, representation, smaller, smaller
    )
    assert isinstance(refused, FunctionRefused)
    assert "old domain" in refused.detail


def test_undo_hides_a_function_and_redo_restores_it(runtime):
    workspace = new_workspace(runtime)
    domain = nonnegative(runtime)
    outcome = workspace.define_function(
        (FunctionParameter(runtime.variable, S.REAL),),
        domain,
        S.REAL,
        square(runtime),
        domain,
        "f",
    )
    assert isinstance(outcome, FunctionDefined)
    assert workspace.undo()
    assert workspace.functions() == ()
    assert workspace.expressions() == ()
    assert workspace.redo()
    assert workspace.functions() == (outcome.function,)
    assert len(workspace.expressions()) == 1


def test_equal_on_rejects_different_parameter_signatures(runtime):
    workspace = new_workspace(runtime)
    domain = nonnegative(runtime)
    one_argument = workspace.define_function(
        (FunctionParameter(runtime.variable, S.REAL),),
        domain,
        S.REAL,
        square(runtime),
        domain,
        "one",
    )
    two_arguments = workspace.define_function(
        (
            FunctionParameter(runtime.variable, S.REAL),
            FunctionParameter(runtime.table.intern("y"), S.REAL),
        ),
        domain,
        S.REAL,
        square(runtime),
        domain,
        "two",
    )
    assert isinstance(one_argument, FunctionDefined)
    assert isinstance(two_arguments, FunctionDefined)
    result = workspace.compare_functions(
        one_argument.function,
        two_arguments.function,
        region=domain,
    )
    assert result.status not in (
        OperationStatus.VERIFIED,
        OperationStatus.CONDITIONAL,
    )
    assert result.candidate is None


def one_argument_value(runtime, term, domain, symbol=None):
    parameter = runtime.variable if symbol is None else symbol
    return FunctionValue(
        (FunctionParameter(parameter, S.REAL),),
        domain,
        S.REAL,
        (FunctionRepresentation(term, domain),),
    )


def test_duplicate_representations_are_rejected(runtime):
    domain = nonnegative(runtime)
    representation = FunctionRepresentation(square(runtime), domain)
    with pytest.raises(ValueError):
        FunctionValue(
            (FunctionParameter(runtime.variable, S.REAL),),
            domain,
            S.REAL,
            (representation, representation),
        )
    value = one_argument_value(runtime, square(runtime), domain)
    with pytest.raises(ValueError):
        value.with_representation(square(runtime), domain)


def test_representation_multisets_compare_with_multiplicity(runtime):
    domain = nonnegative(runtime)
    left = FunctionValue(
        (FunctionParameter(runtime.variable, S.REAL),),
        domain,
        S.REAL,
        (
            FunctionRepresentation(square(runtime), domain),
            FunctionRepresentation(variable(runtime), domain),
        ),
    )
    reordered = FunctionValue(
        (FunctionParameter(runtime.variable, S.REAL),),
        domain,
        S.REAL,
        (
            FunctionRepresentation(variable(runtime), domain),
            FunctionRepresentation(square(runtime), domain),
        ),
    )
    assert same_representation_multiset(left, reordered)
    assert left.same_partial_function(reordered) is FunctionEquality.SAME
    replaced = FunctionValue(
        (FunctionParameter(runtime.variable, S.REAL),),
        domain,
        S.REAL,
        (
            FunctionRepresentation(square(runtime), domain),
            FunctionRepresentation(shifted(runtime), domain),
        ),
    )
    assert not same_representation_multiset(left, replaced)
    assert (
        left.same_partial_function(replaced)
        is FunctionEquality.UNKNOWN
    )
    one_way = one_argument_value(runtime, square(runtime), domain)
    assert not same_representation_multiset(left, one_way)


def test_same_text_conditions_from_different_meanings_are_not_equal(runtime):
    visible = runtime_proposition(runtime, T.TRUE)
    foreign = runtime_proposition(
        runtime, T.TRUE, frame=unrelated_frame(runtime).id
    )
    left = FunctionValue(
        (FunctionParameter(runtime.variable, S.REAL),),
        visible,
        S.REAL,
        (FunctionRepresentation(square(runtime), visible),),
    )
    right = FunctionValue(
        (FunctionParameter(runtime.variable, S.REAL),),
        foreign,
        S.REAL,
        (FunctionRepresentation(square(runtime), foreign),),
    )
    assert left.intrinsic_domain.term == right.intrinsic_domain.term
    assert (
        left.same_partial_function(right)
        is FunctionEquality.UNKNOWN
    )
    same_domain = FunctionValue(
        (FunctionParameter(runtime.variable, S.REAL),),
        visible,
        S.REAL,
        (FunctionRepresentation(square(runtime), foreign),),
    )
    assert (
        left.same_partial_function(same_domain)
        is FunctionEquality.UNKNOWN
    )


def test_alpha_equivalent_parameters_are_unknown(runtime):
    y = runtime.table.intern("y")
    child = runtime.frames.create(
        runtime.frame.id, declarations=(Declaration(y, "y", S.REAL),)
    )
    true = runtime_proposition(runtime, T.TRUE, child.id)
    left = one_argument_value(runtime, square(runtime), true)
    right = one_argument_value(
        runtime, square(runtime), true, symbol=y
    )
    assert same_parameter_shape(left, right)
    assert not same_parameter_signature(left, right)
    assert (
        left.same_partial_function(right)
        is FunctionEquality.UNKNOWN
    )
    assert left.equal_on(true, right) is FunctionEquality.UNKNOWN

    vocabulary = function_vocabulary(runtime)
    claim = runtime_proposition(
        runtime,
        same_partial_function(
            vocabulary, square(runtime), square(runtime)
        ),
        child.id,
    )
    certificate = FunctionEqualityCertificate(None, left, right, 0, 0)
    checker = runtime.store.checkers.get("functions.equality")
    assert checker is not None
    outcome = checker.check(
        CheckRequest(
            child.id,
            (claim,),
            (),
            certificate,
            candidate=claim.term,
            candidate_role=CandidateRole.CONCLUSION,
            context=verification_context(runtime, child.id),
        )
    )
    assert isinstance(outcome, Unverified)
    assert outcome.reason is Reason.FRAGMENT
    assert "alpha-equivalence" in outcome.detail


def test_same_partial_function_compares_condition_identity(runtime):
    visible = runtime_proposition(runtime, T.TRUE)
    ancestor = runtime_proposition(
        runtime, T.TRUE, frame=runtime.frames.root.id
    )
    left = one_argument_value(runtime, square(runtime), visible)
    right = FunctionValue(
        (FunctionParameter(runtime.variable, S.REAL),),
        ancestor,
        S.REAL,
        (FunctionRepresentation(square(runtime), ancestor),),
    )
    vocabulary = function_vocabulary(runtime)
    claim = runtime_proposition(
        runtime,
        same_partial_function(
            vocabulary, square(runtime), square(runtime)
        ),
    )
    certificate = FunctionEqualityCertificate(None, left, right, 0, 0)
    outcome = check_equality(runtime, claim, certificate)
    assert isinstance(outcome, Unverified)
    assert outcome.reason is Reason.FRAGMENT
    assert "intrinsic domains" in outcome.detail


def test_the_checker_compares_representation_multisets(runtime):
    domain = runtime_proposition(runtime, T.TRUE)
    left = FunctionValue(
        (FunctionParameter(runtime.variable, S.REAL),),
        domain,
        S.REAL,
        (
            FunctionRepresentation(square(runtime), domain),
            FunctionRepresentation(variable(runtime), domain),
        ),
    )
    right = FunctionValue(
        (FunctionParameter(runtime.variable, S.REAL),),
        domain,
        S.REAL,
        (
            FunctionRepresentation(square(runtime), domain),
            FunctionRepresentation(shifted(runtime), domain),
        ),
    )
    vocabulary = function_vocabulary(runtime)
    claim = runtime_proposition(
        runtime,
        same_partial_function(
            vocabulary, square(runtime), square(runtime)
        ),
    )
    certificate = FunctionEqualityCertificate(None, left, right, 0, 0)
    outcome = check_equality(runtime, claim, certificate)
    assert isinstance(outcome, Unverified)
    assert outcome.reason is Reason.FRAGMENT
    assert "multisets" in outcome.detail


def test_a_mismatched_coverage_certificate_is_invalid_evidence(runtime):
    old_domain = nonnegative(runtime)
    left = function_value(runtime, old_domain)
    true = runtime_proposition(runtime, T.TRUE)
    genuine = left.extended(true, product(runtime), true)
    bigger = runtime_proposition(runtime, _gt(runtime, -2))
    impostor = left.extended(bigger, product(runtime), old_domain)
    coverage = function_coverage_certificate(genuine, runtime.signature)
    assert isinstance(coverage, CoversCertificate)
    assert verify_region_certificate(coverage, runtime.signature)
    vocabulary = function_vocabulary(runtime)
    claim = runtime_proposition(
        runtime,
        equal_on(
            vocabulary,
            old_domain.term,
            square(runtime),
            product(runtime),
        ),
    )
    certificate = FunctionEqualityCertificate(
        old_domain.term,
        left,
        impostor,
        0,
        1,
        coverage=coverage,
    )
    outcome = check_equality(runtime, claim, certificate)
    assert isinstance(outcome, InvalidEvidence)
    assert "does not match" in outcome.detail


def test_a_forged_coverage_certificate_is_revalidated(runtime):
    old_domain = nonnegative(runtime)
    left = function_value(runtime, old_domain)
    true = runtime_proposition(runtime, T.TRUE)
    right = left.extended(true, product(runtime), old_domain)
    region = function_region(right, true)
    piece = function_region(right, old_domain)
    forged = CoversCertificate(region, (piece, piece), "forged")
    assert coverage_matches_value(forged, right)
    assert not verify_region_certificate(forged, runtime.signature)
    vocabulary = function_vocabulary(runtime)
    claim = runtime_proposition(
        runtime,
        equal_on(
            vocabulary,
            old_domain.term,
            square(runtime),
            product(runtime),
        ),
    )
    certificate = FunctionEqualityCertificate(
        old_domain.term,
        left,
        right,
        0,
        1,
        coverage=forged,
    )
    outcome = check_equality(runtime, claim, certificate)
    assert isinstance(outcome, InvalidEvidence)
    assert "not proved" in outcome.detail


def test_same_partial_function_rejects_a_coverage_certificate(runtime):
    old_domain = nonnegative(runtime)
    left = function_value(runtime, old_domain)
    true = runtime_proposition(runtime, T.TRUE)
    right = left.extended(true, product(runtime), true)
    coverage = function_coverage_certificate(right, runtime.signature)
    assert isinstance(coverage, CoversCertificate)
    vocabulary = function_vocabulary(runtime)
    claim = runtime_proposition(
        runtime,
        same_partial_function(
            vocabulary, square(runtime), product(runtime)
        ),
    )
    certificate = FunctionEqualityCertificate(
        None, left, right, 0, 1, coverage=coverage
    )
    outcome = check_equality(runtime, claim, certificate)
    assert isinstance(outcome, InvalidEvidence)
    assert outcome.detail == (
        "a SamePartialFunction certificate does not carry a coverage claim"
    )


def test_function_coverage_helpers_validate_their_inputs(runtime):
    domain = nonnegative(runtime)
    value = function_value(runtime, domain)
    with pytest.raises(TypeError):
        function_region(value, T.TRUE)
    with pytest.raises(TypeError):
        function_region(T.TRUE, domain)
    with pytest.raises(TypeError):
        function_coverage_certificate(value, "signature")
    certificate = function_coverage_certificate(value, runtime.signature)
    assert isinstance(certificate, CoversCertificate)
    with pytest.raises(TypeError):
        coverage_matches_value("certificate", value)
    with pytest.raises(TypeError):
        coverage_matches_value(certificate, T.TRUE)
    with pytest.raises(TypeError):
        FunctionEqualityCertificate(
            domain.term, value, value, 0, 0, coverage="coverage"
        )


def test_function_region_with_an_unknown_extra_variable_is_not_dense(runtime):
    extra = runtime.table.intern("function_region_extra")
    frame = runtime.frames.create(
        runtime.frame.id,
        declarations=(
            Declaration(extra, "function_region_extra", S.REAL),
        ),
    )
    x = variable(runtime)
    domain = runtime_proposition(
        runtime,
        head_app(
            runtime.signature,
            StructuralHead.AND,
            head_app(
                runtime.signature, StructuralHead.GE, x, T.number(0)
            ),
            head_app(
                runtime.signature,
                StructuralHead.GT,
                T.symbol(extra, "function_region_extra"),
                T.number(0),
            ),
        ),
        frame=frame.id,
    )
    value = FunctionValue(
        (FunctionParameter(runtime.variable, S.REAL),),
        domain,
        S.REAL,
        (FunctionRepresentation(square(runtime), domain),),
    )
    region = function_region(value, domain)
    assert region.coordinates == (runtime.variable, extra)
    assert region.sorts == ()
    assert region.is_dense is False
    assert function_coverage_certificate(value, runtime.signature) is None


def test_function_region_records_parameter_binding_sorts(runtime):
    domain = nonnegative(runtime)
    value = function_value(runtime, domain)
    region = function_region(value, domain)
    assert region.coordinates == (runtime.variable,)
    assert region.sorts == ((runtime.variable, S.REAL),)
    assert region.is_dense


def _power(runtime, base, exponent):
    return head_app(
        runtime.signature, StructuralHead.POWER, base, T.number(exponent)
    )


def _ne(runtime, left):
    return head_app(
        runtime.signature, StructuralHead.NE, left, T.number(0)
    )


def _and(runtime, *terms):
    return head_app(runtime.signature, StructuralHead.AND, *terms)


def partial_condition(runtime):
    return runtime_proposition(
        runtime,
        head_app(
            runtime.signature,
            StructuralHead.GT,
            _power(runtime, variable(runtime), -1),
            T.number(0),
        ),
    )


def test_function_values_reject_partial_domain_and_representation_conditions(
    runtime,
):
    partial = partial_condition(runtime)
    assert partial.definedness
    total = nonnegative(runtime)
    with pytest.raises(ValueError):
        FunctionRepresentation(square(runtime), partial)
    with pytest.raises(ValueError):
        FunctionValue(
            (FunctionParameter(runtime.variable, S.REAL),),
            partial,
            S.REAL,
            (FunctionRepresentation(square(runtime), total),),
        )
    value = function_value(runtime, total)
    assert value.intrinsic_domain is total
    assert value.representations[0].valid_on is total


def test_equal_on_rejects_a_claimed_region_with_an_open_premise(runtime):
    true = runtime_proposition(runtime, T.TRUE)
    value = one_argument_value(runtime, square(runtime), true)
    partial = partial_condition(runtime)
    assert partial.definedness
    vocabulary = function_vocabulary(runtime)
    claim = runtime_proposition(
        runtime,
        equal_on(vocabulary, partial.term, square(runtime), square(runtime)),
    )
    certificate = FunctionEqualityCertificate(partial.term, value, value, 0, 0)
    outcome = check_equality(runtime, claim, certificate)
    assert isinstance(outcome, Unverified)
    assert outcome.reason is Reason.GUARDED
    assert "intrinsic domain" in outcome.detail


def test_equal_on_accepts_a_claimed_region_that_proves_its_premise(runtime):
    true = runtime_proposition(runtime, T.TRUE)
    value = one_argument_value(runtime, square(runtime), true)
    region = _and(
        runtime,
        head_app(
            runtime.signature,
            StructuralHead.GT,
            variable(runtime),
            T.number(0),
        ),
        partial_condition(runtime).term,
    )
    claimed = runtime_proposition(runtime, region)
    assert tuple(
        premise.term for premise in claimed.definedness
    ) == (_ne(runtime, variable(runtime)),)
    vocabulary = function_vocabulary(runtime)
    claim = runtime_proposition(
        runtime,
        equal_on(vocabulary, region, square(runtime), square(runtime)),
    )
    certificate = FunctionEqualityCertificate(region, value, value, 0, 0)
    outcome = check_equality(runtime, claim, certificate)
    assert isinstance(outcome, Verified)


def test_the_premise_aware_subregion_rule_accepts_a_proved_premise(runtime):
    true = runtime_proposition(runtime, T.TRUE)
    region = _and(
        runtime,
        head_app(
            runtime.signature,
            StructuralHead.GT,
            variable(runtime),
            T.number(0),
        ),
        partial_condition(runtime).term,
    )
    claimed = runtime_proposition(runtime, region)
    assert proved_subregion(claimed, true, runtime.signature) is True


def test_the_premise_aware_subregion_rule_rejects_an_open_premise(runtime):
    true = runtime_proposition(runtime, T.TRUE)
    partial = partial_condition(runtime)
    assert is_subregion(partial.term, T.TRUE, runtime.signature) is True
    assert proved_subregion(partial, true, runtime.signature) is not True


def test_extension_refuses_a_partial_new_domain_with_an_open_premise(runtime):
    workspace = new_workspace(runtime)
    domain = nonnegative(runtime)
    function = define(workspace, runtime, square(runtime), domain, "f")
    old_expression = workspace.expressions()[0]
    representation = workspace.intake(product(runtime), "extension")
    partial_domain = partial_condition(runtime)
    result = workspace.apply(
        "extend_function",
        (old_expression, representation),
        parameters=(
            (
                "extension",
                FunctionExtensionInput(
                    function.value, partial_domain, partial_domain
                ),
            ),
        ),
    )
    assert result.status is OperationStatus.INVALID
    assert "old domain" in result.detail
    assert workspace.functions() == (function,)


def test_extension_refuses_a_partial_new_representation_region(runtime):
    workspace = new_workspace(runtime)
    domain = nonnegative(runtime)
    function = define(workspace, runtime, square(runtime), domain, "f")
    old_expression = workspace.expressions()[0]
    representation = workspace.intake(product(runtime), "extension")
    partial = partial_condition(runtime)
    result = workspace.apply(
        "extend_function",
        (old_expression, representation),
        parameters=(
            (
                "extension",
                FunctionExtensionInput(function.value, domain, partial),
            ),
        ),
    )
    assert result.status is OperationStatus.INVALID
    assert "representation region" in result.detail
    assert workspace.functions() == (function,)


def function_problem(runtime, operation, values, region=None):
    return ProblemSpec(
        operation,
        tuple(
            typed_in(
                runtime.frames,
                runtime.frame.id,
                runtime.signature,
                value.representations[0].term,
            )
            for value in values
        ),
        VariableRoles(
            None, (), ParameterMode.SPECIFIED_VALUES, runtime.world.id
        ),
        region,
        (
            ResultLanguage.PROPOSITION
            if operation == "compare_functions"
            else ResultLanguage.EXPRESSION
        ),
        Coverage.ONE_VERIFIED,
        function_inputs=values,
        domain_requirement=DomainRequirement(
            coefficient=None, values=ValueDomain.REAL
        ),
    )


def validate_function_commit(
    runtime, claim, certificate, problem, *, algebra=None
):
    return validate_commit(
        runtime.store,
        CommitProposal(
            runtime.frame.id,
            (claim,),
            "functions.equality",
            problem.operation,
            "EqualOn",
            certificate=certificate,
            problem=problem,
            candidate=claim.term,
            candidate_role=CandidateRole.CONCLUSION,
            algebra=algebra,
        ),
    )


def test_validate_commit_rejects_a_function_proposal_with_algebra(runtime):
    domain = nonnegative(runtime)
    value = function_value(runtime, domain)
    claim = runtime_proposition(
        runtime,
        equal_on(
            function_vocabulary(runtime),
            domain.term,
            value.representations[0].term,
            value.representations[0].term,
        ),
    )
    certificate = FunctionEqualityCertificate(domain.term, value, value, 0, 0)
    problem = function_problem(runtime, "compare_functions", (value, value))
    result = validate_function_commit(
        runtime,
        claim,
        certificate,
        problem,
        algebra=runtime.request,
    )
    assert isinstance(result, Rejected)
    assert result.kind is RejectedKind.INVALID_EVIDENCE
    assert "no algebra request" in result.detail


def test_validate_commit_rejects_a_claim_region_not_covering_the_problem_region(
    runtime,
):
    region = runtime_proposition(runtime, _gt(runtime, 0))
    value = one_argument_value(runtime, square(runtime), region)
    claim = runtime_proposition(
        runtime,
        equal_on(
            function_vocabulary(runtime),
            _gt(runtime, 0),
            square(runtime),
            square(runtime),
        ),
    )
    certificate = FunctionEqualityCertificate(
        _gt(runtime, 0), value, value, 0, 0
    )
    problem = function_problem(
        runtime,
        "compare_functions",
        (value, value),
        region=runtime_proposition(
            runtime, _ne(runtime, variable(runtime))
        ),
    )
    result = validate_function_commit(runtime, claim, certificate, problem)
    assert isinstance(result, Rejected)
    assert not isinstance(result, ValidatedCommitBatch)
    assert "region" in result.detail


def test_validate_commit_accepts_a_claim_on_the_exact_problem_region(runtime):
    region_term = _gt(runtime, 0)
    region = runtime_proposition(runtime, region_term)
    value = one_argument_value(runtime, square(runtime), region)
    claim = runtime_proposition(
        runtime,
        equal_on(
            function_vocabulary(runtime),
            region_term,
            square(runtime),
            square(runtime),
        ),
    )
    certificate = FunctionEqualityCertificate(
        region_term, value, value, 0, 0
    )
    problem = function_problem(
        runtime, "compare_functions", (value, value), region=region
    )
    result = validate_function_commit(runtime, claim, certificate, problem)
    assert isinstance(result, ValidatedCommitBatch)


def test_a_certificate_function_value_must_match_the_problem_input(runtime):
    domain = runtime_proposition(runtime, T.TRUE)
    value = one_argument_value(runtime, square(runtime), domain)
    other_domain = runtime_proposition(runtime, _gt(runtime, 0))
    forged = one_argument_value(runtime, square(runtime), other_domain)
    claim = runtime_proposition(
        runtime,
        equal_on(
            function_vocabulary(runtime),
            T.TRUE,
            square(runtime),
            square(runtime),
        ),
    )
    certificate = FunctionEqualityCertificate(
        T.TRUE, forged, forged, 0, 0
    )
    problem = function_problem(runtime, "compare_functions", (value, value))
    checker = runtime.store.checkers.get("functions.equality")
    assert checker is not None
    outcome = checker.check(
        CheckRequest(
            runtime.frame.id,
            (claim,),
            (),
            certificate,
            problem=problem,
            candidate=claim.term,
            candidate_role=CandidateRole.CONCLUSION,
            context=verification_context(runtime),
        )
    )
    assert isinstance(outcome, InvalidEvidence)
    assert "function input" in outcome.detail


def test_a_representation_outside_its_intrinsic_domain_is_invalid_evidence(
    runtime,
):
    intrinsic = runtime_proposition(runtime, _gt(runtime, 0))
    outside = runtime_proposition(runtime, _lt(runtime, 0))
    forged = FunctionValue(
        (FunctionParameter(runtime.variable, S.REAL),),
        intrinsic,
        S.REAL,
        (FunctionRepresentation(square(runtime), outside),),
    )
    claim = runtime_proposition(
        runtime,
        equal_on(
            function_vocabulary(runtime),
            _gt(runtime, 0),
            square(runtime),
            square(runtime),
        ),
    )
    certificate = FunctionEqualityCertificate(
        _gt(runtime, 0), forged, forged, 0, 0
    )
    outcome = check_equality(runtime, claim, certificate)
    assert isinstance(outcome, InvalidEvidence)
    assert "outside its intrinsic domain" in outcome.detail


def test_integer_parameter_function_equality_is_unverified(runtime):
    domain = runtime_proposition(runtime, T.TRUE)
    value = FunctionValue(
        (FunctionParameter(runtime.variable, S.INTEGER),),
        domain,
        S.REAL,
        (FunctionRepresentation(square(runtime), domain),),
    )
    claim = runtime_proposition(
        runtime,
        equal_on(
            function_vocabulary(runtime),
            T.TRUE,
            square(runtime),
            square(runtime),
        ),
    )
    certificate = FunctionEqualityCertificate(T.TRUE, value, value, 0, 0)
    outcome = check_equality(runtime, claim, certificate)
    assert isinstance(outcome, Unverified)
    assert outcome.reason is Reason.GUARDED
    assert "non-dense" in outcome.detail


def test_equal_on_rejects_a_region_variable_that_is_not_a_parameter(runtime):
    y = runtime.table.intern("function_region_y")
    child = runtime.frames.create(
        runtime.frame.id,
        declarations=(Declaration(y, "function_region_y", S.REAL),),
    )
    domain = runtime_proposition(runtime, T.TRUE)
    value = one_argument_value(runtime, square(runtime), domain)
    region = head_app(
        runtime.signature,
        StructuralHead.GT,
        T.symbol(y, "function_region_y"),
        T.number(0),
    )
    claim = runtime_proposition(
        runtime,
        equal_on(
            function_vocabulary(runtime),
            region,
            square(runtime),
            square(runtime),
        ),
        child.id,
    )
    certificate = FunctionEqualityCertificate(region, value, value, 0, 0)
    checker = runtime.store.checkers.get("functions.equality")
    assert checker is not None
    outcome = checker.check(
        CheckRequest(
            child.id,
            (claim,),
            (),
            certificate,
            candidate=claim.term,
            candidate_role=CandidateRole.CONCLUSION,
            context=verification_context(runtime, child.id),
        )
    )
    assert isinstance(outcome, Unverified)
    assert outcome.reason is Reason.FRAGMENT
    assert "not function parameters" in outcome.detail


def test_same_partial_function_rejects_a_problem_region_outside_the_domain(
    runtime,
):
    domain = runtime_proposition(runtime, _gt(runtime, 0))
    value = one_argument_value(runtime, square(runtime), domain)
    claim = runtime_proposition(
        runtime,
        same_partial_function(
            function_vocabulary(runtime), square(runtime), square(runtime)
        ),
    )
    certificate = FunctionEqualityCertificate(None, value, value, 0, 0)
    problem = function_problem(
        runtime,
        "compare_functions",
        (value, value),
        region=runtime_proposition(runtime, _lt(runtime, 0)),
    )
    checker = runtime.store.checkers.get("functions.equality")
    assert checker is not None
    outcome = checker.check(
        CheckRequest(
            runtime.frame.id,
            (claim,),
            (),
            certificate,
            problem=problem,
            candidate=claim.term,
            candidate_role=CandidateRole.CONCLUSION,
            context=verification_context(runtime),
        )
    )
    assert isinstance(outcome, InvalidEvidence)
    assert "complete domain" in outcome.detail
