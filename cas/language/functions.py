"""Explicit partial function values.

A neutral expression is a formula; it does not by itself carry an intrinsic
domain.  A `FunctionValue` is the object that does: it fixes the parameter
bindings, the intrinsic domain on which the function has a value, its result
sort, and one or more representations with the region on which each represents
the function.

The representation region is deliberately separate from the intrinsic domain.
A representation may be valid on a proper subregion, and a relation proved on a
region never enlarges the function's intrinsic domain.  The workspace records
the object; a later derivative relation is a separate object and keeps its own
region.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import StrEnum

from cas.foundation.ids import SymbolId
from cas.language.propositions import Proposition
from cas.language.sorts import Sort
from cas.syntax import binding as B
from cas.syntax import term as T


@dataclass(frozen=True, slots=True)
class FunctionParameter:
    """One formal parameter of a function value."""

    symbol: SymbolId
    sort: Sort

    def __post_init__(self) -> None:
        if isinstance(self.symbol, bool) or not isinstance(self.symbol, int):
            raise TypeError("a function parameter needs a SymbolId")
        if not isinstance(self.sort, Sort):
            raise TypeError("a function parameter needs a sort")


@dataclass(frozen=True, slots=True)
class FunctionRepresentation:
    """One expression/representation and the region on which it is valid."""

    term: T.Term
    valid_on: Proposition

    def __post_init__(self) -> None:
        if not isinstance(self.term, T.Term):
            raise TypeError("a function representation carries a term")
        if not isinstance(self.valid_on, Proposition):
            raise TypeError(
                "a function representation needs a validity proposition"
            )
        if self.valid_on.definedness:
            raise ValueError(
                "a function representation region must be a total condition; "
                "this batch's workspace and checker consumers compare region "
                "terms and do not account for definedness premises"
            )


class FunctionEquality(StrEnum):
    """A conservative answer to partial-function equality.

    `SAME` has a structural proof.  `DIFFERENT` is used only when the
    parameter count, parameter sorts or result sort differ.  Two different
    representations of the same function, or a different parameter identity,
    are `UNKNOWN`, because alpha-equivalence and equality of formulas are not
    decided here.
    """

    SAME = "same"
    DIFFERENT = "different"
    UNKNOWN = "unknown"


@dataclass(frozen=True, slots=True)
class FunctionApplication:
    """One representation after substituting actual arguments.

    `valid_on` is the substituted representation region.  It is still a term,
    not a proposition: the caller must re-elaborate it in the target frame before
    using it as a condition.
    """

    arguments: tuple[T.Term, ...]
    representation_index: int
    term: T.Term
    valid_on: T.Term

    def __post_init__(self) -> None:
        if not self.arguments:
            raise ValueError("a function application needs arguments")
        if any(not isinstance(argument, T.Term) for argument in self.arguments):
            raise TypeError("function arguments must be terms")
        if self.representation_index < 0:
            raise ValueError("a representation index cannot be negative")
        if not isinstance(self.term, T.Term):
            raise TypeError("a function application needs a term")
        if not isinstance(self.valid_on, T.Term):
            raise TypeError("a function application needs a region term")


@dataclass(frozen=True, slots=True)
class FunctionValue:
    """A partial function with its binding, intrinsic domain and values.

    `parameters` are the formal arguments.  `intrinsic_domain` is part of the
    function's identity: a representation valid outside it would describe a
    different function.  Every representation states its own `valid_on`
    subregion.

    Both the intrinsic domain and every representation region are total
    conditions in this batch.  The workspace's domain checks, the equality
    checker and the coverage helper read their terms; a partial condition would
    have its definedness premises silently ignored.  They move to `RegionSpec`
    only together with those consumers.
    """

    parameters: tuple[FunctionParameter, ...]
    intrinsic_domain: Proposition
    result_sort: Sort
    representations: tuple[FunctionRepresentation, ...]

    def __post_init__(self) -> None:
        parameters = tuple(self.parameters)
        representations = tuple(self.representations)
        if not parameters:
            raise ValueError("a function value needs at least one parameter")
        if len({parameter.symbol for parameter in parameters}) != len(
            parameters
        ):
            raise ValueError("function parameters must be distinct")
        if not isinstance(self.intrinsic_domain, Proposition):
            raise TypeError("a function value needs an intrinsic domain")
        if self.intrinsic_domain.definedness:
            raise ValueError(
                "a function intrinsic domain must be a total condition; this "
                "batch's workspace and checker consumers compare region terms "
                "and do not account for definedness premises"
            )
        if not isinstance(self.result_sort, Sort):
            raise TypeError("a function value needs a result sort")
        if not representations:
            raise ValueError("a function value needs a representation")
        if any(
            not isinstance(representation, FunctionRepresentation)
            for representation in representations
        ):
            raise TypeError(
                "function representations must be FunctionRepresentation values"
            )
        seen: list[FunctionRepresentation] = []
        for representation in representations:
            if representation in seen:
                raise ValueError(
                    "function representations must be distinct; a repeated "
                    "term/region pair does not describe another representation"
                )
            seen.append(representation)
        object.__setattr__(self, "parameters", parameters)
        object.__setattr__(self, "representations", representations)

    @property
    def parameter_symbols(self) -> tuple[SymbolId, ...]:
        return tuple(parameter.symbol for parameter in self.parameters)

    def applications(
        self,
        arguments: tuple[T.Term, ...],
    ) -> tuple[FunctionApplication, ...]:
        """Substitute actual arguments into every representation.

        This is a syntactic operation.  It does not prove that the arguments
        satisfy the intrinsic domain or that a representation is valid at the
        resulting point; those are separate obligations for the caller.
        """
        if len(arguments) != len(self.parameters):
            raise ValueError(
                f"expected {len(self.parameters)} arguments, "
                f"got {len(arguments)}"
            )
        mapping = {
            parameter.symbol: argument
            for parameter, argument in zip(self.parameters, arguments)
        }
        return tuple(
            FunctionApplication(
                arguments,
                index,
                B.substitute_free(representation.term, mapping),
                B.substitute_free(representation.valid_on.term, mapping),
            )
            for index, representation in enumerate(self.representations)
        )

    def with_representation(
        self,
        term: T.Term,
        valid_on: Proposition,
    ) -> FunctionValue:
        """Add a representation without claiming it agrees with the others."""
        return FunctionValue(
            self.parameters,
            self.intrinsic_domain,
            self.result_sort,
            self.representations + (FunctionRepresentation(term, valid_on),),
        )

    def extended(
        self,
        domain: Proposition,
        term: T.Term,
        valid_on: Proposition,
    ) -> FunctionValue:
        """Add one representation and state a (possibly larger) domain.

        The caller is responsible for proving that the new representation
        agrees with the old function on the old domain; this method only builds
        the data value.
        """
        return FunctionValue(
            self.parameters,
            domain,
            self.result_sort,
            self.representations + (FunctionRepresentation(term, valid_on),),
        )

    def representation_index_of(self, term: T.Term) -> int | None:
        """The first representation with this exact term, if any."""
        for index, representation in enumerate(self.representations):
            if representation.term == term:
                return index
        return None

    def same_partial_function(self, other: FunctionValue) -> FunctionEquality:
        """Compare two partial functions conservatively.

        Different arities or parameter sorts are different signatures.  A
        different intrinsic-domain proposition (its meaning key included) or a
        different parameter identity is `UNKNOWN`: alpha-equivalence and
        logical equivalence are not decided here.  `SAME` requires an identical
        intrinsic domain and the same multiset of representations, compared by
        term and validity proposition.
        """
        if not same_parameter_shape(self, other):
            return FunctionEquality.DIFFERENT
        if self.parameter_symbols != other.parameter_symbols:
            return FunctionEquality.UNKNOWN
        if self.intrinsic_domain != other.intrinsic_domain:
            return FunctionEquality.UNKNOWN
        if not same_representation_multiset(self, other):
            return FunctionEquality.UNKNOWN
        return FunctionEquality.SAME

    def equal_on(
        self,
        region: Proposition,
        other: FunctionValue,
    ) -> FunctionEquality:
        """Compare two functions on a region by exact representation identity.

        A structural match proves equality on every subregion.  A signature
        mismatch is `DIFFERENT`; a different parameter identity or a
        representation mismatch is `UNKNOWN`, never `DIFFERENT`: two different
        formulas can agree on a nontrivial region, and this layer does not run
        an algebraic identity checker.
        """
        if not same_parameter_shape(self, other):
            return FunctionEquality.DIFFERENT
        if self.parameter_symbols != other.parameter_symbols:
            return FunctionEquality.UNKNOWN
        for left in self.representations:
            for right in other.representations:
                if left.term == right.term:
                    return FunctionEquality.SAME
        return FunctionEquality.UNKNOWN


def same_parameter_shape(
    left: FunctionValue,
    right: FunctionValue,
) -> bool:
    """Whether two function values agree on arity, parameter sorts and result.

    The parameter symbols are not part of this shape comparison; a caller that
    needs the full signature must also compare `parameter_symbols`.  This is
    what lets the equality checker separate a refutable signature mismatch from
    undecided alpha-equivalence.
    """
    if len(left.parameters) != len(right.parameters):
        return False
    if left.result_sort != right.result_sort:
        return False
    return all(
        first.sort == second.sort
        for first, second in zip(left.parameters, right.parameters)
    )


def same_representation_multiset(
    left: FunctionValue,
    right: FunctionValue,
) -> bool:
    """Whether two values carry the same representations with multiplicity.

    `FunctionRepresentation` equality compares the term and the validity
    proposition, including its meaning key.  A one-way containment check would
    accept `[x^2, x^2]` against `[x^2, x]`; matching by removal rejects it.
    """
    if len(left.representations) != len(right.representations):
        return False
    remaining = list(right.representations)
    for representation in left.representations:
        try:
            remaining.remove(representation)
        except ValueError:
            return False
    return not remaining


def same_parameter_signature(
    left: FunctionValue,
    right: FunctionValue,
) -> bool:
    """Whether two function values have the same parameter signature.

    The signature is the parameter count, each parameter's symbol and sort, and
    the result sort.  Parameter symbols are part of the signature: this layer
    does not decide alpha-equivalence of function bindings.
    """
    return (
        same_parameter_shape(left, right)
        and left.parameter_symbols == right.parameter_symbols
    )


__all__ = [
    "FunctionApplication",
    "FunctionEquality",
    "FunctionParameter",
    "FunctionRepresentation",
    "FunctionValue",
    "same_parameter_shape",
    "same_parameter_signature",
    "same_representation_multiset",
]
