"""Problem specifications: what is being computed, and to what standard.

A problem is not a command and not a belief. It fixes the inputs, the target,
the region, the result language, the parameter promise and the coverage
demanded of an answer. Budget and execution attempts are not part of it.

Operation-specific parameters (for example an integration method or an
elimination order) belong to the operation's own spec record; they are added
with that operation rather than guessed here.

An `AlgebraRequest` owns the algebra view: coefficient and parameter parents,
symbol roles and interpretation. The `target` and `parameter_mode` fields here
mirror that view; an operation derives them from its fixed request and never
chooses them independently.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import StrEnum

from cas.foundation.ids import SymbolId
from cas.language.propositions import Proposition
from cas.syntax import term as T


class ParameterMode(StrEnum):
    """What a result may assume about parameters."""

    SPECIFIED_VALUES = "specified_values"
    GENERIC_PARAMETERS = "generic_parameters"
    ALL_PARAMETER_VALUES = "all_parameter_values"


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


@dataclass(frozen=True, slots=True)
class ProblemSpec:
    """A fixed problem statement.

    `externalizable` lists premises the request explicitly allows to remain
    outside the answer. A complete-set request may not externalize anything:
    an unhandled case cannot be moved into an external obligation.
    """

    operation: str
    inputs: tuple[T.Term, ...]
    target: SymbolId | None
    region: Proposition | None
    result_language: ResultLanguage
    parameter_mode: ParameterMode
    coverage: Coverage
    externalizable: tuple[Proposition, ...] = ()

    def __post_init__(self) -> None:
        if not self.operation:
            raise ValueError("a problem needs an operation identifier")
        if not self.inputs:
            raise ValueError("a problem needs at least one input")
        if any(not isinstance(item, T.Term) for item in self.inputs):
            raise TypeError("problem inputs must be terms")
        if self.region is not None and not isinstance(
            self.region, Proposition
        ):
            raise TypeError("a problem region must be a proposition")
        if not isinstance(self.result_language, ResultLanguage):
            raise TypeError("a problem needs a result language")
        if not isinstance(self.parameter_mode, ParameterMode):
            raise TypeError("a problem needs a parameter mode")
        if not isinstance(self.coverage, Coverage):
            raise TypeError("a problem needs a coverage requirement")
        if any(
            not isinstance(item, Proposition)
            for item in self.externalizable
        ):
            raise TypeError("externalizable premises must be propositions")
        if self.externalizable and self.coverage is Coverage.COMPLETE_SET:
            raise ValueError(
                "a complete-set request cannot externalize premises: "
                "unhandled cases would masquerade as coverage"
            )

    def allows_unresolved(self) -> bool:
        """Whether the request accepts an answer with open premises."""
        return bool(self.externalizable)


__all__ = [
    "Coverage",
    "ParameterMode",
    "ProblemSpec",
    "ResultLanguage",
]
