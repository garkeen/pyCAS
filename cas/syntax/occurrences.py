"""Structural occurrence paths and capture-safe replacement.

A path is a tuple of child indices:

- on `Apply`, `0` is the operator and `1..n` are the arguments;
- on `Binder`, `0` is the body and `1..n` are the annotations;
- `Quote` is held syntax data and is never traversed.

Replacing under binders shifts the replacement by the number of crossed bound
variables, so free variables in the replacement keep their outer meaning.
"""

from __future__ import annotations

from dataclasses import dataclass

from cas.syntax import binding as B
from cas.syntax import term as T


@dataclass(frozen=True, slots=True)
class Occurrence:
    """One structural position in a term.

    `expected` is the subterm the caller saw at that path when the occurrence
    was selected.  A rewrite refuses a stale occurrence whose path no longer
    holds that subterm, so a path alone cannot be used against another source.
    """

    path: tuple[int, ...]
    expected: T.Term | None = None

    def __post_init__(self) -> None:
        if any(
            isinstance(index, bool) or not isinstance(index, int) or index < 0
            for index in self.path
        ):
            raise ValueError("an occurrence path needs nonnegative indices")
        if self.expected is not None and not isinstance(
            self.expected, T.Term
        ):
            raise TypeError("an occurrence expectation must be a term or None")


def subterm_at(term: T.Term, path: tuple[int, ...]) -> T.Term | None:
    """The subterm at `path`, or None when the path does not exist."""
    current = term
    for index in path:
        if isinstance(current, T.Apply):
            if index == 0:
                current = current.operator
            elif 1 <= index <= len(current.arguments):
                current = current.arguments[index - 1]
            else:
                return None
        elif isinstance(current, T.Binder):
            if index == 0:
                current = current.body
            elif 1 <= index <= len(current.annotations):
                current = current.annotations[index - 1]
            else:
                return None
        else:
            return None
    return current


def occurrences(
    term: T.Term,
    target: T.Term,
) -> tuple[Occurrence, ...]:
    """All structural positions whose subterm equals `target`."""
    found: list[Occurrence] = []

    def walk(current: T.Term, path: tuple[int, ...]) -> None:
        if current == target:
            found.append(Occurrence(path, current))
        if isinstance(current, T.Apply):
            walk(current.operator, path + (0,))
            for index, argument in enumerate(current.arguments):
                walk(argument, path + (index + 1,))
        elif isinstance(current, T.Binder):
            walk(current.body, path + (0,))
            for index, annotation in enumerate(current.annotations):
                walk(annotation, path + (index + 1,))

    walk(term, ())
    return tuple(found)


def replace_at(
    term: T.Term,
    path: tuple[int, ...],
    replacement: T.Term,
) -> T.Term:
    """Replace the subterm at `path`, shifting under binders.

    Raises `IndexError` when the path does not exist.  The replacement is
    written in the outer context; crossing a binder shifts its free bound
    variables so they keep referring outside the binder.
    """
    if not path:
        return replacement
    return _replace(term, path, replacement, 0)


def _replace(
    term: T.Term,
    path: tuple[int, ...],
    replacement: T.Term,
    depth: int,
) -> T.Term:
    if not path:
        return _shifted(replacement, depth)
    head, rest = path[0], path[1:]
    if isinstance(term, T.Apply):
        if head == 0:
            operator = _replace(term.operator, rest, replacement, depth)
            return T.app(operator, *term.arguments)
        index = head - 1
        if not 0 <= index < len(term.arguments):
            raise IndexError("occurrence path is outside the term")
        arguments = list(term.arguments)
        arguments[index] = _replace(
            arguments[index], rest, replacement, depth
        )
        return T.app(term.operator, *arguments)
    if isinstance(term, T.Binder):
        if head == 0:
            body = _replace(
                term.body,
                rest,
                replacement,
                depth + term.arity,
            )
            return T.binder(
                term.signature,
                term.arity,
                body,
                *term.annotations,
                hint=term.hint,
            )
        index = head - 1
        if not 0 <= index < len(term.annotations):
            raise IndexError("occurrence path is outside the term")
        annotations = list(term.annotations)
        annotations[index] = _replace(
            annotations[index], rest, replacement, depth
        )
        return T.binder(
            term.signature,
            term.arity,
            term.body,
            *annotations,
            hint=term.hint,
        )
    raise IndexError("occurrence path descends into an atomic term")


def _shifted(term: T.Term, depth: int) -> T.Term:
    return term if depth == 0 else B.shift(term, depth, 0)


__all__ = [
    "Occurrence",
    "occurrences",
    "replace_at",
    "subterm_at",
]
