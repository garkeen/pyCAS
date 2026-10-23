"""Binding: the only place that manipulates de Bruijn indices.

Every operation here is structural and capture-safe. None of them descends into
`Quote`, whose content is held syntax data rather than a term in the current
context.

Conventions:

- `BoundVar(0)` names the innermost bound variable; enclosing binders increase
  the index.
- A `Binder` introduces `arity` variables at once, so entering its body raises
  the binder depth by `arity`. Its annotations are evaluated at the *outer*
  depth and therefore never see the bound variables.
- `instantiate` removes a binder whose arguments live in the binder's own
  context; an inserted argument is shifted by the number of nested binders
  crossed at the insertion site, so its outer references stay outside the body.
"""

from __future__ import annotations

from collections.abc import Mapping

from cas.foundation.ids import SymbolId
from cas.syntax import term as T


def _rebuild_apply(
    original: T.Apply,
    operator: T.Term,
    arguments: tuple[T.Term, ...],
) -> T.Term:
    if operator is original.operator and all(
        new is old for new, old in zip(arguments, original.arguments)
    ):
        return original
    return T.Apply(operator, arguments)


def _rebuild_binder(
    original: T.Binder,
    body: T.Term,
    annotations: tuple[T.Term, ...],
) -> T.Term:
    if body is original.body and all(
        new is old for new, old in zip(annotations, original.annotations)
    ):
        return original
    return T.Binder(
        original.signature,
        original.arity,
        body,
        annotations,
        original.hint,
    )


def shift(term: T.Term, delta: int, cutoff: int = 0) -> T.Term:
    """Move free-by-index variables at or beyond `cutoff` by `delta`."""
    if delta == 0:
        return term
    if isinstance(term, T.BoundVar):
        if term.index < cutoff:
            return term
        moved = term.index + delta
        if moved < 0:
            raise ValueError("shift produced a negative de Bruijn index")
        return term if moved == term.index else T.BoundVar(moved)
    if isinstance(term, T.Apply):
        operator = shift(term.operator, delta, cutoff)
        arguments = tuple(
            shift(argument, delta, cutoff) for argument in term.arguments
        )
        return _rebuild_apply(term, operator, arguments)
    if isinstance(term, T.Binder):
        body = shift(term.body, delta, cutoff + term.arity)
        annotations = tuple(
            shift(annotation, delta, cutoff) for annotation in term.annotations
        )
        return _rebuild_binder(term, body, annotations)
    return term


def instantiate(binder: T.Binder, arguments: tuple[T.Term, ...]) -> T.Term:
    """Remove `binder` and replace its variables by `arguments`.

    `arguments` live in the context of the binder itself. At a site under `local`
    nested binders inside the body, the removed variables are indexed
    `local … local+arity-1`, and an inserted argument must be shifted by `local`
    so that its outer references still point outside the body.
    """
    if len(arguments) != binder.arity:
        raise ValueError(
            f"binder introduces {binder.arity} variables, "
            f"got {len(arguments)} arguments"
        )
    arity = binder.arity

    def walk(current: T.Term, local: int) -> T.Term:
        if isinstance(current, T.BoundVar):
            if current.index < local:
                return current
            offset = current.index - local
            if offset < arity:
                return shift(arguments[offset], local)
            return T.BoundVar(current.index - arity)
        if isinstance(current, T.Apply):
            operator = walk(current.operator, local)
            values = tuple(walk(argument, local) for argument in current.arguments)
            return _rebuild_apply(current, operator, values)
        if isinstance(current, T.Binder):
            body = walk(current.body, local + current.arity)
            annotations = tuple(
                walk(annotation, local) for annotation in current.annotations
            )
            return _rebuild_binder(current, body, annotations)
        return current

    return walk(binder.body, 0)


def abstract(
    term: T.Term,
    symbols: tuple[SymbolId, ...],
    depth: int = 0,
) -> T.Term:
    """Bind the listed free symbols as the variables of the enclosing binder.

    The position of a symbol in `symbols` decides its index, so the caller fixes
    the order explicitly.
    """
    if not symbols:
        return term
    positions = {symbol: position for position, symbol in enumerate(symbols)}

    def walk(current: T.Term, local: int) -> T.Term:
        if isinstance(current, T.SymbolRef):
            position = positions.get(current.symbol_id)
            return current if position is None else T.BoundVar(local + position)
        if isinstance(current, T.Apply):
            operator = walk(current.operator, local)
            arguments = tuple(walk(argument, local) for argument in current.arguments)
            return _rebuild_apply(current, operator, arguments)
        if isinstance(current, T.Binder):
            body = walk(current.body, local + current.arity)
            annotations = tuple(
                walk(annotation, local) for annotation in current.annotations
            )
            return _rebuild_binder(current, body, annotations)
        return current

    return walk(term, depth)


def substitute_free(
    term: T.Term,
    mapping: Mapping[SymbolId, T.Term],
) -> T.Term:
    """Simultaneously replace free symbols; inserted terms are not revisited.

    An inserted term lives in the outer context, so at binder depth `depth` it
    is shifted by `depth` before insertion. Without that shift a replacement
    mentioning an outer bound variable would be captured by an inner binder.
    """
    if not mapping:
        return term

    def walk(current: T.Term, depth: int) -> T.Term:
        if isinstance(current, T.SymbolRef):
            replacement = mapping.get(current.symbol_id)
            return current if replacement is None else shift(replacement, depth)
        if isinstance(current, T.Apply):
            operator = walk(current.operator, depth)
            arguments = tuple(walk(argument, depth) for argument in current.arguments)
            return _rebuild_apply(current, operator, arguments)
        if isinstance(current, T.Binder):
            body = walk(current.body, depth + current.arity)
            annotations = tuple(
                walk(annotation, depth) for annotation in current.annotations
            )
            return _rebuild_binder(current, body, annotations)
        return current

    return walk(term, 0)


def free_symbols(term: T.Term) -> frozenset[SymbolId]:
    """Free symbols in operator, argument and annotation positions.

    Quoted content contributes nothing: it is data, not a term of this context.
    """
    found: set[SymbolId] = set()
    stack: list[T.Term] = [term]
    while stack:
        current = stack.pop()
        if isinstance(current, T.SymbolRef):
            found.add(current.symbol_id)
        elif isinstance(current, T.Apply):
            stack.append(current.operator)
            stack.extend(current.arguments)
        elif isinstance(current, T.Binder):
            stack.extend(current.annotations)
            stack.append(current.body)
    return frozenset(found)


def well_scoped(term: T.Term, depth: int = 0) -> bool:
    """Whether every bound index names an enclosing binder."""
    stack: list[tuple[T.Term, int]] = [(term, depth)]
    while stack:
        current, local = stack.pop()
        if isinstance(current, T.BoundVar):
            if current.index >= local:
                return False
        elif isinstance(current, T.Apply):
            stack.append((current.operator, local))
            stack.extend((argument, local) for argument in current.arguments)
        elif isinstance(current, T.Binder):
            stack.extend((annotation, local) for annotation in current.annotations)
            stack.append((current.body, local + current.arity))
    return True


__all__ = [
    "abstract",
    "free_symbols",
    "instantiate",
    "shift",
    "substitute_free",
    "well_scoped",
]
