"""Explicit-stack term traversal, substitution, and path rewriting."""

from __future__ import annotations

from collections.abc import Iterator, Mapping
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from cas.syntax.term import Sym, Term


def subst_raw(term: Term, mapping: Mapping[Term, Term]) -> Term:
    """Structural substitution preserving held Quote structure."""
    from cas.syntax import term as T

    if not mapping:
        return term
    order: list[Term] = []
    stack = [term]
    while stack:
        current = stack.pop()
        order.append(current)
        if isinstance(current, T.Expr):
            if current in mapping:
                continue
            stack.extend(current.args)
        elif isinstance(current, T.Bound):
            stack.append(current.body)
    values: dict[Term, Term] = {}
    for current in reversed(order):
        replacement = mapping.get(current)
        if replacement is not None:
            values[current] = replacement
        elif isinstance(current, T.Expr):
            values[current] = T.intern_expr(
                current.head, tuple(values[argument] for argument in current.args))
        elif isinstance(current, T.Bound):
            values[current] = T.mk_bound_canon(
                current.hint, values[current.body])
        else:
            values[current] = current
    return values[term]


def subst(term: Term, mapping: Mapping[Term, Term]) -> Term:
    """One-pass structural substitution with canonical reconstruction."""
    from cas.syntax import term as T

    if not mapping:
        return term
    order: list[Term] = []
    stack = [term]
    while stack:
        current = stack.pop()
        order.append(current)
        if isinstance(current, T.Expr):
            if current in mapping or current.head.name == "Quote":
                continue
            stack.extend(current.args)
        elif isinstance(current, T.Bound):
            stack.append(current.body)
    values: dict[Term, Term] = {}
    for current in reversed(order):
        replacement = mapping.get(current)
        if replacement is not None:
            values[current] = replacement
        elif isinstance(current, T.Expr):
            if current.head.name == "Quote":
                values[current] = T.intern_expr(
                    current.head,
                    tuple(subst_raw(argument, mapping) for argument in current.args),
                )
            else:
                values[current] = T.mk(
                    current.head,
                    tuple(values[argument] for argument in current.args),
                )
        elif isinstance(current, T.Bound):
            values[current] = T.mk_bound_canon(
                current.hint, values[current.body])
        else:
            values[current] = current
    return values[term]


def free_vars(term: Term, accumulator: set[Sym] | None = None) -> set[Sym]:
    """Return the term's free symbols."""
    from cas.syntax import term as T

    result = set() if accumulator is None else accumulator
    if isinstance(term, T.Sym):
        result.add(term)
    elif isinstance(term, T.Expr):
        for argument in term.args:
            free_vars(argument, result)
    elif isinstance(term, T.Bound):
        free_vars(term.body, result)
    return result




def instantiate_de_bruijn(
    template: Term,
    replacement: Term,
    depth: int = 0,
) -> Term:
    """Instantiate one de Bruijn placeholder with an arbitrary syntax term."""
    from cas.syntax import term as T

    if isinstance(template, T.DB):
        return replacement if template.i == depth else template
    if isinstance(template, T.Expr):
        arguments = tuple(
            instantiate_de_bruijn(argument, replacement, depth)
            for argument in template.args
        )
        return (
            template
            if all(new is old for new, old in zip(arguments, template.args))
            else T.mk(template.head, arguments)
        )
    if isinstance(template, T.Bound):
        body = instantiate_de_bruijn(template.body, replacement, depth + 1)
        return (
            template
            if body is template.body
            else T.mk_bound_canon(template.hint, body)
        )
    return template
def term_at(term: Term, path: tuple[int, ...]) -> Term:
    """Return the subterm at an explicit argument path."""
    from cas.syntax import term as T

    current = term
    for index in path:
        if isinstance(current, T.Expr):
            current = current.args[index]
        elif isinstance(current, T.Bound):
            current = T.lift(current.body, T.S(current.hint), 0)
        else:
            raise IndexError(path)
    return current


def _bind_into(term: Term, variable: Sym, depth: int = 0) -> Term:
    """Abstract only the free ``variable`` without shifting existing DB indices."""
    from cas.syntax import term as T

    if isinstance(term, T.Sym):
        return T.DB_(depth) if term is variable else term
    if isinstance(term, T.Expr):
        return T.mk(
            term.head,
            tuple(_bind_into(argument, variable, depth) for argument in term.args),
        )
    if isinstance(term, T.Bound):
        return T.mk_bound_canon(
            term.hint, _bind_into(term.body, variable, depth + 1))
    return term


def replace_at(term: Term, path: tuple[int, ...], replacement: Term) -> Term:
    """Replace the subterm at ``path``, preserving binder hygiene."""
    from cas.syntax import term as T

    if not path:
        return replacement
    index = path[0]
    if isinstance(term, T.Expr):
        arguments = list(term.args)
        arguments[index] = replace_at(arguments[index], path[1:], replacement)
        return T.mk(term.head, tuple(arguments))
    if isinstance(term, T.Bound):
        variable = T.S(term.hint)
        inner = replace_at(
            T.lift(term.body, variable, 0), path[1:], replacement)
        return T.mk_bound_canon(term.hint, _bind_into(inner, variable, 0))
    raise IndexError(path)


def all_paths(
    term: Term,
    base: tuple[int, ...] = (),
) -> Iterator[tuple[int, ...]]:
    """Yield every explicit path in deterministic preorder."""
    from cas.syntax import term as T

    yield base
    if isinstance(term, T.Expr):
        for index, argument in enumerate(term.args):
            yield from all_paths(argument, base + (index,))
    elif isinstance(term, T.Bound):
        yield from all_paths(term.body, base + (0,))


def postorder(term: Term) -> list[Term]:
    """Return all nodes in explicit-stack postorder."""
    from cas.syntax import term as T

    order: list[Term] = []
    stack = [term]
    while stack:
        current = stack.pop()
        order.append(current)
        if isinstance(current, T.Expr):
            stack.extend(current.args)
        elif isinstance(current, T.Bound):
            stack.append(current.body)
    return order
