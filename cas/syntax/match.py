"""Pattern matching over the pattern metalanguage.

A pattern is matched against a term through this module only. Pattern variables
therefore never enter the term layer, and every binding is represented by the
same named substitution value type used by rule instantiation.
"""

from __future__ import annotations

from collections.abc import Callable, Iterator, Mapping
from typing import TypeAlias

from cas.errors import BudgetExceeded
from cas.syntax import pattern as P
from cas.syntax import term as T

SubstitutionValue: TypeAlias = T.Term | tuple[T.Term, ...]
Substitution: TypeAlias = dict[str, SubstitutionValue]
PatternPredicate: TypeAlias = Callable[[T.Term], bool]

_PREDS: Mapping[str, PatternPredicate] = {
    "num": lambda term: T.is_num(term),
    "int": lambda term: isinstance(term, T.Int),
    "rat": lambda term: isinstance(term, T.Rat),
    "sym": lambda term: isinstance(term, T.Sym),
    "const": lambda term: isinstance(term, T.Const) or T.is_num(term),
    "expr": lambda term: isinstance(term, T.Expr),
}


def _pred_ok(pattern: P.PatternVar, target: T.Term) -> bool:
    if pattern.pred is None:
        return True
    predicate = _PREDS.get(pattern.pred)
    return predicate is not None and predicate(target)


# OneIdentity: an AC head with an identity element also matches a bare term.
_ONE_ID: dict[str, T.Term] = {}


def _one_identity() -> Mapping[str, T.Term]:
    if not _ONE_ID:
        _ONE_ID.update({"Plus": T.ZERO, "Times": T.ONE})
    return _ONE_ID


def identity_element(head_name: str) -> T.Term | None:
    """Return the identity element absorbed by ``head_name`` when declared."""
    return _one_identity().get(head_name)


def _bind_identity(
    pattern: P.PatternLike,
    identity: T.Term,
    substitution: Substitution,
) -> Substitution | None:
    if isinstance(pattern, P.PatternVar):
        if not _pred_ok(pattern, identity):
            return None
        current = substitution.get(pattern.name)
        if current is None:
            result = dict(substitution)
            result[pattern.name] = identity
            return result
        return substitution if current is identity else None
    if isinstance(pattern, P.PatternSeq):
        current = substitution.get(pattern.name)
        if current is None:
            result = dict(substitution)
            result[pattern.name] = ()
            return result
        return substitution if current == () else None
    return substitution if pattern is identity else None


def _all_identity(
    patterns: list[P.PatternLike],
    identity: T.Term,
    substitution: Substitution,
    state: list[int],
    binds: tuple[str, ...] = (),
) -> Iterator[Substitution]:
    if not patterns:
        yield substitution
        return
    result = _bind_identity(patterns[0], identity, substitution)
    if result is not None:
        yield from _all_identity(patterns[1:], identity, result, state, binds)


def _match_one_id(
    patterns: list[P.PatternLike],
    identity: T.Term,
    target: T.Term,
    substitution: Substitution,
    state: list[int],
    binds: tuple[str, ...] = (),
) -> Iterator[Substitution]:
    state[0] -= 1
    if state[0] < 0:
        raise BudgetExceeded()
    if not patterns:
        return
    pattern, rest = patterns[0], patterns[1:]
    for result in _match(pattern, target, substitution, state, binds):
        yield from _all_identity(rest, identity, result, state, binds)
    identity_result = _bind_identity(pattern, identity, substitution)
    if identity_result is not None:
        yield from _match_one_id(rest, identity, target, identity_result, state, binds)


def _restore_db(term: T.Term, binds: tuple[str, ...]) -> T.Term:
    """Turn a bound de Bruijn index back into its bound symbol."""
    if isinstance(term, T.DB) and binds and term.i < len(binds):
        return T.S(binds[-1 - term.i])
    return term


def _match(
    pattern: P.PatternLike,
    target: T.Term,
    substitution: Substitution,
    state: list[int],
    binds: tuple[str, ...] = (),
) -> Iterator[Substitution]:
    state[0] -= 1
    if state[0] < 0:
        raise BudgetExceeded()
    if isinstance(pattern, T.Term):
        if pattern is target:
            yield substitution
        return
    if isinstance(pattern, P.PatternVar):
        if not _pred_ok(pattern, target):
            return
        restored = _restore_db(target, binds)
        current = substitution.get(pattern.name)
        if current is None:
            result = dict(substitution)
            result[pattern.name] = restored
            yield result
        elif current is restored:
            yield substitution
        return
    if isinstance(pattern, P.PatternSeq):
        restored = _restore_db(target, binds)
        current = substitution.get(pattern.name)
        if current is None:
            result = dict(substitution)
            result[pattern.name] = (restored,)
            yield result
        elif current == (restored,):
            yield substitution
        return
    if isinstance(pattern, P.PatternCall):
        if isinstance(target, T.Expr) and target.head is pattern.head:
            if pattern.head.name in T.AC:
                yield from _match_orderless(
                    list(pattern.args), list(target.args), substitution, state, binds
                )
            else:
                yield from _match_seq(
                    list(pattern.args), list(target.args), substitution, state, binds
                )
            return
        identity = _one_identity().get(pattern.head.name)
        if identity is not None:
            yield from _match_one_id(
                list(pattern.args), identity, target, substitution, state, binds
            )


def _match_seq(
    patterns: list[P.PatternLike],
    terms: list[T.Term],
    substitution: Substitution,
    state: list[int],
    binds: tuple[str, ...] = (),
) -> Iterator[Substitution]:
    if not patterns:
        if not terms:
            yield substitution
        return
    pattern = patterns[0]
    if isinstance(pattern, P.PatternSeq):
        for size in range(1, len(terms) + 1):
            segment = tuple(_restore_db(term, binds) for term in terms[:size])
            current = substitution.get(pattern.name)
            if current is None:
                result = dict(substitution)
                result[pattern.name] = segment
                yield from _match_seq(
                    patterns[1:], terms[size:], result, state, binds
                )
            elif current == segment:
                yield from _match_seq(
                    patterns[1:], terms[size:], substitution, state, binds
                )
        return
    if not terms:
        return
    for result in _match(pattern, terms[0], substitution, state, binds):
        yield from _match_seq(patterns[1:], terms[1:], result, state, binds)


def _match_orderless(
    patterns: list[P.PatternLike],
    terms: list[T.Term],
    substitution: Substitution,
    state: list[int],
    binds: tuple[str, ...] = (),
) -> Iterator[Substitution]:
    state[0] -= 1
    if state[0] < 0:
        raise BudgetExceeded()
    if not patterns:
        if not terms:
            yield substitution
        return
    pattern = patterns[0]
    if isinstance(pattern, T.Term):
        if pattern in terms:
            rest = list(terms)
            rest.remove(pattern)
            yield from _match_orderless(
                patterns[1:], rest, substitution, state, binds
            )
        return
    if isinstance(pattern, P.PatternSeq):
        for index in range(len(terms)):
            for size in range(1, len(terms) - index + 1):
                segment = tuple(
                    _restore_db(term, binds)
                    for term in terms[index : index + size]
                )
                rest = terms[:index] + terms[index + size :]
                current = substitution.get(pattern.name)
                if current is None:
                    result = dict(substitution)
                    result[pattern.name] = segment
                    yield from _match_orderless(
                        patterns[1:], rest, result, state, binds
                    )
                elif current == segment:
                    yield from _match_orderless(
                        patterns[1:], rest, substitution, state, binds
                    )
        return
    for index, term in enumerate(terms):
        rest = terms[:index] + terms[index + 1 :]
        for result in _match(pattern, term, substitution, state, binds):
            yield from _match_orderless(patterns[1:], rest, result, state, binds)


def _sub_key(substitution: Substitution) -> tuple[tuple[str, int, tuple[int, ...]], ...]:
    items: list[tuple[str, int, tuple[int, ...]]] = []
    for name, value in substitution.items():
        if isinstance(value, tuple):
            items.append((name, 1, tuple(term._h for term in value)))
        else:
            items.append((name, 0, (value._h,)))
    return tuple(sorted(items))


def matches(
    pattern: P.PatternLike,
    target: T.Term,
    substitution: Mapping[str, SubstitutionValue] | None = None,
    budget: int = 10000,
) -> Iterator[Substitution]:
    """Yield all bindings matching ``pattern`` against ``target``."""
    state = [budget]
    base: Substitution = dict(substitution) if substitution is not None else {}
    seen: set[tuple[tuple[str, int, tuple[int, ...]], ...]] = set()
    if isinstance(pattern, P.PatternVar):
        if not _pred_ok(pattern, target):
            return
        current = base.get(pattern.name)
        if current is None or current is target:
            result = dict(base)
            result[pattern.name] = target
            yield result
        return
    for result in _match(pattern, target, base, state):
        key = _sub_key(result)
        if key in seen:
            continue
        seen.add(key)
        yield result
