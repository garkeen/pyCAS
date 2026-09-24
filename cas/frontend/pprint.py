"""Typed pretty-printing for terms and pattern-language values."""

from __future__ import annotations

from collections.abc import Mapping, Sequence
from fractions import Fraction
from typing import TypeAlias

from cas.runtime.runtime import Runtime
from cas.syntax import pattern as P
from cas.syntax import term as T
from cas.syntax.parse import atom_notation
from cas.syntax.term import DB, Bound, BVal, Const, Expr, Int, Rat, Special, Sym, Term
from cas.syntax.termpath import postorder

Rendered: TypeAlias = tuple[str, int]
PatternLike: TypeAlias = T.Term | P.Pattern

_PREC = {
    "Eq": 2,
    "Ne": 2,
    "Lt": 2,
    "Le": 2,
    "Gt": 2,
    "Ge": 2,
    "Plus": 3,
    "Times": 4,
    "Power": 6,
}
_INFIX = {
    "Plus": "+",
    "Times": "*",
    "Eq": "==",
    "Ne": "!=",
    "Lt": "<",
    "Le": "<=",
    "Gt": ">",
    "Ge": ">=",
}
_ATOM_P = 100


def _atom_str(runtime: Runtime, atom: Term, src: bool = False) -> str:
    """Render a term atom in display or source mode."""
    if isinstance(atom, Sym):
        return atom.name
    if isinstance(atom, Const):
        if src:
            return atom.name
        declaration = runtime.const_by_atom(atom)
        return declaration.print_name if declaration is not None else atom.name
    if isinstance(atom, BVal):
        return "true" if atom.val else "false"
    if isinstance(atom, Int):
        return str(atom.v)
    if isinstance(atom, Rat):
        return f"{atom.f.numerator}/{atom.f.denominator}"
    if isinstance(atom, Special):
        if src:
            notation = atom_notation(atom)
            if notation is not None:
                return notation
        if atom is T.EMPTY_SET:
            return "{}"
        return atom.name
    if isinstance(atom, DB):
        return f"@{atom.i}" if src else f"#{atom.i}"
    return repr(atom)


def _name_of(runtime: Runtime, head: Sym, src: bool = False) -> str:
    """Render a head using declared display data or its canonical name."""
    print_name = runtime.print_name(head.name)
    if print_name is not None:
        return print_name
    return head.name if src else head.name.lower()


def _wrap(child: Rendered, needed_precedence: int) -> str:
    text, precedence = child
    return "(" + text + ")" if needed_precedence > precedence else text


def _call_str(
    name: str,
    values: Mapping[Term, Rendered],
    arguments: Sequence[Term],
) -> str:
    return name + "(" + ", ".join(_wrap(values[argument], 0) for argument in arguments) + ")"


_BINDER_SYMBOLS = {
    "Integrate": "∫",
    "Sum": "Σ",
    "Product": "Π",
    "Limit": "lim",
}


def _binder_display(runtime: Runtime, node: Expr, bound: Bound, body: Term) -> str:
    if node.head.name == "DefIntegrate" and len(node.args) == 3:
        lower, upper = node.args[1], node.args[2]
        return f"∫_{to_str(runtime, lower)}^{to_str(runtime, upper)}[{to_str(runtime, body)}] d{bound.hint}"
    symbol = _BINDER_SYMBOLS.get(node.head.name)
    if symbol is not None and len(node.args) == 1:
        return f"{symbol}[{to_str(runtime, body)}] d{bound.hint}"
    parts = [to_str(runtime, body), bound.hint]
    parts.extend(to_str(runtime, argument) for argument in node.args[1:])
    return f"{_name_of(runtime, node.head)}({', '.join(parts)})"


def to_str(
    runtime: Runtime,
    term: Term,
    precedence: int = 0,
    hint: str | None = None,
    src: bool = False,
) -> str:
    """Render a term in display or parseable source form."""
    del hint
    values: dict[Term, Rendered] = {}
    for current in reversed(postorder(term)):
        if not isinstance(current, Expr):
            if isinstance(current, Bound):
                values[current] = values[current.body]
            else:
                values[current] = (_atom_str(runtime, current, src), _ATOM_P)
            continue
        name = current.head.name
        if name == "Quote":
            values[current] = ("'" + _wrap(values[current.args[0]], 0), _ATOM_P)
            continue
        if (
            current.args
            and isinstance(current.args[0], Bound)
            and runtime.is_binder(current.head.name)
        ):
            bound = current.args[0]
            _variable, body = T.open_bound(bound)
            if src:
                source_parts = [to_str(runtime, body, src=True), bound.hint]
                source_parts.extend(
                    to_str(runtime, argument, src=True) for argument in current.args[1:]
                )
                values[current] = (
                    f"{current.head.name}(" + ", ".join(source_parts) + ")",
                    _ATOM_P,
                )
            else:
                values[current] = (_binder_display(runtime, current, bound, body), _ATOM_P)
            continue
        if name == "Piecewise" and len(current.args) % 2 == 0:
            if src:
                values[current] = (_call_str(name, values, current.args), _ATOM_P)
            else:
                parts = [
                    f"{_wrap(values[current.args[index]], 0)} if "
                    f"{_wrap(values[current.args[index + 1]], 0)}"
                    for index in range(0, len(current.args), 2)
                ]
                values[current] = ("piecewise(" + ", ".join(parts) + ")", _ATOM_P)
            continue
        if name == "FiniteSet":
            if src:
                values[current] = (_call_str(name, values, current.args), _ATOM_P)
            else:
                values[current] = (
                    "{" + ", ".join(_wrap(values[argument], 0) for argument in current.args) + "}",
                    _ATOM_P,
                )
            continue
        if name == "Interval" and len(current.args) == 4:
            if src:
                values[current] = (_call_str(name, values, current.args), _ATOM_P)
            else:
                lower, upper, lower_open, upper_open = current.args
                left = "(" if isinstance(lower_open, BVal) and lower_open.val else "["
                right = ")" if isinstance(upper_open, BVal) and upper_open.val else "]"
                values[current] = (
                    f"{left}{_wrap(values[lower], 0)}, {_wrap(values[upper], 0)}{right}",
                    _ATOM_P,
                )
            continue
        if name == "Union":
            if src:
                values[current] = (_call_str(name, values, current.args), _ATOM_P)
            else:
                values[current] = (
                    " U ".join(_wrap(values[argument], 0) for argument in current.args),
                    _ATOM_P,
                )
            continue
        if name == "O" and len(current.args) == 1:
            values[current] = (
                "O(" + _wrap(values[current.args[0]], 0) + ")",
                _ATOM_P,
            )
            continue
        if name in _PREC:
            own_precedence = _PREC[name]
            if name == "Plus":
                plus_parts: list[str] = []
                for index, argument in enumerate(current.args):
                    argument_text = _wrap(values[argument], own_precedence)
                    negative = argument_text.startswith("-")
                    plus_parts.append(
                        argument_text
                        if index == 0
                        else "- " + argument_text[1:]
                        if negative
                        else "+ " + argument_text
                    )
                body_text = " ".join(plus_parts)
            elif name == "Times":
                factors: list[str] = []
                denominator_factors: list[tuple[Term, int]] = []
                kept: list[Term] = []
                coefficient = Fraction(1)
                for argument in current.args:
                    if T.is_num(argument):
                        coefficient *= T.num_val(argument)
                        continue
                    if (
                        isinstance(argument, Expr)
                        and argument.head.name == "Power"
                        and isinstance(argument.args[1], Int)
                        and argument.args[1].v < 0
                    ):
                        base = argument.args[0]
                        exponent_term = argument.args[1]
                        if not isinstance(exponent_term, Int):
                            continue
                        if T.is_num(base) and T.num_val(base) != 0:
                            coefficient *= T.num_val(base) ** exponent_term.v
                        else:
                            denominator_factors.append((base, -exponent_term.v))
                        continue
                    kept.append(argument)
                numerator, denominator = coefficient.numerator, coefficient.denominator
                coefficient_text = ""
                if numerator == -1:
                    coefficient_text = "-"
                elif numerator != 1:
                    coefficient_text = _atom_str(runtime, T.N(numerator))
                denominator_text = "" if denominator == 1 else str(denominator)
                factors.extend(_wrap(values[argument], own_precedence) for argument in kept)
                body_text = (
                    "*".join(factors)
                    if factors
                    else coefficient_text
                    if coefficient_text not in ("", "-")
                    else "1"
                )
                if coefficient_text and coefficient_text != "-" and factors:
                    body_text = coefficient_text + "*" + body_text
                elif coefficient_text == "-":
                    body_text = "-" + body_text
                elif coefficient_text and not factors:
                    body_text = coefficient_text
                if denominator_factors or denominator_text:
                    denominator_parts = [denominator_text] if denominator_text else []
                    for denominator_base, denominator_exponent in denominator_factors:
                        base_text = _wrap(values[denominator_base], 6)
                        if T.is_num(denominator_base) and (
                            T.num_val(denominator_base) < 0 or isinstance(denominator_base, Rat)
                        ):
                            base_text = "(" + base_text + ")"
                        denominator_parts.append(
                            base_text if denominator_exponent == 1
                            else f"{base_text}^{denominator_exponent}"
                        )
                    rendered_denominator = (
                        denominator_parts[0]
                        if len(denominator_parts) == 1
                        else "(" + "*".join(denominator_parts) + ")"
                    )
                    body_text += "/" + rendered_denominator
            elif name == "Power":
                base, exponent = current.args
                base_text = _wrap(values[base], own_precedence)
                if T.is_num(base) and (
                    T.num_val(base) < 0 or isinstance(base, Rat)
                ):
                    base_text = "(" + base_text + ")"
                exponent_text = _wrap(values[exponent], own_precedence + 1)
                if isinstance(exponent, Rat):
                    exponent_text = "(" + exponent_text + ")"
                body_text = f"{base_text}^{exponent_text}"
            else:
                parts = [
                    _wrap(values[argument], own_precedence + 1)
                    for argument in current.args
                ]
                body_text = f" {_INFIX.get(name, name)} ".join(parts)
            values[current] = (body_text, own_precedence)
            continue
        arguments = ", ".join(_wrap(values[argument], 0) for argument in current.args)
        values[current] = (f"{_name_of(runtime, current.head, src)}({arguments})", _ATOM_P)

    text, own_precedence = values[term]
    if (
        precedence > own_precedence
        and isinstance(term, Expr)
        and term.head.name in _PREC
    ):
        return "(" + text + ")"
    return text


def _pat_prec(pattern: PatternLike) -> int:
    if isinstance(pattern, P.PatternCall) and pattern.head.name in _PREC:
        return _PREC[pattern.head.name]
    return _ATOM_P


def pat_to_str(runtime: Runtime, pattern: PatternLike, src: bool = False) -> str:
    """Render a pattern in a reparsable pattern-language form."""
    if isinstance(pattern, T.Term):
        return to_str(runtime, pattern, src=src)
    if isinstance(pattern, P.PatternVar):
        return "?" + pattern.name + (("::" + pattern.pred) if pattern.pred else "")
    if isinstance(pattern, P.PatternSeq):
        return "??" + pattern.name
    if not isinstance(pattern, P.PatternCall):
        raise TypeError(f"unsupported pattern node: {pattern!r}")
    name = pattern.head.name
    if name in _PREC:
        precedence = _PREC[name]
        if name == "Power":
            base, exponent = pattern.args
            base_text = _wrap((pat_to_str(runtime, base, src), _pat_prec(base)), precedence)
            exponent_text = _wrap(
                (pat_to_str(runtime, exponent, src), _pat_prec(exponent)),
                precedence + 1,
            )
            return f"{base_text}^{exponent_text}"
        parts = [
            _wrap(
                (pat_to_str(runtime, argument, src), _pat_prec(argument)),
                precedence + 1,
            )
            for argument in pattern.args
        ]
        return f" {_INFIX.get(name, name)} ".join(parts)
    arguments = ", ".join(pat_to_str(runtime, argument, src) for argument in pattern.args)
    return f"{_name_of(runtime, pattern.head, src)}({arguments})"
