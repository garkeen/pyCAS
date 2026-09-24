"""Strict parsers for rule and mathematical declaration DSL text."""

from __future__ import annotations

import re
from fractions import Fraction
from pathlib import Path

from cas.errors import ParseError
from cas.math.decls import (
    AliasDecl,
    BinderDecl,
    ConstantDecl,
    DeclarationSet,
    FunctionDecl,
    LiftDecl,
    LiftPolicy,
    RoleDecl,
)
from cas.math.domains.qarith import fold
from cas.math.rules import AutoRule, GuardedRule, ManualRule, Rule
from cas.syntax.parse import parse
from cas.syntax.term import C, Term

_RULE_HEAD = re.compile(r"^\s*rule\s+([A-Za-z_]\w*)\s*=\s*(.+)$")
_DECL_TOKEN = re.compile(r'"[^"]*"|\S+')
_OPEN = "(["
_CLOSE = ")]"


def _tokens_at_depth_zero(body: str) -> list[tuple[str, int, int]]:
    """Return whitespace tokens outside brackets as ``(text, start, end)``."""

    tokens: list[tuple[str, int, int]] = []
    depth = 0
    start: int | None = None
    for index, char in enumerate(body):
        if char in _OPEN:
            depth += 1
        elif char in _CLOSE and depth > 0:
            depth -= 1
        if char.isspace() and depth == 0:
            if start is not None:
                tokens.append((body[start:index], start, index))
                start = None
        elif start is None:
            start = index
    if start is not None:
        tokens.append((body[start:len(body)], start, len(body)))
    return tokens


def _split_keywords(body: str) -> tuple[str, str | None, str | None, bool]:
    """Split a rule body into its main text and optional suffix fields."""

    tokens = _tokens_at_depth_zero(body)
    index = len(tokens)
    auto = False
    priority_text: str | None = None
    guard_text: str | None = None

    if index and tokens[index - 1][0] == "auto":
        auto = True
        index -= 1
    if index > 1 and tokens[index - 2][0] == "prio":
        priority_text = tokens[index - 1][0]
        index -= 2
    elif index and tokens[index - 1][0] == "prio":
        raise ParseError(f"prio needs an integer value: {body!r}")

    guard_at: int | None = None
    for token_index in range(index):
        if tokens[token_index][0] == "guard":
            guard_at = token_index
            break
    if guard_at is not None:
        if guard_at + 1 == index:
            raise ParseError(f"guard needs a value: {body!r}")
        guard_text = body[tokens[guard_at][2]:tokens[index - 1][2]].strip()
        index = guard_at

    head = body[:tokens[index - 1][2]].strip() if index else ""
    keyword = (
        "guard" if guard_text is not None
        else "prio" if priority_text is not None
        else "auto" if auto
        else None
    )
    if keyword is not None and not head.rpartition("->")[2].strip():
        raise ParseError(
            f"keyword {keyword!r} found where a template is required: {body!r}")
    return head, guard_text, priority_text, auto


def _split_arrow(source: str) -> tuple[str, str]:
    index = source.find("->")
    if index < 0:
        raise ParseError(f"rule needs '->': {source}")
    return source[:index].strip(), source[index + 2:].strip()


def parse_rule_line(line: str) -> Rule:
    """Parse one rule line into its closed rule variant."""

    match = _RULE_HEAD.match(line)
    if match is None:
        raise ParseError(f"bad rule line: {line}")
    rule_id = match.group(1)
    head, guard_text, priority_text, auto = _split_keywords(match.group(2))
    pattern_text, template_text = _split_arrow(head)
    pattern = parse(pattern_text, pattern=True)
    template = parse(template_text, pattern=True)
    condition = parse(guard_text, pattern=True) if guard_text is not None else None
    priority = 100
    if priority_text is not None:
        try:
            priority = int(priority_text)
        except ValueError:
            raise ParseError(
                f"prio value {priority_text!r} is not an integer: {line!r}") from None
    if auto:
        if condition is not None:
            raise ParseError(f"auto rule must not carry a guard: {line!r}")
        return AutoRule(id=rule_id, pattern=pattern, template=template, priority=priority)
    if condition is None:
        return ManualRule(id=rule_id, pattern=pattern, template=template, priority=priority)
    return GuardedRule(
        id=rule_id,
        pattern=pattern,
        template=template,
        condition=condition,
        priority=priority,
    )


def _strip_comment(line: str) -> str:
    """Remove a comment outside a quoted string."""

    output: list[str] = []
    in_string = False
    for char in line:
        if char == '"':
            in_string = not in_string
        elif char == "#" and not in_string:
            break
        output.append(char)
    return "".join(output)


def _tokens(line: str) -> list[str]:
    """Tokenize a declaration statement, preserving quoted text as one token."""

    return [
        token[1:-1] if token.startswith('"') and token.endswith('"') else token
        for token in _DECL_TOKEN.findall(line)
    ]


def _bound_value(source: str) -> Fraction | None:
    if source == "none":
        return None
    try:
        return Fraction(source)
    except ValueError:
        raise ParseError(f"invalid bound value: {source!r}") from None


def _integer(tokens: list[str], index: int, statement: str, lineno: int) -> int:
    if index >= len(tokens):
        raise ParseError(f"line {lineno}: {statement} needs an integer value")
    try:
        return int(tokens[index])
    except ValueError:
        raise ParseError(
            f"line {lineno}: invalid integer for {statement}: {tokens[index]!r}") from None


_LIFT = re.compile(r"^lift\s+([A-Za-z_]\w*)\s*=\s*([A-Za-z]+)$")
_ALIAS = re.compile(r"^alias\s+([A-Za-z_]\w*)\s*=\s*([A-Za-z_]\w*)$")
_BINDER = re.compile(r"^binder\s+([A-Za-z_]\w*)$")
_ROLE = re.compile(r"^role\s+([A-Za-z_]\w*)\s*=\s*([A-Za-z_]\w*)$")


def _parse_lift(lineno: int, line: str) -> LiftDecl:
    match = _LIFT.match(line)
    if match is None:
        raise ParseError(
            f"line {lineno}: lift must look like 'lift <Head> = congruent|conditional|forbidden'")
    try:
        policy = LiftPolicy(match.group(2))
    except ValueError:
        raise ParseError(
            f"line {lineno}: unknown lift policy {match.group(2)!r}") from None
    return LiftDecl(match.group(1), policy)


def _parse_alias(lineno: int, line: str) -> AliasDecl:
    match = _ALIAS.match(line)
    if match is None:
        raise ParseError(f"line {lineno}: alias must look like 'alias <name> = <Head>'")
    return AliasDecl(match.group(1), match.group(2))


def _parse_binder(lineno: int, line: str) -> BinderDecl:
    match = _BINDER.match(line)
    if match is None:
        raise ParseError(
            f"line {lineno}: binder must look like 'binder <Head>'")
    return BinderDecl(match.group(1))


def _parse_role(lineno: int, line: str) -> RoleDecl:
    match = _ROLE.match(line)
    if match is None:
        raise ParseError(f"line {lineno}: role must look like 'role <role> = <Head>'")
    return RoleDecl(match.group(1), match.group(2))


def _parse_constant(lineno: int, line: str) -> ConstantDecl:
    tokens = _tokens(line)
    if len(tokens) < 2:
        raise ParseError(f"line {lineno}: constant is missing a name")
    name = tokens[1]
    print_name = name
    real: bool | None = None
    positive: bool | None = None
    bounds: tuple[int, int] | None = None
    index = 2
    while index < len(tokens):
        key = tokens[index]
        if key == "print":
            if index + 1 >= len(tokens):
                raise ParseError(f"line {lineno}: print needs a value")
            print_name = tokens[index + 1]
            index += 2
        elif key == "real":
            if index + 1 < len(tokens) and tokens[index + 1] in ("true", "false"):
                real = tokens[index + 1] == "true"
                index += 2
            else:
                real = True
                index += 1
        elif key == "positive":
            positive = True
            index += 1
        elif key == "bounds":
            low = _integer(tokens, index + 1, "bounds", lineno)
            high = _integer(tokens, index + 2, "bounds", lineno)
            bounds = (low, high)
            index += 3
        else:
            raise ParseError(f"line {lineno}: unknown constant key {key!r}")
    return ConstantDecl(C(name), name, print_name, real, positive, bounds)


def _parse_function(
    lineno: int,
    line: str,
    constants: dict[str, Term],
) -> FunctionDecl:
    tokens = _tokens(line)
    if len(tokens) < 2:
        raise ParseError(f"line {lineno}: function is missing a head name")
    name = tokens[1]
    print_name = name
    arity: int | None = None
    real_on_real: bool | None = None
    bound: tuple[Fraction | None, Fraction | None] | None = None
    zero_iff_arg_zero = False
    deriv: Term | None = None
    domain: Term | None = None
    note = ""
    index = 2
    while index < len(tokens):
        key = tokens[index]
        if key == "print":
            if index + 1 >= len(tokens):
                raise ParseError(f"line {lineno}: print needs a value")
            print_name = tokens[index + 1]
            index += 2
        elif key == "arity":
            arity = _integer(tokens, index + 1, "arity", lineno)
            index += 2
        elif key == "real_on_real":
            real_on_real = True
            index += 1
        elif key == "zero_iff_arg_zero":
            zero_iff_arg_zero = True
            index += 1
        elif key == "bounds":
            if index + 2 >= len(tokens):
                raise ParseError(f"line {lineno}: bounds needs two values")
            bound = (
                _bound_value(tokens[index + 1]),
                _bound_value(tokens[index + 2]),
            )
            index += 3
        elif key == "deriv":
            if index + 1 >= len(tokens):
                raise ParseError(f"line {lineno}: deriv needs a template")
            deriv = fold(parse(tokens[index + 1], constants=constants))
            index += 2
        elif key == "domain":
            if index + 1 >= len(tokens):
                raise ParseError(f"line {lineno}: domain needs a condition")
            domain = fold(parse(tokens[index + 1], constants=constants))
            index += 2
        elif key == "note":
            if index + 1 >= len(tokens):
                raise ParseError(f"line {lineno}: note needs text")
            note = tokens[index + 1]
            index += 2
        else:
            raise ParseError(f"line {lineno}: unknown function key {key!r}")
    if arity is None:
        raise ParseError(f"line {lineno}: function {name} is missing arity")
    return FunctionDecl(
        name=name,
        print_name=print_name,
        arity=arity,
        real_on_real=real_on_real,
        bound=bound,
        zero_iff_arg_zero=zero_iff_arg_zero,
        deriv=deriv,
        domain=domain,
        note=note,
    )


def _ensure_unique(identities: tuple[str, ...], kind: str) -> None:
    seen: set[str] = set()
    for identity in identities:
        if identity in seen:
            raise ParseError(f"duplicate {kind} declaration {identity!r}")
        seen.add(identity)


def parse_declarations(text: str) -> DeclarationSet:
    """Parse declaration DSL text into immutable, fully typed records."""

    constant_lines: list[tuple[int, str]] = []
    function_lines: list[tuple[int, str]] = []
    alias_lines: list[tuple[int, str]] = []
    binder_lines: list[tuple[int, str]] = []
    role_lines: list[tuple[int, str]] = []
    lift_lines: list[tuple[int, str]] = []
    rule_lines: list[tuple[int, str]] = []
    for lineno, raw in enumerate(text.splitlines(), 1):
        line = _strip_comment(raw).strip()
        if not line:
            continue
        if line.startswith("rule "):
            rule_lines.append((lineno, line))
        elif line.startswith("constant "):
            constant_lines.append((lineno, line))
        elif line.startswith("function "):
            function_lines.append((lineno, line))
        elif line.startswith("alias "):
            alias_lines.append((lineno, line))
        elif line.startswith("binder "):
            binder_lines.append((lineno, line))
        elif line.startswith("role "):
            role_lines.append((lineno, line))
        elif line.startswith("lift "):
            lift_lines.append((lineno, line))
        else:
            raise ParseError(f"line {lineno}: unknown declaration: {line!r}")

    constants = tuple(_parse_constant(lineno, line) for lineno, line in constant_lines)
    _ensure_unique(tuple(declaration.name for declaration in constants), "constant")
    constant_map: dict[str, Term] = {
        declaration.name: declaration.atom for declaration in constants
    }
    functions = tuple(
        _parse_function(lineno, line, constant_map)
        for lineno, line in function_lines
    )
    _ensure_unique(tuple(declaration.name for declaration in functions), "function")
    aliases = tuple(_parse_alias(lineno, line) for lineno, line in alias_lines)
    _ensure_unique(tuple(declaration.surface for declaration in aliases), "alias")
    binders = tuple(_parse_binder(lineno, line) for lineno, line in binder_lines)
    _ensure_unique(tuple(declaration.head for declaration in binders), "binder")
    roles = tuple(_parse_role(lineno, line) for lineno, line in role_lines)
    _ensure_unique(tuple(declaration.role for declaration in roles), "role")
    lifts = tuple(_parse_lift(lineno, line) for lineno, line in lift_lines)
    _ensure_unique(tuple(declaration.head for declaration in lifts), "lift")
    rules = tuple(parse_rule_line(line) for _lineno, line in rule_lines)
    _ensure_unique(tuple(rule.id for rule in rules), "rule")
    return DeclarationSet(
        constants=constants,
        functions=functions,
        aliases=aliases,
        binders=binders,
        roles=roles,
        lifts=lifts,
        rules=rules,
    )


def load_declarations(path: str | Path) -> DeclarationSet:
    """Read and parse one UTF-8 declaration DSL file."""

    return parse_declarations(Path(path).read_text(encoding="utf-8"))
