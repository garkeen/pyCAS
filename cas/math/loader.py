"""Declaration DSL parsing: the single DSL parsing responsibility.

Two kinds of DSL text are parsed here:

· **rule lines**: `rule <id> = <pattern> -> <template> [guard <expr>] [prio N] [auto]`
  (see `parse_rule_line`).
· **declaration lines** (constants, functions, derivative templates and domain
  conditions must be declared in the DSL rather than registered from Python):

      constant <Name> print "<name>" [real [true|false]] [positive]
                     [bounds <lo> <hi>]

      function <Head> print "<name>" arity <n> [real_on_real]
                     [bounds <lo> <hi>] [zero_iff_arg_zero]
                     [deriv "<template>"] [domain "<condition>"] [note "<text>"]

      alias <surface> = <Head>         # a parse-level token (ln, sqrt) to a canonical head
      role <role> = <Head>             # a canonical function an algorithm refers to

  `<lo>` / `<hi>` are integers or `none` for unbounded. Inside `<template>` and
  `<condition>`, `@0` is a de Bruijn placeholder for the function's argument,
  instantiated by the differentiation layer or the domain-condition layer.

**Why it must be text**: the admission discipline (only unconditional identities,
branch-breaking templates set to null with a recorded reason) must be checkable
mechanically against text, not by inspecting Python registration calls.

**This module returns neutral data** (dicts, tuples, raw rule lines); it neither
builds the runtime declaration objects nor imports the runtime, because the
dependency direction is runtime -> math. The assembler (the elementary module)
hands the dicts to the injected builder.
"""

import re

from dataclasses import dataclass
from fractions import Fraction as Fr

from cas.errors import ParseError
from cas.frontend.parser import parse
from cas.syntax.term import C
from cas.math.qarith import fold
from cas.math.rules import Rule

_HEAD = re.compile(r"^\s*rule\s+([A-Za-z_]\w*)\s*=\s*(.+)$")
_KWS = ("guard", "prio", "auto")
_SEP = "\x00"


def _split_keywords(body):
    rest = " " + body.strip() + " "
    rest = re.sub(r"\s+auto\s*$", " \x00auto\x00 ", rest)
    for kw in _KWS:
        rest = re.sub(rf"\s+{kw}\s+", f" {_SEP}{kw}{_SEP} ", rest)
    parts = [p.strip() for p in rest.split(_SEP) if p.strip()]
    return parts


def _split_arrow(s):
    idx = s.find("->")
    if idx < 0:
        raise ParseError(f"rule needs '->': {s}")
    return s[:idx].strip(), s[idx + 2 :].strip()


def parse_rule_line(line):
    m = _HEAD.match(line)
    if not m:
        raise ParseError(f"bad rule line: {line}")
    rid = m.group(1)
    parts = _split_keywords(m.group(2))
    pat_s, tpl_s = _split_arrow(parts[0])
    # LHS/RHS/guard are all parsed through the pattern channel, so the products
    # are Patterns rather than Terms.
    pat = parse(pat_s, pattern=True)
    tpl = parse(tpl_s, pattern=True)
    guard = None
    auto = False
    priority = 100
    i = 1
    while i < len(parts):
        kw = parts[i]
        val = parts[i + 1] if i + 1 < len(parts) else None
        if kw == "guard":
            guard = parse(val, pattern=True)
            i += 2
        elif kw == "prio":
            priority = int(val)
            i += 2
        elif kw == "auto":
            auto = True
            i += 1
        else:
            i += 1
    return Rule(id=rid, pattern=pat, template=tpl, guard=guard,
                auto=auto, priority=priority)


# ---------------------------------------------------------------------------
# Declaration DSL
# ---------------------------------------------------------------------------

_DECL_TOK = re.compile(r'"[^"]*"|\S+')


def _strip_comment(line):
    """Remove a `#` comment outside quoted strings, since note text may contain
    `#`."""
    out, in_str = [], False
    for ch in line:
        if ch == '"':
            in_str = not in_str
        elif ch == "#" and not in_str:
            break
        out.append(ch)
    return "".join(out)


def _tokens(line):
    toks = _DECL_TOK.findall(line)
    return [t[1:-1] if t.startswith('"') and t.endswith('"') else t
            for t in toks]


def _bound_val(s):
    return None if s == "none" else Fr(s)


@dataclass(frozen=True, slots=True)
class Declarations:
    """The parsed result of the declaration DSL (neutral data whose field names
    line up with the runtime declaration objects)."""
    constants: tuple      # tuple[dict]
    functions: tuple      # tuple[dict]
    aliases: tuple        # tuple[(surface name, canonical head)]
    roles: tuple          # tuple[(role, canonical head)]
    rules: tuple          # tuple[str] of rule lines, parsed by parse_rule_line


_ALIAS = re.compile(r"^alias\s+([A-Za-z_]\w*)\s*=\s*([A-Za-z_]\w*)$")


def _parse_alias(lineno, line):
    m = _ALIAS.match(line)
    if not m:
        raise ParseError(f"line {lineno}: alias must look like 'alias <name> = <Head>'")
    return (m.group(1), m.group(2))


_ROLE = re.compile(r"^role\s+([A-Za-z_]\w*)\s*=\s*([A-Za-z_]\w*)$")


def _parse_role(lineno, line):
    m = _ROLE.match(line)
    if not m:
        raise ParseError(f"line {lineno}: role must look like 'role <role> = <Head>'")
    return (m.group(1), m.group(2))


def _parse_constant(lineno, line):
    t = _tokens(line)
    if len(t) < 2:
        raise ParseError(f"line {lineno}: constant is missing a name")
    d = {"name": t[1], "print_name": t[1]}
    i = 2
    while i < len(t):
        k = t[i]
        if k == "print":
            d["print_name"] = t[i + 1]
            i += 2
        elif k == "real":
            if i + 1 < len(t) and t[i + 1] in ("true", "false"):
                d["real"] = t[i + 1] == "true"
                i += 2
            else:
                d["real"] = True
                i += 1
        elif k == "positive":
            d["positive"] = True
            i += 1
        elif k == "bounds":
            d["bounds"] = (int(t[i + 1]), int(t[i + 2]))
            i += 3
        else:
            raise ParseError(f"line {lineno}: unknown constant key {k!r}")
    return d


def _parse_function(lineno, line, const_map):
    t = _tokens(line)
    if len(t) < 2:
        raise ParseError(f"line {lineno}: function is missing a head name")
    d = {"name": t[1], "print_name": t[1], "arity": None}
    i = 2
    while i < len(t):
        k = t[i]
        if k == "print":
            d["print_name"] = t[i + 1]
            i += 2
        elif k == "arity":
            d["arity"] = int(t[i + 1])
            i += 2
        elif k == "real_on_real":
            d["real_on_real"] = True
            i += 1
        elif k == "zero_iff_arg_zero":
            d["zero_iff_arg_zero"] = True
            i += 1
        elif k == "bounds":
            d["bound"] = (_bound_val(t[i + 1]), _bound_val(t[i + 2]))
            i += 3
        elif k == "deriv":
            d["deriv"] = fold(parse(t[i + 1], constants=const_map))
            i += 2
        elif k == "domain":
            d["domain"] = fold(parse(t[i + 1], constants=const_map))
            i += 2
        elif k == "note":
            d["note"] = t[i + 1]
            i += 2
        else:
            raise ParseError(f"line {lineno}: unknown function key {k!r}")
    return d


def parse_declarations(text) -> Declarations:
    """Parse declaration DSL text. Constants are collected first to build the
    atom table, which is then used to parse function templates.

    Template parsing does **not** call back into the runtime: the atom table is
    injected through `constants=`, because calling dispatch during bootstrap would
    trigger lazy assembly and recurse. An identifier in a template that is not a
    declared constant is treated as a symbol (a function head), which is exactly
    what templates like `Sin(@0)` need.
    """
    const_lines, func_lines, alias_lines, role_lines, rules = [], [], [], [], []
    for lineno, raw in enumerate(text.splitlines(), 1):
        line = _strip_comment(raw).strip()
        if not line:
            continue
        if line.startswith("rule "):
            rules.append(line)
        elif line.startswith("constant "):
            const_lines.append((lineno, line))
        elif line.startswith("function "):
            func_lines.append((lineno, line))
        elif line.startswith("alias "):
            alias_lines.append((lineno, line))
        elif line.startswith("role "):
            role_lines.append((lineno, line))
        else:
            raise ParseError(f"line {lineno}: unknown declaration: {line!r}")

    constants = tuple(_parse_constant(ln, l) for ln, l in const_lines)
    const_map = {c["name"]: C(c["name"]) for c in constants}
    functions = tuple(_parse_function(ln, l, const_map) for ln, l in func_lines)
    aliases = tuple(_parse_alias(ln, l) for ln, l in alias_lines)
    roles = tuple(_parse_role(ln, l) for ln, l in role_lines)
    return Declarations(constants, functions, aliases, roles, tuple(rules))


def load_declarations(path) -> Declarations:
    """Read a declaration DSL file (UTF-8) and parse it."""
    with open(path, encoding="utf-8") as f:
        return parse_declarations(f.read())
