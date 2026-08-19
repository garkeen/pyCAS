import os
import re

from cas.errors import ParseError
from cas.parser import parse
from cas.rules import Rule

_HEAD = re.compile(r"^\s*rule\s+([A-Za-z_]\w*)\s*=\s*(.+)$")
_KWS = ("guard", "as", "channels", "prio", "auto")
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


def parse_rule_line(line, origin="dsl"):
    m = _HEAD.match(line)
    if not m:
        raise ParseError(f"bad rule line: {line}")
    rid = m.group(1)
    parts = _split_keywords(m.group(2))
    pat_s, tpl_s = _split_arrow(parts[0])
    pat = parse(pat_s)
    tpl = parse(tpl_s)
    guard = None
    direction = None
    channels = ("manual", "suggest")
    auto = False
    priority = 100
    i = 1
    while i < len(parts):
        kw = parts[i]
        val = parts[i + 1] if i + 1 < len(parts) else None
        if kw == "guard":
            guard = parse(val)
            i += 2
        elif kw == "as":
            direction = val
            i += 2
        elif kw == "channels":
            channels = tuple(c.strip() for c in val.split(",") if c.strip())
            i += 2
        elif kw == "prio":
            priority = int(val)
            i += 2
        elif kw == "auto":
            auto = True
            i += 1
        else:
            i += 1
    return Rule(
        id=rid,
        pattern=pat,
        template=tpl,
        guard=guard,
        direction=direction,
        channels=channels,
        auto=auto,
        origin=origin,
        priority=priority,
    )


def parse_rules(text, origin="dsl"):
    out = []
    for raw in text.splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        out.append(parse_rule_line(line, origin))
    return out


def load_dir(path, ruleset):
    n = 0
    errors = []
    for fn in sorted(os.listdir(path)):
        if fn.endswith(".rules"):
            try:
                with open(os.path.join(path, fn), encoding="utf-8") as fh:
                    rules = parse_rules(fh.read(), origin=fn)
            except ParseError as e:
                errors.append(f"{fn}: {e}")
                continue
            for r in rules:
                ruleset.add(r)
                n += 1
    if errors:
        raise ParseError("; ".join(errors))
    return n
