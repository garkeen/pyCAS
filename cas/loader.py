import re

from cas.errors import ParseError
from cas.parser import parse
from cas.rules import Rule

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
    pat = parse(pat_s)
    tpl = parse(tpl_s)
    guard = None
    auto = False
    priority = 100
    i = 1
    while i < len(parts):
        kw = parts[i]
        val = parts[i + 1] if i + 1 < len(parts) else None
        if kw == "guard":
            guard = parse(val)
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
