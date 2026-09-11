"""Pattern metalanguage: a pattern is not a term.

PatternVar / PatternSeq are not Term subclasses, so they can never appear in a
user expression, a domain projection or a mathematical equality test. The term
layer holds mathematical objects only.

A literal is used directly as a pattern: pointer equality of interned terms is
literal matching, so no wrapper type is needed and a pattern argument has type
`Pattern | Term`, recorded here as PatternLike.

Rule declarations (DSL) are parsed through the pattern channel by the loader,
producing Pattern objects; template instantiation produces Terms. Pattern
variables therefore occur in exactly two places: matching and instantiation.
"""

from cas.syntax import term as T
from cas.errors import BudgetExceeded, ParseError

_hp = 0


def _next_hp():
    global _hp
    _hp += 1
    return _hp


class Pattern:
    """Base of the closed pattern hierarchy: interned pointer semantics,
    isomorphic to Term."""

    __slots__ = ("_h",)

    def __hash__(self):
        return self._h

    def __eq__(self, other):
        return self is other

    def __ne__(self, other):
        return self is not other

    def __lt__(self, other):
        return sort_key(self) < sort_key(other)


class PatternVar(Pattern):
    __slots__ = ("name", "pred")

    def __init__(self, name, pred=None):
        self.name = name
        self.pred = pred
        self._h = _next_hp()

    def __repr__(self):
        return f"?{self.name}" + (f"::{self.pred}" if self.pred else "")


class PatternSeq(Pattern):
    __slots__ = ("name",)

    def __init__(self, name):
        self.name = name
        self._h = _next_hp()

    def __repr__(self):
        return f"??{self.name}"


class PatternCall(Pattern):
    __slots__ = ("head", "args")

    def __init__(self, head, args, h):
        self.head = head                  # Term (a symbol)
        self.args = args                  # tuple[PatternLike, ...]
        self._h = h

    def __repr__(self):
        return f"{self.head.name}{tuple(repr(a) for a in self.args)}"


_VARS = {}
_SEQS = {}
_CALLS = {}


def PV(name, pred=None):
    t = _VARS.get((name, pred))
    if t is None:
        t = PatternVar(name, pred)
        _VARS[(name, pred)] = t
    return t


def PS(name):
    t = _SEQS.get(name)
    if t is None:
        t = PatternSeq(name)
        _SEQS[name] = t
    return t


def _flatten_ac(head, args):
    """AC-head flattening, isomorphic to the term layer: flatten same-head
    nesting and sort deterministically."""
    flat = []
    for a in args:
        if isinstance(a, PatternCall) and a.head is head:
            flat.extend(a.args)
        else:
            flat.append(a)
    return sorted(flat, key=sort_key)


def pcall(head, args):
    """Interned PatternCall constructor; AC heads get the same flattening and
    sorting as the term layer."""
    name = head.name if isinstance(head, T.Sym) else None
    if name in T.AC:
        args = _flatten_ac(head, list(args))
    key = (head._h, tuple(a._h for a in args))
    t = _CALLS.get(key)
    if t is None:
        t = PatternCall(head, tuple(args), _next_hp())
        _CALLS[key] = t
    return t


def sort_key(p):
    """Pattern sort key. Terms reuse T.sort_key so that the relative order of
    literals matches the term layer."""
    if isinstance(p, T.Term):
        return (10,) + T.sort_key(p)
    k = p.__class__
    if k is PatternVar:
        return (0, p.name, p.pred or "")
    if k is PatternSeq:
        return (1, p.name)
    return (11, T.sort_key(p.head), tuple(sort_key(a) for a in p.args))


def has_holes(p):
    """Whether the pattern contains a hole. Always False for a Term, since a
    hole cannot occur inside a term."""
    if isinstance(p, T.Term):
        return False
    if p.__class__ is PatternCall:
        return any(has_holes(a) for a in p.args)
    return True


def root_key(p):
    """Rule index key: AC heads bucket by head name, holes map to '*'. Mirrors
    the term-layer root key."""
    if isinstance(p, T.Term):
        if isinstance(p, T.Expr):
            return p.head.name
        return p.__class__.__name__ + ":" + repr(p)
    if p.__class__ is PatternCall:
        return p.head.name
    return "*"


def instantiate(pat, sub):
    """Template instantiation: Pattern -> Term.

    An unbound hole means the rule declaration is defective, so it is reported
    explicitly rather than letting a pattern variable leak into the term layer.
    """
    if isinstance(pat, T.Term):
        return pat
    k = pat.__class__
    if k is PatternVar:
        v = sub.get(pat.name)
        if v is None:
            raise ParseError(f"unbound pattern variable ?{pat.name} in rule template")
        return v
    if k is PatternSeq:
        raise BudgetExceeded(message=f"sequence hole ??{pat.name} not in arg position")
    if pat.head.name == "Quote":
        # Inside Quote the held structure is preserved: rebuild raw, no AC
        # normalization.
        return T._intern_expr(pat.head, tuple(_inst_raw(a, sub) for a in pat.args))
    out = []
    for a in pat.args:
        if a.__class__ is PatternSeq:
            seq = sub.get(a.name)
            if seq is None:
                raise ParseError(f"unbound sequence hole ??{a.name} in rule template")
            out.extend(seq)
        else:
            out.append(instantiate(a, sub))
    return T.mk(pat.head, tuple(out))


def _inst_raw(pat, sub):
    """Held channel of `instantiate`: rebuild through _intern_expr, with no AC
    normalization."""
    if isinstance(pat, T.Term):
        return pat
    k = pat.__class__
    if k is PatternVar:
        v = sub.get(pat.name)
        if v is None:
            raise ParseError(f"unbound pattern variable ?{pat.name} in rule template")
        return v
    if k is PatternSeq:
        raise BudgetExceeded(message=f"sequence hole ??{pat.name} not in arg position")
    out = []
    for a in pat.args:
        if a.__class__ is PatternSeq:
            seq = sub.get(a.name)
            if seq is None:
                raise ParseError(f"unbound sequence hole ??{a.name} in rule template")
            out.extend(seq)
        else:
            out.append(_inst_raw(a, sub))
    return T._intern_expr(pat.head, tuple(out))
