from functools import partial

from fractions import Fraction


_hc = 0


def _next_h():
    global _hc
    _hc += 1
    return _hc


class Term:
    __slots__ = ("_h",)

    def __hash__(self):
        return self._h

    def __eq__(self, other):
        return self is other

    def __ne__(self, other):
        return self is not other

    def __lt__(self, other):
        return sort_key(self) < sort_key(other)


class Sym(Term):
    __slots__ = ("name",)

    def __init__(self, name):
        self.name = name
        self._h = _next_h()

    def __repr__(self):
        return self.name


class Const(Term):
    __slots__ = ("name",)

    def __init__(self, name):
        self.name = name
        self._h = _next_h()

    def __repr__(self):
        return self.name


class DB(Term):
    __slots__ = ("i",)

    def __init__(self, i):
        self.i = i
        self._h = _next_h()

    def __repr__(self):
        return f"#{self.i}"


class BVal(Term):
    __slots__ = ("val",)

    def __init__(self, val):
        self.val = val
        self._h = _next_h()

    def __repr__(self):
        return "True" if self.val else "False"


class Int(Term):
    __slots__ = ("v",)

    def __init__(self, v):
        self.v = v
        self._h = _next_h()

    def __repr__(self):
        return str(self.v)


class Rat(Term):
    __slots__ = ("f",)

    def __init__(self, f):
        self.f = f
        self._h = _next_h()

    def __repr__(self):
        return f"{self.f.numerator}/{self.f.denominator}"


class Special(Term):
    __slots__ = ("name",)

    def __init__(self, name):
        self.name = name
        self._h = _next_h()


class Expr(Term):
    __slots__ = ("head", "args")

    def __init__(self, head, args, h):
        self.head = head
        self.args = args
        self._h = h

    def __repr__(self):
        if self.head.name in _INFIX:
            op = _INFIX[self.head.name]
            return "(" + f" {op} ".join(repr(a) for a in self.args) + ")"
        return f"{self.head.name}{tuple(repr(a) for a in self.args)}"


class Bound(Term):
    __slots__ = ("hint", "body")

    def __init__(self, hint, body, h):
        self.hint = hint
        self.body = body
        self._h = h

    def __repr__(self):
        return f"bound<{self.hint}>({self.body!r})"


_INFIX = {
    "Plus": "+",
    "Times": "*",
    "Power": "^",
    "Eq": "==",
    "Ne": "!=",
    "Lt": "<",
    "Le": "<=",
    "Gt": ">",
    "Ge": ">=",
    "And": "&&",
    "Or": "||",
}

_SYMS = {}
_CONSTS = {}
_NUMS = {}
_SPECIALS = {}
_EXPRS = {}
_BOUNDS = {}
_DBS = {}


def DB_(i):
    t = _DBS.get(i)
    if t is None:
        t = DB(i)
        _DBS[i] = t
    return t


TRUE = BVal(True)
FALSE = BVal(False)
UND = _SPECIALS.setdefault("Undefined", Special("Undefined"))
INFINITY = _SPECIALS.setdefault("Infinity", Special("Infinity"))
EMPTY_SET = _SPECIALS.setdefault("EmptySet", Special("EmptySet"))   # solution sets

AC = {"Plus", "Times", "And", "Or"}
BOOL_HEADS = {"And", "Or", "Not"}


def S(name):
    t = _SYMS.get(name)
    if t is None:
        t = Sym(name)
        _SYMS[name] = t
    return t


def C(name):
    t = _CONSTS.get(name)
    if t is None:
        t = Const(name)
        _CONSTS[name] = t
    return t


# No mathematical constants live here: every concrete constant is declared by
# math/elementary and installed by bootstrap. This layer only has the Const ADT
# variant; there is no pi and no i here.


def N(v):
    if isinstance(v, int):
        t = _NUMS.get(v)
        if t is None:
            t = Int(v)
            _NUMS[v] = t
        return t
    f = Fraction(v)
    if f.denominator == 1:
        return N(f.numerator)
    t = _NUMS.get(f)
    if t is None:
        t = Rat(f)
        _NUMS[f] = t
    return t


def SP(name):
    t = _SPECIALS.get(name)
    if t is None:
        t = Special(name)
        _SPECIALS[name] = t
    return t


def is_num(t):
    return isinstance(t, (Int, Rat))


def num_val(t):
    if isinstance(t, Int):
        return Fraction(t.v)
    return t.f


def sign_num(t):
    v = num_val(t)
    return (v > 0) - (v < 0)


ZERO = N(0)
ONE = N(1)
TWO = N(2)
MONE = N(-1)


def sort_key(t):
    k = t.__class__
    if k is Sym:
        return (0, t.name)
    if k is Const:
        return (1, t.name)
    if k is BVal:
        return (2, 0 if t.val else 1)
    if k is DB:
        return (3, t.i)
    if k is Int:
        return (25, Fraction(t.v))
    if k is Rat:
        return (25, t.f)
    if k is Special:
        return (8, t.name)
    if k is Expr:
        return (20, sort_key(t.head), tuple(sort_key(a) for a in t.args))
    if k is Bound:
        return (21, sort_key(t.body))
    return (22, repr(t))



def _flatten_ac(head, args):
    """Flatten one level of same-head nesting, then sort deterministically.

    Representation only: no numeric folding, no algebraic merging. The
    canonical form is supplied by the function-structure layer.
    """
    flat = []
    for a in args:
        if isinstance(a, Expr) and a.head is head:
            flat.extend(a.args)
        else:
            flat.append(a)
    return sorted(flat)


def _fold_bool_ac(head, args):
    """Canonical representation for And/Or: flatten, dedupe by pointer,
    absorb identity and annihilator elements.

    This is representation normalization only, not a decision procedure:
    the canonical form under associativity/commutativity/idempotence
    (empty conjunction = true, empty disjunction = false, identity
    absorption, annihilator absorption) is what makes interned equality a
    pointer comparison, so it belongs to the syntax layer. Complementary-pair
    collapse (`c or not c -> true`) is deliberately NOT done here: that
    decides whether a proposition is a tautology and belongs to the branch
    coverage checker, which keeps verification independent of construction.
    """
    name = head.name
    flat = []
    for a in args:
        if isinstance(a, Expr) and a.head is head:
            flat.extend(a.args)
        else:
            flat.append(a)
    out, seen = [], set()
    for a in flat:
        if isinstance(a, BVal):
            if (name == "And" and not a.val) or (name == "Or" and a.val):
                return a                       # annihilator: False in And, True in Or
            continue                           # identity element is absorbed
        if a._h in seen:
            continue
        seen.add(a._h)
        out.append(a)
    if not out:
        return TRUE if name == "And" else FALSE
    if len(out) == 1:
        return out[0]
    return sorted(out)


def _intern_expr(head, args):
    key = (head._h, tuple(a._h for a in args))
    t = _EXPRS.get(key)
    if t is None:
        h = _next_h()
        t = Expr(head, args, h)
        _EXPRS[key] = t
    return t


_CMP_HEADS = {"Eq", "Ne", "Lt", "Le", "Gt", "Ge"}


def mk(head, args):
    """The single interned constructor.

    Representation normalization only: AC heads (Plus/Times/And/Or) get
    same-head flattening, deterministic sorting, idempotent dedupe and
    identity/annihilator absorption; every other head is interned as given.
    Equality then reduces to a pointer comparison.

    No semantics are decided here: tautology/contradiction (such as
    `c or not c`) is not collapsed at construction time, it is decided by the
    corresponding checker.

    Canonical-form duties live in the function-structure layer, not here:
    numeric constant folding, like-term collection, same-base power merging,
    integer powers of i, rewriting e^a to Exp(a), radical normalization and
    domain collapse, special-point folding of function heads. Those belong to
    rational arithmetic, the polynomial machine, the Gaussian domain, the
    declaration naming convention and the gate chain respectively.
    """
    name = head.name if isinstance(head, Sym) else None
    if name in AC:
        if name in BOOL_HEADS:
            r = _fold_bool_ac(head, list(args))
            if isinstance(r, list):
                return _intern_expr(head, tuple(r))
            return r
        return _intern_expr(head, tuple(_flatten_ac(head, list(args))))
    return _intern_expr(head, tuple(args))


def call(name, *args):
    """Generic constructor for a call of any head; it knows no head by name.

    Elementary functions (Sin/Exp/Log/...) are constructed by the declaration
    layer, the only place that knows those heads exist. The syntax layer knows
    structural heads only: Plus/Times/Power are the ring signature and And/Or
    are boolean structure, so only their constructors are exposed here, built
    on this one generic entry point.
    """
    return mk(S(name), args)


# Structural-head constructors: ring signature and boolean structure.
plus = partial(call, "Plus")
times = partial(call, "Times")
pw = partial(call, "Power")


def neg(a):
    return times(MONE, a)


def div(a, b):
    return times(a, pw(b, MONE))


def eq(a, b):
    return mk(S("Eq"), (a, b))


def lt(a, b):
    return mk(S("Lt"), (a, b))


def le(a, b):
    return mk(S("Le"), (a, b))


def gt(a, b):
    return mk(S("Gt"), (a, b))


def ge(a, b):
    return mk(S("Ge"), (a, b))


def ne(a, b):
    return mk(S("Ne"), (a, b))


def and_(*a):
    return mk(S("And"), a)


def implies(a, b):
    """The canonical implication term, used wherever a guarded promotion
    `C => G` is built."""
    return mk(S("Implies"), (a, b))


def is_eq(t) -> bool:
    """True if `t` is an equation-shaped call (head `Eq`). A pure shape test,
    hence it belongs to the syntax layer."""
    return isinstance(t, Expr) and t.head.name == "Eq"


def or_(*a):
    return mk(S("Or"), a)


def not_(a):
    return mk(S("Not"), (a,))


def quote(a):
    return mk(S("Quote"), (a,))


def _shift(t, d, cutoff):
    if isinstance(t, DB):
        if t.i >= cutoff:
            return DB_(t.i + d)
        return t
    if isinstance(t, Expr):
        return mk(t.head, tuple(_shift(a, d, cutoff) for a in t.args))
    if isinstance(t, Bound):
        return mk_bound(t.hint, _shift(t.body, d, cutoff + 1))
    return t


def _abstract(t, var, depth):
    if isinstance(t, Sym):
        if t is var:
            return DB_(depth)
        return t
    if isinstance(t, DB):
        return DB_(t.i + 1) if t.i >= depth else t
    if isinstance(t, Expr):
        return mk(t.head, tuple(_abstract(a, var, depth) for a in t.args))
    if isinstance(t, Bound):
        return mk_bound(t.hint, _abstract(t.body, var, depth + 1))
    return t


def _mk_bound_canon(hint, cbody):
    key = cbody._h
    t = _BOUNDS.get(key)
    if t is None:
        h = _next_h()
        t = Bound(hint, cbody, h)
        _BOUNDS[key] = t
    return t


def mk_bound(var_hint, body, var=None):
    if var is None:
        var = S(var_hint) if isinstance(var_hint, str) else var_hint
    hint = var.name if isinstance(var, Sym) else str(var_hint)
    return _mk_bound_canon(hint, _abstract(body, var, 0))


def open_bound(b):
    """Bound -> (hint symbol, body): restore DB(0) to the hint symbol, the
    inverse of mk_bound. Nested binders are shifted by depth."""
    var = S(b.hint)
    return var, _lift(b.body, var, 0)


def _lift(t, var, depth):
    if isinstance(t, DB):
        return var if t.i == depth else t
    if isinstance(t, Expr):
        args = tuple(_lift(a, var, depth) for a in t.args)
        if all(a is b for a, b in zip(args, t.args)):
            return t
        return mk(t.head, args)
    if isinstance(t, Bound):
        nb = _lift(t.body, var, depth + 1)
        return t if nb is t.body else _mk_bound_canon(t.hint, nb)
    return t


# ---------------------------------------------------------------------------
# Tree traversal and rewriting live in cas/syntax/termpath.py. Names are
# re-exported lazily here so `from cas.syntax.term import subst` keeps working.
# Term-level instantiation does not exist (the term layer has no holes);
# instantiation lives with the pattern language in cas/syntax/pattern.py.
#
# The re-export uses a PEP 562 module __getattr__ instead of an import at the
# bottom: termpath imports `cas.syntax.term` at its top, so importing termpath
# back here would hit a half-initialized term module and raise ImportError.
# Lazy resolution keeps both import directions independent.
# ---------------------------------------------------------------------------

_TERMPATH_REEXPORT = frozenset((
    "_subst_raw", "subst",
    "free_vars", "term_at", "_bind_into", "replace_at", "all_paths",
))


def __getattr__(name):
    """Lazily re-export names from cas/syntax/termpath (PEP 562).

    Called only when normal attribute lookup fails, so term's own definitions
    take precedence; unknown names still raise AttributeError instead of being
    swallowed.
    """
    if name in _TERMPATH_REEXPORT:
        from cas.syntax import termpath
        return getattr(termpath, name)
    raise AttributeError(f"module {__name__!r} has no attribute {name!r}")
