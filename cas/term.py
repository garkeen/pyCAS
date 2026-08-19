from fractions import Fraction

from cas.errors import BudgetExceeded

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

    def __repr__(self):
        return self.name


class PatVar(Term):
    __slots__ = ("name",)

    def __init__(self, name):
        self.name = name
        self._h = _next_h()

    def __repr__(self):
        return f"?{self.name}"


class PatSeq(Term):
    __slots__ = ("name",)

    def __init__(self, name):
        self.name = name
        self._h = _next_h()

    def __repr__(self):
        return f"??{self.name}"


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
_PATVARS = {}
_PATSEQS = {}
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


PI = C("pi")
E = C("e")
IU = C("i")
GAMMA = C("gamma")


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


def PV(name):
    t = _PATVARS.get(name)
    if t is None:
        t = PatVar(name)
        _PATVARS[name] = t
    return t


def PS(name):
    t = _PATSEQS.get(name)
    if t is None:
        t = PatSeq(name)
        _PATSEQS[name] = t
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
    if k is PatVar:
        return (4, t.name)
    if k is PatSeq:
        return (5, t.name)
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


def _has_special(args):
    return any(isinstance(a, Special) for a in args)


def _fold_ac(head, args):
    is_times = head.name == "Times"
    flat = []
    for a in args:
        if isinstance(a, Expr) and a.head is head:
            flat.extend(a.args)
        else:
            flat.append(a)
    if UND in flat:
        return UND
    special = _has_special(flat)
    if special:
        nums = []
        rest = []
        for a in flat:
            if is_num(a):
                nums.append(a)
            else:
                rest.append(a)
        if not rest:
            return _fold_num_only(head, nums)
        flat = sorted(rest + nums)
    else:
        acc = None
        rest = []
        for a in flat:
            if is_num(a):
                if acc is None:
                    acc = num_val(a)
                else:
                    acc = acc + num_val(a) if not is_times else acc * num_val(a)
            else:
                rest.append(a)
        if is_times:
            if acc == 0:
                return ZERO
            if acc is not None and acc != 1:
                rest.append(N(acc))
        else:
            if acc is not None and acc != 0:
                rest.append(N(acc))
        flat = sorted(rest)
    if not flat:
        return ONE if is_times else ZERO
    if len(flat) == 1:
        return flat[0]
    return flat


def _fold_num_only(head, nums):
    if head.name == "Times":
        acc = Fraction(1)
        for n in nums:
            acc *= num_val(n)
        return N(acc)
    acc = Fraction(0)
    for n in nums:
        acc += num_val(n)
    return N(acc)


def _fold_bool_ac(head, args):
    is_or = head.name == "Or"
    flat = []
    for a in args:
        if isinstance(a, Expr) and a.head is head:
            flat.extend(a.args)
        else:
            flat.append(a)
    seen = []
    sid = set()
    for a in flat:
        if a is (TRUE if is_or else FALSE):
            return TRUE if is_or else FALSE
        if a is (FALSE if is_or else TRUE):
            continue
        if a._h in sid:
            continue
        sid.add(a._h)
        seen.append(a)
    if not seen:
        return FALSE if is_or else TRUE
    if len(seen) == 1:
        return seen[0]
    return sorted(seen)


def _fold_power(b, e):
    if UND in (b, e) or INFINITY in (b, e):
        return UND
    if is_num(b) and isinstance(e, Int):
        bv = num_val(b)
        ev = e.v
        if ev == 0:
            if bv == 0:
                return UND
            return ONE
        if ev > 0:
            if abs(ev) > 100000:
                return None
            return N(bv**ev)
        if bv == 0:
            return UND
        return N(Fraction(1) / (bv ** (-ev)))
    if (
        isinstance(e, Int)
        and isinstance(b, Expr)
        and b.head.name == "Power"
        and isinstance(b.args[1], Rat)
        and b.args[1].f == Fraction(1, 2)
        and is_num(b.args[0])
        and num_val(b.args[0]) >= 0
        and e.v % 2 == 0
    ):
        return N(num_val(b.args[0]) ** (e.v // 2))
    return None


def _intern_expr(head, args):
    key = (head._h, tuple(a._h for a in args))
    t = _EXPRS.get(key)
    if t is None:
        h = _next_h()
        t = Expr(head, args, h)
        _EXPRS[key] = t
    return t


def mk(head, args):
    name = head.name if isinstance(head, Sym) else None
    if name in AC:
        if name in BOOL_HEADS:
            r = _fold_bool_ac(head, list(args))
            if isinstance(r, list):
                return _intern_expr(head, tuple(r))
            return r
        r = _fold_ac(head, list(args))
        if isinstance(r, list):
            return _intern_expr(head, tuple(r))
        return r
    if name == "Power":
        b, e = args
        r = _fold_power(b, e)
        if r is not None:
            return r
        return _intern_expr(head, tuple(args))
    if name == "Not":
        (a,) = args
        if isinstance(a, BVal):
            return TRUE if a is FALSE else FALSE
        if isinstance(a, Expr) and a.head is S("Not"):
            return a.args[0]
        return _intern_expr(head, args)
    if name == "Quote":
        (a,) = args
        if isinstance(a, Expr) and a.head is S("Quote"):
            return a
        return _intern_expr(head, args)
    return _intern_expr(head, tuple(args))


def fn(name):
    h = S(name)

    def build(*args):
        return mk(h, args)

    return build


plus = fn("Plus")
times = fn("Times")
pw = fn("Power")
sin = fn("Sin")
cos = fn("Cos")
tan = fn("Tan")
atan = fn("Atan")
exp = fn("Exp")
log = fn("Log")
abs_ = fn("Abs")


def neg(a):
    return times(MONE, a)


def div(a, b):
    return times(a, pw(b, MONE))


def sqrt(a):
    return pw(a, N(Fraction(1, 2)))


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


def subst(t, mapping):
    if not mapping:
        return t
    if isinstance(t, Sym):
        return mapping.get(t, t)
    if isinstance(t, Expr):
        return mk(t.head, tuple(subst(a, mapping) for a in t.args))
    if isinstance(t, Bound):
        return _mk_bound_canon(t.hint, subst(t.body, mapping))
    return t


def instantiate(t, sub):
    if isinstance(t, PatVar):
        return sub.get(t.name, t)
    if isinstance(t, PatSeq):
        raise BudgetExceeded(message=f"sequence hole ?{t.name} not in arg position")
    if isinstance(t, Expr):
        out = []
        for a in t.args:
            if isinstance(a, PatSeq):
                seq = sub.get(a.name)
                if seq is None:
                    out.append(a)
                else:
                    out.extend(seq)
            else:
                out.append(instantiate(a, sub))
        return mk(t.head, tuple(out))
    if isinstance(t, Bound):
        return _mk_bound_canon(t.hint, instantiate(t.body, sub))
    return t


def free_vars(t, acc=None):
    if acc is None:
        acc = set()
    if isinstance(t, Sym):
        acc.add(t)
    elif isinstance(t, Expr):
        for a in t.args:
            free_vars(a, acc)
    elif isinstance(t, Bound):
        free_vars(t.body, acc)
    return acc


def term_at(t, path):
    for i in path:
        if isinstance(t, Expr):
            t = t.args[i]
        elif isinstance(t, Bound):
            t = t.body
        else:
            raise IndexError(path)
    return t


def replace_at(t, path, v):
    if not path:
        return v
    i = path[0]
    if isinstance(t, Expr):
        args = list(t.args)
        args[i] = replace_at(args[i], path[1:], v)
        return mk(t.head, tuple(args))
    if isinstance(t, Bound):
        return mk_bound(t.hint, replace_at(t.body, path[1:], v))
    raise IndexError(path)


def all_paths(t, base=()):
    yield base
    if isinstance(t, Expr):
        for i, a in enumerate(t.args):
            yield from all_paths(a, base + (i,))
    elif isinstance(t, Bound):
        yield from all_paths(t.body, base + (0,))


def size(t):
    if isinstance(t, Expr):
        return 1 + sum(size(a) for a in t.args)
    if isinstance(t, Bound):
        return 1 + size(t.body)
    return 1
