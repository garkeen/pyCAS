from fractions import Fraction as Fr

from cas import term as T
from cas.term import S, N, Expr, Int, Sym, Rat
from cas.errors import BudgetExceeded

WEIGHTS = {"Power": 2, "Exp": 2, "Log": 2}
DEFAULT_W = 1

_REGISTRY = {}


def register(name, fn):
    _REGISTRY[name] = fn


def cost(t):
    if isinstance(t, Expr):
        w = WEIGHTS.get(t.head.name, DEFAULT_W)
        return w + sum(cost(a) for a in t.args)
    if isinstance(t, T.Bound):
        return 1 + cost(t.body)
    return 1


def _split_coeff(a):
    if T.is_num(a):
        return T.num_val(a), ()
    if isinstance(a, Expr) and a.head.name == "Times":
        nums = [x for x in a.args if T.is_num(x)]
        rest = tuple(x for x in a.args if not T.is_num(x))
        if len(nums) == 1:
            return T.num_val(nums[0]), rest
        if not nums:
            return 1, a.args
        acc = 1
        for x in nums:
            acc *= T.num_val(x)
        return acc, rest
    return 1, (a,)


def _norm_plus(args):
    groups = {}
    const = 0
    for a in args:
        c, rest = _split_coeff(a)
        if not rest:
            const += c
            continue
        key = tuple(x._h for x in rest)
        if key in groups:
            c0, rest0 = groups[key]
            groups[key] = (c0 + c, rest0)
        else:
            groups[key] = (c, rest)
    out = []
    if const != 0:
        out.append(N(const))
    for c, rest in groups.values():
        if c == 0:
            continue
        if c == 1:
            if len(rest) == 1:
                out.append(rest[0])
            else:
                out.append(T.mk(S("Times"), rest))
        elif len(rest) == 1:
            out.append(T.mk(S("Times"), (rest[0], N(c))))
        else:
            out.append(T.mk(S("Times"), tuple(rest) + (N(c),)))
    if not out:
        return T.ZERO
    if len(out) == 1:
        return out[0]
    return T.mk(S("Plus"), tuple(out))


def _norm_times(args):
    if any(isinstance(a, T.Special) for a in args):
        return None
    neg_sym = None
    for a in args:
        if isinstance(a, Expr) and a.head.name == "Power":
            b, e = a.args
            if not T.is_num(b) and isinstance(e, Int) and e.v < 0:
                neg_sym = b._h
                break
    coeff = 1
    plain = []
    powers = {}
    for a in args:
        if T.is_num(a):
            coeff *= T.num_val(a)
            continue
        if isinstance(a, Expr) and a.head.name == "Power":
            b, e = a.args
            if isinstance(e, Int):
                key = b._h
                if key in powers:
                    powers[key] = (powers[key][0], powers[key][1] + e.v)
                else:
                    powers[key] = (b, e.v)
                continue
        key = a._h
        if key in powers:
            powers[key] = (powers[key][0], powers[key][1] + 1)
        else:
            powers[key] = (a, 1)
        plain.append(key)
    if neg_sym is not None and (
        neg_sym not in powers or powers[neg_sym][1] < 0
    ):
        return None
    out = []
    seen = set()
    for a in args:
        if T.is_num(a):
            continue
        if isinstance(a, Expr) and a.head.name == "Power" and isinstance(a.args[1], Int):
            continue
        if a._h in powers and a._h not in seen:
            seen.add(a._h)
    for key, (b, e) in powers.items():
        if e == 0:
            continue
        if e == 1:
            out.append(b)
        else:
            out.append(T.mk(S("Power"), (b, N(e))))
    if coeff == 0:
        return T.ZERO
    if coeff != 1 or not out:
        out.append(N(coeff))
    if len(out) == 1:
        return out[0]
    return T.mk(S("Times"), tuple(out))


def _sqrt_fac_fold(b, e):
    facs = []
    for a in b.args:
        if T.is_num(a):
            facs.append(N(T.num_val(a) ** e.v))
        elif (
            isinstance(a, Expr)
            and a.head.name == "Power"
            and isinstance(a.args[1], Rat)
            and a.args[1].f == Fr(1, 2)
            and T.is_num(a.args[0])
            and T.num_val(a.args[0]) >= 0
        ):
            facs.append(N(T.num_val(a.args[0]) ** (e.v // 2)))
        else:
            return None
    return T.times(*facs)


def _norm_power(args):
    b, e = args
    if e is T.ONE:
        return b
    if e is T.ZERO:
        return T.ONE
    if b is T.ONE:
        return T.ONE
    if (
        isinstance(e, Int)
        and e.v % 2 == 0
        and isinstance(b, Expr)
        and b.head.name == "Times"
    ):
        r = _sqrt_fac_fold(b, e)
        if r is not None:
            return r
    if (
        isinstance(b, Expr)
        and b.head.name == "Power"
        and isinstance(e, Int)
        and isinstance(b.args[1], Int)
    ):
        return T.mk(S("Power"), (b.args[0], N(b.args[1].v * e.v)))
    return None


register("Plus", _norm_plus)
register("Times", _norm_times)
register("Power", _norm_power)


def _mul_expand(a, b):
    if isinstance(a, Expr) and a.head.name == "Plus":
        return T.plus(*[_mul_expand(x, b) for x in a.args])
    if isinstance(b, Expr) and b.head.name == "Plus":
        return T.plus(*[_mul_expand(a, y) for y in b.args])
    return T.times(a, b)


def expand(t):
    if isinstance(t, Expr):
        name = t.head.name
        if name == "Plus":
            return T.plus(*[expand(a) for a in t.args])
        if name == "Times":
            acc = T.ONE
            for a in t.args:
                acc = _mul_expand(acc, expand(a))
            return acc
        if name == "Power":
            b, e = t.args
            if isinstance(e, Int) and e.v >= 2:
                base = expand(b)
                acc = base
                for _ in range(e.v - 1):
                    acc = _mul_expand(acc, base)
                return acc
            if isinstance(e, Int) and e.v == 1:
                return expand(b)
            if isinstance(e, Int) and e.v == 0:
                return T.ONE
            return t
    return t


def simplify(t, budget=100000):
    spent = [budget]

    def rec(x):
        spent[0] -= 1
        if spent[0] < 0:
            raise BudgetExceeded()
        if isinstance(x, Expr):
            args = [rec(a) for a in x.args]
            t2 = T.mk(x.head, tuple(args))
            if not isinstance(t2, Expr):
                return t2
            h = _REGISTRY.get(x.head.name)
            if h:
                r = h(t2.args)
                if r is not None:
                    return r
            return t2
        if isinstance(x, T.Bound):
            return T.mk_bound(x.hint, rec(x.body))
        return x

    prev = t
    for _ in range(20):
        nxt = rec(prev)
        if nxt is prev:
            return prev
        prev = nxt
    return prev
