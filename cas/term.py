from fractions import Fraction
from fractions import Fraction as Fr


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
    __slots__ = ("name", "pred")

    def __init__(self, name, pred=None):
        self.name = name
        self.pred = pred
        self._h = _next_h()

    def __repr__(self):
        return f"?{self.name}" + (f"::{self.pred}" if self.pred else "")


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
EMPTY_SET = _SPECIALS.setdefault("EmptySet", Special("EmptySet"))   # 解集一等结构用

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


# 数学常数不在此处：一切具体常数由 library 包声明创建（library/constants.py）。
# 本层只有 Const 这一 ADT 变体，没有 π 也没有 i。


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


def PV(name, pred=None):
    t = _PATVARS.get((name, pred))
    if t is None:
        t = PatVar(name, pred)
        _PATVARS[(name, pred)] = t
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
        return (4, t.name, t.pred or "")
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



def _flatten_ac(head, args):
    """AC 头的句法折叠：同类嵌套拉平一层 + 确定性排序。

    纯表示规范，无数值折叠、无代数合并——标准形归函数结构提供。
    """
    flat = []
    for a in args:
        if isinstance(a, Expr) and a.head is head:
            flat.extend(a.args)
        else:
            flat.append(a)
    return sorted(flat)


# 每头规范化注册表（L5 扩展入口）：构造器 mk 对非 AC/Power 头应用。
# Plus/Times/Power 属 L0 环规范化，内建于 mk，不经此表。
NORM = {}


def register_norm(name, fn):
    NORM[name] = fn


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
    """驻留构造器，唯一入口。

    只做句法不变量：AC 头（Plus/Times/And/Or）拉平同类嵌套并确定性排序，
    其余头直接驻留。判等退化为指针比较。

    标准形职责已移交函数结构层（docs/cas_v3_arch.md 第五节），本层不再做：
    数值常量折叠、同类项合并、同底幂合并、i 的整数幂、e^a 到 Exp(a) 的
    改写、根式归一与落域坍缩、函数头特殊点折叠。以上分别属于 ℚ 算术、
    多项式机器、高斯域、图书馆命名约定与闸门链。
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
sinh = fn("Sinh")
cosh = fn("Cosh")
tanh = fn("Tanh")
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


def open_bound(b):
    """Bound -> (hint 符号, 体)：DB(0) 还原为 hint 符号（mk_bound 的逆，
    供惰性积分的体参与环运算/打印）。嵌套绑定按深度位移。"""
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
# 树遍历与重写工具（M6.7 拆分）：subst/instantiate/path 操作移居
# cas/termpath.py（对 term 只持模块引用，无导入环）；此处回接名字，
# `from cas.term import subst` 等既有导入面不变。
# ---------------------------------------------------------------------------

from cas.termpath import (  # noqa: E402
    _subst_raw, subst, _instantiate_raw, instantiate,
    free_vars, term_at, _bind_into, replace_at, all_paths, size,
)
