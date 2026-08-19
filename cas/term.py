from fractions import Fraction
from fractions import Fraction as Fr

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
    # 虚数单位整数幂：i^n 按 mod 4 折叠（纯符号，无近似）
    if b is IU and isinstance(e, Int):
        r = e.v % 4
        if r == 0:
            return ONE
        if r == 1:
            return IU
        if r == 2:
            return MONE
        return neg(IU)
    if (
        isinstance(e, Int)
        and isinstance(b, Expr)
        and b.head.name == "Power"
        and is_num(b.args[0])
        and num_val(b.args[0]) >= 0
        and isinstance(b.args[1], Rat)
    ):
        # (n^r)^k（n 非负数值）：指数相乘，结果为整数指数时精确折叠（如 (√2)^2 -> 2）
        new_exp = b.args[1].f * e.v
        if new_exp.denominator == 1:
            return N(num_val(b.args[0]) ** new_exp.numerator)
        return None
    if (
        isinstance(e, Int)
        and 0 < e.v <= 64
        and isinstance(b, Expr)
        and not isinstance(b, Special)
        and not (b.head.name == "Power" and isinstance(b.args[1], Rat))
        and all(_pure_numeric(a) for a in b.args)
    ):
        # 纯常数底的正整数幂（如 (-i)^2、(2i)^3）：乘开折叠，结果仍是纯常数；
        # 负指数不在此折叠（避免与倒数构造互递归）；有理指数底由上一分支处理。
        acc = ONE
        for _ in range(e.v):
            acc = mk(S("Times"), (acc, b))
        return acc
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


def _split_coeff(a):
    """加法项拆系数：a -> (系数: Fraction, 剩余因子 tuple)。"""
    if is_num(a):
        return num_val(a), ()
    if isinstance(a, Expr) and a.head.name == "Times":
        nums = [x for x in a.args if is_num(x)]
        rest = tuple(x for x in a.args if not is_num(x))
        if not nums:
            return Fr(1), rest
        acc = Fr(1)
        for x in nums:
            acc *= num_val(x)
        return acc, rest
    return Fr(1), (a,)


def _norm_plus(args):
    """Plus 环规范化：合并同类项（按剩余因子签名分组）。

    返回规范项；含 Special（Infinity 等）或无可归约时返回 None（由 mk 原样驻留）。
    """
    if any(isinstance(a, Special) for a in args):
        return None
    groups = {}
    const = Fr(0)
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
                out.append(mk(S("Times"), rest))
        elif len(rest) == 1:
            out.append(mk(S("Times"), (rest[0], N(c))))
        else:
            out.append(mk(S("Times"), tuple(rest) + (N(c),)))
    if not out:
        return ZERO
    if len(out) == 1:
        return out[0]
    if len(out) == len(args) and all(o is a for o, a in zip(sorted(out), args)):
        return None
    return mk(S("Plus"), tuple(out))


def _pure_numeric(t):
    """t 是否不含任何符号/洞（仅数值与常数，如 1+i）。头不计入（Sin 等由参数判定）。"""
    if isinstance(t, (Sym, PatVar, PatSeq)):
        return False
    if isinstance(t, Expr):
        return all(_pure_numeric(a) for a in t.args)
    if isinstance(t, Bound):
        return False
    return True


def _norm_times(args):
    """Times 环规范化：合并同底整数幂（x^a*x^b -> x^(a+b)，a,b 整数）、归一系数。

    generic 语义：x*x^-1 -> 1（与主流 CAS 一致）；定义域条件由 dom_condition 按需提取。
    非整数指数幂视为原子基底，不做指数算术（分支切割安全）。
    返回规范项；含 Special 或无可归约时返回 None。
    """
    if any(isinstance(a, Special) for a in args):
        return None
    if (
        any(isinstance(a, Expr) and a.head.name == "Plus" for a in args)
        and all(_pure_numeric(a) for a in args)
    ):
        # 纯常数乘积且含加法因子（如 (1+i)(1-i)）：分配展开并折叠；
        # 展开后因子不再含 Plus，不会重入此分支（终止性保证）。
        from cas.simplify import expand

        return expand(_intern_expr(S("Times"), tuple(args)))
    coeff = Fr(1)
    powers = {}
    for a in args:
        if is_num(a):
            coeff *= num_val(a)
            continue
        if isinstance(a, Expr) and a.head.name == "Power":
            b, e = a.args
            if isinstance(e, Int):
                key = b._h
                if key in powers:
                    powers[key][1] += e.v
                else:
                    powers[key] = [b, e.v]
                continue
        key = a._h
        if key in powers:
            powers[key][1] += 1
        else:
            powers[key] = [a, 1]
    if coeff == 0:
        return ZERO
    out = []
    for b, e in powers.values():
        if e == 0:
            continue
        if e == 1:
            out.append(b)
        else:
            out.append(mk(S("Power"), (b, N(e))))
    if coeff != 1 or not out:
        out.append(N(coeff))
    if len(out) == 1:
        return out[0]
    if len(out) == len(args) and all(o is a for o, a in zip(sorted(out), args)):
        return None
    return mk(S("Times"), tuple(out))


def _sqrt_fac_fold(b, e):
    """(数值与数值平方根的积)^偶数整数 -> 数值折叠。"""
    facs = []
    for a in b.args:
        if is_num(a):
            facs.append(N(num_val(a) ** e.v))
        elif (
            isinstance(a, Expr)
            and a.head.name == "Power"
            and isinstance(a.args[1], Rat)
            and a.args[1].f == Fr(1, 2)
            and is_num(a.args[0])
            and num_val(a.args[0]) >= 0
        ):
            facs.append(N(num_val(a.args[0]) ** (e.v // 2)))
        else:
            return None
    return times(*facs)


def _norm_power(args):
    """Power 规范化：x^1 -> x、x^0 -> 1、1^e -> 1、(x^i)^j -> x^(i*j)（i,j 整数）。

    非整数内层指数不合并（分支切割）；根式偶次幂折叠走 _sqrt_fac_fold。
    """
    b, e = args
    if e is ONE:
        return b
    if e is ZERO:
        return ONE
    if b is ONE:
        return ONE
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
        return mk(S("Power"), (b.args[0], N(b.args[1].v * e.v)))
    return None


# 每头规范化注册表（L5 扩展入口）：构造器 mk 对非 AC/Power 头应用。
# Plus/Times/Power 属 L0 环规范化，内建于 mk，不经此表。
NORM = {}


def register_norm(name, fn):
    NORM[name] = fn


def _norm_conjugate(args):
    """Conjugate 表示归并（实数域公理）：实常数/数值不变，i -> -i，
    对 Plus/Times/整数幂分配，双重共轭消去；其余形态驻留为名词。"""
    (a,) = args
    if a is IU:          # 必须先于 Const 检查（IU 本身是 Const）
        return neg(IU)
    if is_num(a) or isinstance(a, Const):
        return a
    if isinstance(a, Expr):
        n = a.head.name
        if n == "Conjugate":
            return a.args[0]
        if n == "Plus":
            return mk(S("Plus"), tuple(mk(S("Conjugate"), (x,)) for x in a.args))
        if n == "Times":
            return mk(S("Times"), tuple(mk(S("Conjugate"), (x,)) for x in a.args))
        if n == "Power" and isinstance(a.args[1], Int):
            return mk(S("Power"), (mk(S("Conjugate"), (a.args[0],)), a.args[1]))
    return None


register_norm("Conjugate", _norm_conjugate)


_SPEC_MOD = None


def _spec_lookup(name):
    """延迟导入 spec（避免 term <-> spec 循环），查函数注册表。"""
    global _SPEC_MOD
    if _SPEC_MOD is None:
        from cas import spec as _s

        _SPEC_MOD = _s
    return _SPEC_MOD.get(name)


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
    """唯一的规范化构造器：构造即规范化。

    AC 头（Plus/Times/And/Or）：flatten + 全序 + 常量折叠；
    Plus/Times 追加环规范化（同类项合并 / 同底整数幂合并，generic 语义）；
    Power：数值折叠 + 幂规范化；其余头走 NORM 注册表。
    模式（含 ?x/??x 洞）同样经此构造：规范化是语义保持的（目标项同样规范化）。
    """
    name = head.name if isinstance(head, Sym) else None
    if name in AC:
        if name in BOOL_HEADS:
            r = _fold_bool_ac(head, list(args))
            if isinstance(r, list):
                return _intern_expr(head, tuple(r))
            return r
        r = _fold_ac(head, list(args))
        if not isinstance(r, list):
            return r
        n = _norm_times(r) if name == "Times" else _norm_plus(r)
        if n is not None:
            return n
        return _intern_expr(head, tuple(r))
    if name == "Power":
        b, e = args
        r = _fold_power(b, e)
        if r is not None:
            return r
        r = _norm_power((b, e))
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
    if name in _CMP_HEADS:
        # 比较头参数递归规范化（parser 的 = 等直走 _intern_expr，此处补齐），
        # 保证账本事实与表达式共享同一规范形（指针判等/替换依赖它）。
        return _intern_expr(head, tuple(mk(a.head, a.args) if isinstance(a, Expr) else a for a in args))
    if name == "Quote":
        (a,) = args
        if isinstance(a, Expr) and a.head is S("Quote"):
            return a
        return _intern_expr(head, args)
    args = tuple(args)
    # FunctionSpec 特殊点折叠（构造即规范化；洞参数不折叠，模式语义保持）
    sp = _spec_lookup(name)
    if sp is not None and sp.special:
        a0 = args[0]
        if not isinstance(a0, (PatVar, PatSeq)):
            r = sp.special.get(a0)
            if r is not None:
                return r
    norm = NORM.get(name)
    if norm is not None:
        r = norm(args)
        if r is not None:
            return r
    return _intern_expr(head, args)


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


def subst(t, mapping):
    """替换（显式工作栈后序重建，深表达式不触及 Python 递归上限）。"""
    if not mapping:
        return t
    # 显式栈后序遍历；Bound 的 body 必须始终下行（内部自由变量需替换且防捕获）
    order = []
    stack = [t]
    while stack:
        u = stack.pop()
        order.append(u)
        if isinstance(u, Expr):
            if u in mapping:
                continue  # 命中替换表的子树不再下行
            stack.extend(u.args)
        elif isinstance(u, Bound):
            stack.append(u.body)
    val = {}
    for u in reversed(order):
        hit = mapping.get(u)
        if hit is not None:
            val[u] = hit
        elif isinstance(u, Expr):
            val[u] = mk(u.head, tuple(val[a] for a in u.args))
        elif isinstance(u, Bound):
            val[u] = _mk_bound_canon(u.hint, val[u.body])
        else:
            val[u] = u
    return val[t]


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
