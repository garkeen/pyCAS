from enum import Enum

from cas import term as T
from cas.term import S, N, PI, E
from cas.domain import R, Q, Z, C, DEFAULT_DOMAIN, domain_of


class T3(Enum):
    YES = "YES"
    NO = "NO"
    UNKNOWN = "UNKNOWN"


def and3(a, b):
    if a is T3.NO or b is T3.NO:
        return T3.NO
    if a is T3.YES and b is T3.YES:
        return T3.YES
    return T3.UNKNOWN


def or3(a, b):
    if a is T3.YES or b is T3.YES:
        return T3.YES
    if a is T3.NO and b is T3.NO:
        return T3.NO
    return T3.UNKNOWN


def not3(a):
    if a is T3.YES:
        return T3.NO
    if a is T3.NO:
        return T3.YES
    return T3.UNKNOWN


_NEG = {
    "Gt": ("Le", False),
    "Ge": ("Lt", False),
    "Lt": ("Ge", False),
    "Le": ("Gt", False),
    "Eq": ("Ne", False),
    "Ne": ("Eq", False),
}


def negate(f):
    if isinstance(f, T.Expr) and f.head.name in _NEG:
        name, swap = _NEG[f.head.name]
        a, b = f.args
        if swap:
            a, b = b, a
        return T.mk(S(name), (a, b))
    if isinstance(f, T.Expr) and f.head.name == "Not":
        return f.args[0]
    return T.mk(S("Not"), (f,))


_CMP = ("Lt", "Le", "Gt", "Ge", "Eq", "Ne")
_CMP_INV = {"Lt": "Gt", "Gt": "Lt", "Le": "Ge", "Ge": "Le"}


def _cmp_numeric(op, a, b):
    av = T.num_val(a) if T.is_num(a) else None
    bv = T.num_val(b) if T.is_num(b) else None
    if av is None or bv is None:
        return None
    if op == "Lt":
        r = av < bv
    elif op == "Le":
        r = av <= bv
    elif op == "Gt":
        r = av > bv
    elif op == "Ge":
        r = av >= bv
    elif op == "Eq":
        r = av == bv
    else:
        r = av != bv
    return T3.YES if r else T3.NO


def _same(op, a, b):
    if a is not b:
        return None
    if op in ("Eq", "Le", "Ge"):
        return T3.YES
    return T3.NO


def _poly_eq_check(a, b):
    # TODO: 多项式机器（第四层公共算法机器）重建后恢复此判定
    return None


def _facts_lookup(fact, ctx):
    for e in ctx.entries:
        f = e.fact
        if f is fact:
            return T3.YES
        if f is negate(fact):
            return T3.NO
        if isinstance(f, T.Expr) and isinstance(fact, T.Expr):
            if f.head.name in _CMP_INV and fact.head.name in _CMP_INV:
                if (
                    f.head.name == _CMP_INV[fact.head.name]
                    and f.args[0] is fact.args[1]
                    and f.args[1] is fact.args[0]
                ):
                    return T3.YES
    return None


def _chain_query(op, a, b, ctx):
    """序链 BFS：账本不等式建边，传递闭包回答 a<b 型查询。

    数值界推理（x>2 -> x+1>3）与等式代入由 _interval 区间通道负责，此处只走图边。
    """
    adj = {}
    strict = op in ("Lt", "Gt")
    want = (a, b)
    if op in ("Gt", "Ge"):
        want = (b, a)
    for e in ctx.entries:
        f = e.fact
        if isinstance(f, T.Expr) and f.head.name in ("Lt", "Le", "Gt", "Ge"):
            opf = f.head.name
            u, v = f.args
            if opf in ("Gt", "Ge"):
                u, v = v, u
                opf = "Lt" if opf == "Gt" else "Le"
            adj.setdefault(u, []).append((v, opf == "Lt"))
    if a is b:
        return T3.YES if op in ("Le", "Ge", "Eq") else T3.NO
    from collections import deque

    start, goal = want
    q = deque([(start, False)])
    seen = {start._h}
    while q:
        cur, ever_strict = q.popleft()
        for nxt, st in adj.get(cur, ()):
            ns = ever_strict or st
            if nxt is goal:
                if not strict or ns:
                    return T3.YES
            key = (nxt._h, ns)
            if nxt._h not in seen or (nxt._h, False) in seen and ns:
                seen.add(key)
                q.append((nxt, ns))
    return None


def _interval(t, ctx, seen=None, depth=0):
    """数值区间传播：(lo, hi, lo_strict, hi_strict)，端点可为 None（无界）。

    来源：数值原子 / 常数公理界 / 账本数值界直查 / 账本等式代入（递归） /
    Plus 求和 / 数值标量 Times 缩放 / 偶次幂与 Abs 非负。
    只读 term + 账本，不回调 decide（防循环）。无任何信息时返回 None。
    """
    from fractions import Fraction as Fr

    if T.is_num(t):
        v = T.num_val(t)
        return (v, v, False, False)
    lb = _CONST_BOUNDS.get(id(t))
    if lb is not None:
        return (Fr(lb[0]), Fr(lb[1]), True, True)
    if depth > 8:
        return None
    if seen is None:
        seen = set()
    if t._h in seen:
        return None
    seen.add(t._h)
    lo = hi = None
    los = his = False
    is_int = False

    def tighten(nlo, nlos, nhi, nhis):
        nonlocal lo, hi, los, his
        if nlo is not None and (lo is None or nlo > lo or (nlo == lo and nlos)):
            lo, los = nlo, nlos
        if nhi is not None and (hi is None or nhi < hi or (nhi == hi and nhis)):
            hi, his = nhi, nhis

    for e in ctx.entries:
        f = e.fact
        if not isinstance(f, T.Expr):
            continue
        n = f.head.name
        if n == "Attr" and f.args[0] is t and f.args[1].name == "integer":
            is_int = True
            continue
        if n in ("Lt", "Le", "Gt", "Ge"):
            u, v = f.args
            if u is t and T.is_num(v):
                bv = T.num_val(v)
                if n == "Lt":
                    tighten(None, False, bv, True)
                elif n == "Le":
                    tighten(None, False, bv, False)
                elif n == "Gt":
                    tighten(bv, True, None, False)
                else:
                    tighten(bv, False, None, False)
            elif v is t and T.is_num(u):
                bv = T.num_val(u)
                if n == "Lt":
                    tighten(bv, True, None, False)
                elif n == "Le":
                    tighten(bv, False, None, False)
                elif n == "Gt":
                    tighten(None, False, bv, True)
                else:
                    tighten(None, False, bv, False)
        elif n == "Eq":
            u, v = f.args
            o = v if u is t else (u if v is t else None)
            if o is not None and o is not t:
                if T.is_num(o):
                    # 常数等式 x=c：x 恰为 c，端点非严格（避免 x=5 推出 x<5）
                    bv = T.num_val(o)
                    tighten(bv, False, bv, False)
                else:
                    # 变量等式 x=y：x 与 y 同值，区间与严格性透明传递
                    iv = _interval(o, ctx, seen, depth + 1)
                    if iv is not None:
                        tighten(*iv)
    if is_int:
        # 整数属性消费：端点收紧到最近整点（x>2 ∧ x∈Z ⇒ x≥3）
        if lo is not None:
            c = lo.numerator // lo.denominator + 1 if los else -((-lo.numerator) // lo.denominator)
            if c > lo or los:
                lo, los = c, False
        if hi is not None:
            c = -((-hi.numerator) // hi.denominator) - 1 if his else hi.numerator // hi.denominator
            if c < hi or his:
                hi, his = c, False
    if isinstance(t, T.Expr):
        n = t.head.name
        if n == "Plus":
            # TODO: 数值常量子项（含字面 0 因子）应先经 ℚ 域算术折叠——
            # 原由 L0 构造期折叠承担，裁定后职责移至数域层。未折叠时
            # 本处理器会因单个无界子项整体放弃。
            ivs = [_interval(a, ctx, seen, depth + 1) for a in t.args]
            if all(iv is not None for iv in ivs):
                slo = sum(iv[0] for iv in ivs) if all(iv[0] is not None for iv in ivs) else None
                shi = sum(iv[1] for iv in ivs) if all(iv[1] is not None for iv in ivs) else None
                st = any(iv[2] for iv in ivs if iv[0] is not None)
                sht = any(iv[3] for iv in ivs if iv[1] is not None)
                tighten(slo, st, shi, sht)
        elif n == "Times":
            # TODO: 同上——字面零因子应折叠为零（ℚ 域算术），当前 len(rest)!=1 即放弃
            nums = [a for a in t.args if T.is_num(a)]
            rest = [a for a in t.args if not T.is_num(a)]
            if nums and len(rest) == 1:
                c = Fr(1)
                for nn in nums:
                    c *= T.num_val(nn)
                iv = _interval(rest[0], ctx, seen, depth + 1)
                if iv is not None:
                    if c > 0:
                        tighten(
                            None if iv[0] is None else c * iv[0], iv[2],
                            None if iv[1] is None else c * iv[1], iv[3],
                        )
                    elif c < 0:
                        tighten(
                            None if iv[1] is None else c * iv[1], iv[3],
                            None if iv[0] is None else c * iv[0], iv[2],
                        )
        elif n == "Power" and isinstance(t.args[1], T.Int) and t.args[1].v % 2 == 0:
            tighten(Fr(0), False, None, False)
        elif n == "Abs":
            tighten(Fr(0), False, None, False)
    if lo is None and hi is None:
        return None
    return (lo, hi, los, his)


def _cmp_interval(op, a, b, ctx):
    """把 a op b 归为 d = a - b 对 0 的区间比较（构造器自动合并同类项）。"""
    d = T.plus(a, T.neg(b))
    if op in ("Eq", "Ne"):
        if d is T.ZERO:
            return T3.YES if op == "Eq" else T3.NO
        iv = _interval(d, ctx)
        if iv is not None:
            lo, hi, _, _ = iv
            away = (lo is not None and lo > 0) or (hi is not None and hi < 0)
            if away:
                return T3.NO if op == "Eq" else T3.YES
        return None
    if d is T.ZERO:
        return T3.YES if op in ("Le", "Ge") else T3.NO
    iv = _interval(d, ctx)
    if iv is None:
        return None
    lo, hi, los, his = iv
    if lo is not None and hi is not None and lo == hi and not los and not his:
        # 闭区间退化为单点 = 精确值，直接裁决
        if op == "Gt":
            return T3.YES if lo > 0 else T3.NO
        if op == "Ge":
            return T3.YES if lo >= 0 else T3.NO
        if op == "Lt":
            return T3.YES if lo < 0 else T3.NO
        return T3.YES if lo <= 0 else T3.NO
    if op == "Gt":
        if (lo is not None and lo > 0) or (lo == 0 and los):
            return T3.YES
        if (hi is not None and hi < 0) or (hi == 0 and his):
            return T3.NO
    elif op == "Ge":
        if lo is not None and lo >= 0:
            return T3.YES
        if (hi is not None and hi < 0) or (hi == 0 and his):
            return T3.NO
    elif op == "Lt":
        if (hi is not None and hi < 0) or (hi == 0 and his):
            return T3.YES
        if (lo is not None and lo > 0) or (lo == 0 and los):
            return T3.NO
    else:  # Le
        if hi is not None and hi <= 0:
            return T3.YES
        if (lo is not None and lo > 0) or (lo == 0 and los):
            return T3.NO
    return None


_RULES = []
_MAX_DEPTH = 6


def derive(name, applies):
    def deco(fn):
        _RULES.append((name, applies, fn))
        return fn
    return deco


def _is_cmp(f):
    return isinstance(f, T.Expr) and f.head.name in _CMP


def _is_ord(f):
    return isinstance(f, T.Expr) and f.head.name in ("Lt", "Le", "Gt", "Ge")


def _zero_cmp_of(a, ctx, q, op):
    nneg = R.nonneg(a, ctx)
    pos = R.pos(a, ctx)
    if op == "Gt":
        if pos is True:
            return T3.YES
        if nneg is False or (nneg is True and pos is False):
            return T3.NO
        return None
    if op == "Ge":
        if nneg is True:
            return T3.YES
        if nneg is False:
            return T3.NO
        return None
    if op == "Lt":
        if pos is True:
            return T3.NO
        if nneg is False:
            return T3.YES
        if nneg is True and pos is False:
            return T3.NO
        return None
    if op == "Le":
        if pos is True:
            return T3.NO
        if nneg is False:
            return T3.YES
        if nneg is True and pos is False:
            return T3.YES
        return None
    return None


@derive("ne-from-ord", lambda f: f.head.name == "Ne")
def _rule_ne_from_ord(f, ctx, q):
    a, b = f.args
    if q(T.mk(S("Gt"), (a, b))) is T3.YES or q(T.mk(S("Lt"), (a, b))) is T3.YES:
        return T3.YES
    if q(T.mk(S("Eq"), (a, b))) is T3.YES:
        return T3.NO
    return None


@derive("cmp-via-eq", lambda f: _is_ord(f))
def _rule_cmp_via_eq(f, ctx, q):
    a, b = f.args
    if T.is_num(b):
        for e in ctx.entries:
            g = e.fact
            if (
                isinstance(g, T.Expr)
                and g.head.name == "Eq"
                and g.args[0] is a
                and T.is_num(g.args[1])
            ):
                return _cmp_numeric(f.head.name, g.args[1], b)
    return None


def _sign_of_term(t, ctx, q):
    if T.is_num(t):
        s = T.sign_num(t)
        if s > 0:
            return 1
        if s < 0:
            return -1
        return 0
    if t is PI or t is E:
        return 1
    r = q(T.mk(S("Gt"), (t, T.ZERO)))
    if r is T3.YES:
        return 1
    r = q(T.mk(S("Lt"), (t, T.ZERO)))
    if r is T3.YES:
        return -1
    r = q(T.mk(S("Eq"), (t, T.ZERO)))
    if r is T3.YES:
        return 0
    r = q(T.mk(S("Ge"), (t, T.ZERO)))
    if r is T3.YES:
        return 2
    return None


@derive("sign-atom", lambda f: _is_ord(f) and f.args[1] is T.ZERO)
def _rule_sign_atom(f, ctx, q):
    return _zero_cmp_of(f.args[0], ctx, q, f.head.name)


@derive("sign-times", lambda f: _is_ord(f) and f.args[1] is T.ZERO and isinstance(f.args[0], T.Expr) and f.args[0].head.name == "Times")
def _rule_sign_times(f, ctx, q):
    op = f.head.name
    a = f.args[0]
    s_zero = False
    s_nn = False
    neg_count = 0
    for fac in a.args:
        s = _sign_of_term(fac, ctx, q)
        if s is None:
            return None
        if s == 0:
            s_zero = True
        elif s == -1:
            neg_count += 1
        elif s == 2:
            s_nn = True
    if s_zero:
        return T3.NO if op in ("Gt", "Lt") else T3.YES
    odd = neg_count % 2 == 1
    if op == "Gt":
        if odd:
            return T3.NO
        return T3.YES if not s_nn else T3.UNKNOWN
    if op == "Ge":
        if odd and not s_nn:
            return T3.NO
        return T3.UNKNOWN if odd else T3.YES
    if op == "Lt":
        if odd and not s_nn:
            return T3.YES
        return T3.UNKNOWN if odd else T3.NO
    return T3.YES if odd else (T3.UNKNOWN if s_nn else T3.NO)


@derive("sign-even-power", lambda f: _is_ord(f) and f.args[1] is T.ZERO and isinstance(f.args[0], T.Expr) and f.args[0].head.name == "Power" and isinstance(f.args[0].args[1], T.Int) and f.args[0].args[1].v % 2 == 0)
def _rule_sign_even_power(f, ctx, q):
    op = f.head.name
    b = f.args[0].args[0]
    if op in ("Ge",):
        return T3.YES
    if op == "Lt":
        return T3.NO
    if op == "Gt":
        r = q(T.mk(S("Ne"), (b, T.ZERO)))
        if r is T3.YES:
            return T3.YES
        r = q(T.mk(S("Eq"), (b, T.ZERO)))
        if r is T3.YES:
            return T3.NO
        return None
    r = q(T.mk(S("Eq"), (b, T.ZERO)))
    if r is T3.YES:
        return T3.YES
    r = q(T.mk(S("Ne"), (b, T.ZERO)))
    if r is T3.YES:
        return T3.NO
    return None


@derive("sign-abs", lambda f: _is_ord(f) and f.args[1] is T.ZERO and isinstance(f.args[0], T.Expr) and f.args[0].head.name == "Abs")
def _rule_sign_abs(f, ctx, q):
    op = f.head.name
    u = f.args[0].args[0]
    if op == "Ge":
        return T3.YES
    if op == "Lt":
        return T3.NO
    if op == "Gt":
        r = q(T.mk(S("Ne"), (u, T.ZERO)))
        if r is T3.YES:
            return T3.YES
        r = q(T.mk(S("Eq"), (u, T.ZERO)))
        if r is T3.YES:
            return T3.NO
        return None
    r = q(T.mk(S("Eq"), (u, T.ZERO)))
    if r is T3.YES:
        return T3.YES
    r = q(T.mk(S("Ne"), (u, T.ZERO)))
    if r is T3.YES:
        return T3.NO
    return None


@derive("sign-power", lambda f: _is_ord(f) and f.args[1] is T.ZERO and isinstance(f.args[0], T.Expr) and f.args[0].head.name == "Power" and isinstance(f.args[0].args[1], T.Int) and f.args[0].args[1].v % 2 == 1)
def _rule_sign_odd_power(f, ctx, q):
    b = f.args[0].args[0]
    return q(T.mk(S(f.head.name), (b, T.ZERO)))


@derive("sign-sum", lambda f: _is_ord(f) and f.args[1] is T.ZERO and isinstance(f.args[0], T.Expr) and f.args[0].head.name == "Plus")
def _rule_sign_sum(f, ctx, q):
    op = f.head.name
    a = f.args[0]
    if op in ("Gt", "Ge"):
        all_ge = True
        any_pos = False
        for t_ in a.args:
            r = q(T.mk(S("Ge"), (t_, T.ZERO)))
            if r is not T3.YES:
                all_ge = False
                break
            r2 = q(T.mk(S("Gt"), (t_, T.ZERO)))
            if r2 is T3.YES:
                any_pos = True
        if all_ge and any_pos:
            return T3.YES
        all_le = True
        any_neg = False
        for t_ in a.args:
            r = q(T.mk(S("Le"), (t_, T.ZERO)))
            if r is not T3.YES:
                all_le = False
                break
            r2 = q(T.mk(S("Lt"), (t_, T.ZERO)))
            if r2 is T3.YES:
                any_neg = True
        if all_le and any_neg:
            return T3.NO
        return None
    all_le = True
    any_neg = False
    for t_ in a.args:
        r = q(T.mk(S("Le"), (t_, T.ZERO)))
        if r is not T3.YES:
            all_le = False
            break
        r2 = q(T.mk(S("Lt"), (t_, T.ZERO)))
        if r2 is T3.YES:
            any_neg = True
    if all_le and any_neg:
        return T3.YES
    all_ge = True
    any_pos = False
    for t_ in a.args:
        r = q(T.mk(S("Ge"), (t_, T.ZERO)))
        if r is not T3.YES:
            all_ge = False
            break
        r2 = q(T.mk(S("Gt"), (t_, T.ZERO)))
        if r2 is T3.YES:
            any_pos = True
    if all_ge and any_pos:
        return T3.NO
    return None


@derive("eq-times-zero", lambda f: f.head.name == "Eq" and isinstance(f.args[0], T.Expr) and f.args[0].head.name == "Times")
def _rule_eq_times_zero(f, ctx, q):
    a = f.args[0]
    any_zero = T3.NO
    for fac in a.args:
        r = q(T.mk(S("Eq"), (fac, T.ZERO)))
        if r is T3.YES:
            return T3.YES
        if r is T3.UNKNOWN:
            any_zero = T3.UNKNOWN
    return any_zero


@derive("sign-num", lambda f: _is_ord(f) and f.args[1] is T.ZERO and T.is_num(f.args[0]))
def _rule_sign_num(f, ctx, q):
    s = T.sign_num(f.args[0])
    op = f.head.name
    if op == "Gt":
        return T3.YES if s > 0 else T3.NO
    if op == "Ge":
        return T3.YES if s >= 0 else T3.NO
    if op == "Lt":
        return T3.YES if s < 0 else T3.NO
    return T3.YES if s <= 0 else T3.NO


@derive("eq-num", lambda f: f.head.name in ("Eq", "Ne") and T.is_num(f.args[0]) and T.is_num(f.args[1]))
def _rule_eq_num(f, ctx, q):
    if f.head.name == "Eq":
        return T3.YES if T.num_val(f.args[0]) == T.num_val(f.args[1]) else T3.NO
    return T3.YES if T.num_val(f.args[0]) != T.num_val(f.args[1]) else T3.NO


@derive("cmp-flip", lambda f: _is_cmp(f) and f.args[0] is T.ZERO and f.args[1] is not T.ZERO)
def _rule_cmp_flip(f, ctx, q):
    op = f.head.name
    a, b = f.args
    if op in ("Eq", "Ne"):
        return q(T.mk(S(op), (b, a)))
    flip = {"Gt": "Lt", "Lt": "Gt", "Ge": "Le", "Le": "Ge"}
    return q(T.mk(S(flip[op]), (b, a)))


def _derive_layer(fact, ctx, depth):
    q = lambda f: decide(f, ctx, depth + 1)
    for name, applies, fn in _RULES:
        if applies(fact):
            r = fn(fact, ctx, q)
            if r is not None:
                return r
    return None


_AXIOM_CHECKS = []


def axiom(fn):
    _AXIOM_CHECKS.append(fn)
    return fn


_CONST_BOUNDS = {id(PI): (3, 4), id(E): (2, 3)}


@axiom
def _axiom_constants(fact, ctx):
    if not (isinstance(fact, T.Expr) and fact.head.name in ("Gt", "Ge", "Lt", "Le")):
        return None
    a, b = fact.args
    if id(a) in _CONST_BOUNDS and T.is_num(b):
        lo, hi = _CONST_BOUNDS[id(a)]
        bv = T.num_val(b)
        op = fact.head.name
        if op in ("Gt", "Ge"):
            if bv <= lo:
                return T3.YES
            if bv >= hi:
                return T3.NO
        else:
            if bv >= hi:
                return T3.YES
            if bv <= lo:
                return T3.NO
    return None


# TODO: 有界性公理由图书馆引理表接替（原 FunctionSpec.bound 自动生成，
# spec 层已删除）。逐个函数登记 |f| <= c 型引理后恢复。


def _family_cmp(fact, ctx, depth):
    op = fact.head.name
    a, b = fact.args
    if op in ("Eq", "Ne"):
        r = _same(op, a, b)
        if r is not None:
            return r
        r = _cmp_numeric(op, a, b)
        if r is not None:
            return r
        r = _facts_lookup(fact, ctx)
        if r is not None:
            return r
        if op == "Eq":
            r = _poly_eq_check(a, b)
            if r is not None:
                return r
        r = _cmp_interval(op, a, b, ctx)
        if r is not None:
            return r
    else:
        r = _cmp_numeric(op, a, b)
        if r is not None:
            return r
        r = _same(op, a, b)
        if r is not None:
            return r
        r = _facts_lookup(fact, ctx)
        if r is not None:
            return r
        r = _cmp_interval(op, a, b, ctx)
        if r is not None:
            return r
        r = _chain_query(op, a, b, ctx)
        if r is not None:
            return r
    r = _derive_layer(fact, ctx, depth)
    if r is not None:
        return r
    for ax in _AXIOM_CHECKS:
        r = ax(fact, ctx)
        if r is not None:
            return r
    return T3.UNKNOWN


def _contains(t, pat):
    if t is pat:
        return True
    if isinstance(t, T.Expr):
        return any(_contains(a, pat) for a in t.args)
    return False


def _eq_subst(fact, ctx, depth):
    """账本等式代入归一：把账本中的 Eq(u,v) 双向代入查询事实后重判。

    不限数值侧：符号等式（如换元定义 t = sin(x)）同样背书查询
    （decide 相对账本的含义即"在假设下判定"；_MAX_DEPTH 防连锁循环）。
    """
    a, b = fact.args
    for e in ctx.entries:
        f = e.fact
        if isinstance(f, T.Expr) and f.head.name == "Eq" and f is not fact:
            u, v = f.args
            if not (_contains(a, u) or _contains(a, v) or _contains(b, u) or _contains(b, v)):
                continue
            for pat, rep in ((u, v), (v, u)):
                na = T.subst(a, {pat: rep})
                nb = T.subst(b, {pat: rep})
                if na is a and nb is b:
                    continue
                r = decide(T.mk(S("Eq"), (na, nb)), ctx, depth + 1)
                if r is not T3.UNKNOWN:
                    return r
    return None


def decide(fact, ctx, _depth=0):
    if _depth > _MAX_DEPTH:
        return T3.UNKNOWN
    if fact is T.TRUE:
        return T3.YES
    if fact is T.FALSE:
        return T3.NO
    if isinstance(fact, T.Expr):
        name = fact.head.name
        if name in _CMP:
            if name == "Eq":
                r = _eq_subst(fact, ctx, _depth)
                if r is not None:
                    return r
            return _family_cmp(fact, ctx, _depth)
        if name == "And":
            r = T3.YES
            for a in fact.args:
                r = and3(r, decide(a, ctx, _depth))
                if r is T3.NO:
                    return r
            return r
        if name == "Or":
            r = T3.NO
            for a in fact.args:
                r = or3(r, decide(a, ctx, _depth))
                if r is T3.YES:
                    return r
            return r
        if name == "Not":
            return not3(decide(fact.args[0], ctx, _depth))
    return T3.UNKNOWN


def decided(fact, ctx):
    return decide(fact, ctx, 0)


def satisfiable(constraints, ctx):
    for i, c in enumerate(constraints):
        tmp = ctx.clone()
        for j, d in enumerate(constraints):
            if j != i:
                tmp.assume(d, origin="_sat")
        if decide(c, tmp) is T3.NO or decide(negate(c), tmp) is T3.YES:
            return T3.NO
    return T3.YES if not constraints else T3.UNKNOWN


def domain_ok(fact, ctx):
    from cas.domain import dom_condition

    return satisfiable(dom_condition(fact), ctx)


def contradicted(fact, ctx):
    return decide(fact, ctx) is T3.NO or decide(negate(fact), ctx) is T3.YES


def eval_guard(guard, sub, ctx):
    g = T.instantiate(guard, sub)
    r = decide(g, ctx)
    return r.value


# 判等阶段注册表（Step 4：管线分派从硬编码变为声明式数据）。
# 阶段契约：run(r, a, b, ctx) -> T3 结论 | None（无结论则继续下阶段）。
# 内置序 = 原硬编码顺序；外部（如 diff.py 的塔零判定/分数幂合并）
# 经 register_eq_stage 追加——三处重复分派的最后一份消除。
_EQ_STAGES = []


def register_eq_stage(name, run, prepend=False):
    entry = (name, run)
    if prepend:
        _EQ_STAGES.insert(0, entry)
    else:
        _EQ_STAGES.append(entry)
    return name


def equivalent(a, b, ctx=None, budget=100000):
    """统一判等管线：指针 -> 数值常量 -> 标准形归零 -> 注册阶段序列 -> 诚实 UNKNOWN。

    TODO: 第二步依赖所在域的标准形（多项式机器、塔规范形）——
    当前多数域的标准形尚未重建，非指针相等的判等大量返回 UNKNOWN，
    属预期降级而非回归。"""
    from cas.simplify import simplify
    from cas.context import Context

    if a is b:
        return T3.YES
    if T.is_num(a) and T.is_num(b):
        return T3.YES if T.num_val(a) == T.num_val(b) else T3.NO
    r = simplify(T.plus(a, T.neg(b)), budget)
    if r is T.ZERO:
        return T3.YES
    if ctx is None:
        ctx = Context()
    for _name, run in _EQ_STAGES:
        try:
            d = run(r, a, b, ctx)
        except Exception:
            continue          # 阶段内部失败 = 无结论（绝不污染判等）
        if d is not None and d is not T3.UNKNOWN:
            return d
    return T3.UNKNOWN


def _stage_decide(r, a, b, ctx):
    d = decide(T.mk(S("Eq"), (r, T.ZERO)), ctx)
    return None if d is T3.UNKNOWN else d


# TODO: 三角基归零阶段随函数结构层重建（原走 cas.trig.trig_reduce）
register_eq_stage("ledger_decide", _stage_decide)

# TODO: 数值采样阶段被纯符号约束永久移除。未找到与不存在是两个结论，
# 采样从未有资格产出后者；如需概率通道须先修订宪章。


