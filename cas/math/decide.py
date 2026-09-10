# -*- coding: utf-8 -*-
"""判定管线：命题复合 + 域特定可判定原子（架构第七节）。

返回值是判定 ADT（cas/verdict）：Yes/No/Unknown(理由)。
Unknown 的理由区分片段没覆盖（FRAGMENT）、被条件挡住（GUARDED）、
根本不可判定（UNDECIDABLE）、预算耗尽（BUDGET）——四种后果不同，
禁止折叠成同一个"不知道"。

原子通道（按序）：指针/数值 → 账本直查 → 投影判零（域标准形）→
区间传播 → 序链推理 → 规则派生层 → 图书馆引理（常数粗界、函数值域界）。
"""

from collections import deque

from cas.syntax import term as T
from cas.syntax.term import S, N
from cas.math.qarith import fold as _qfold
from cas.kernel.verdict import (Verdict, Yes, No, Unknown, Reason,
                          YES, NO, unknown, and3, or3, not3)
import library


_NEG = {
    "Gt": "Le",
    "Ge": "Lt",
    "Lt": "Ge",
    "Le": "Gt",
    "Eq": "Ne",
    "Ne": "Eq",
}


def negate(f):
    """比较谓词的强否定（¬(a>b) ≡ a≤b 等）；其余走句法 Not。"""
    if isinstance(f, T.Expr) and f.head.name in _NEG:
        return T.mk(S(_NEG[f.head.name]), f.args)
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
    return YES if r else NO


def _same(op, a, b):
    if a is not b:
        return None
    if op in ("Eq", "Le", "Ge"):
        return YES
    return NO


def _poly_eq_check(a, b):
    """投影判零通道：a−b 落入 ℚ/K[x]/K(x) 时域标准形完全判定。"""
    d = _qfold(T.plus(a, T.neg(b)))
    if d is T.ZERO:
        return YES
    from cas.math.project import zero_of
    r = zero_of(d)
    if r is True:
        return YES
    if r is False:
        return NO
    return None


def _facts_lookup(fact, ctx):
    for e in ctx.entries:
        f = e.fact
        if f is fact:
            return YES
        if f is negate(fact):
            return NO
        if isinstance(f, T.Expr) and isinstance(fact, T.Expr):
            if f.head.name in _CMP_INV and fact.head.name in _CMP_INV:
                if (
                    f.head.name == _CMP_INV[fact.head.name]
                    and f.args[0] is fact.args[1]
                    and f.args[1] is fact.args[0]
                ):
                    return YES
    return None


def _chain_query(op, a, b, ctx):
    """序链 BFS：账本不等式建边，传递闭包回答 a<b 型查询。

    状态为 (节点, 路径是否含严格边)，按节点记录最优严格性；
    数值界推理与等式代入由 _interval 区间通道负责，此处只走图边。
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
        return YES if op in ("Le", "Ge", "Eq") else NO
    start, goal = want
    best = {start._h: False}
    queue = deque([(start, False)])
    while queue:
        cur, evs = queue.popleft()
        if best.get(cur._h, False) != evs:
            continue                       # 过期状态（已有更优严格性）
        for nxt, st in adj.get(cur, ()):
            ns = evs or st
            if nxt is goal and (not strict or ns):
                return YES
            prev = best.get(nxt._h)
            if prev is None or (ns and not prev):
                best[nxt._h] = ns
                queue.append((nxt, ns))
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
    lb = library.const_bounds(t)
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
            ivs = [_interval(a, ctx, seen, depth + 1) for a in t.args]
            if all(iv is not None for iv in ivs):
                slo = sum(iv[0] for iv in ivs) if all(iv[0] is not None for iv in ivs) else None
                shi = sum(iv[1] for iv in ivs) if all(iv[1] is not None for iv in ivs) else None
                st = any(iv[2] for iv in ivs if iv[0] is not None)
                sht = any(iv[3] for iv in ivs if iv[1] is not None)
                tighten(slo, st, shi, sht)
        elif n == "Times":
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
        else:
            # 函数值域界（图书馆声明）：端点可达（lo ≤ f ≤ hi），严格性为假
            bd = _func_bound(n)
            if bd is not None:
                tighten(bd[0], False, bd[1], False)
    if lo is None and hi is None:
        return None
    return (lo, hi, los, his)


def _cmp_interval(op, a, b, ctx):
    """把 a op b 归为 d = a - b 对 0 的区间比较（d 先经 ℚ 字面折叠）。"""
    d = _qfold(T.plus(a, T.neg(b)))
    if op in ("Eq", "Ne"):
        if d is T.ZERO:
            return YES if op == "Eq" else NO
        iv = _interval(d, ctx)
        if iv is not None:
            lo, hi, _, _ = iv
            away = (lo is not None and lo > 0) or (hi is not None and hi < 0)
            if away:
                return NO if op == "Eq" else YES
        return None
    if d is T.ZERO:
        return YES if op in ("Le", "Ge") else NO
    iv = _interval(d, ctx)
    if iv is None:
        return None
    lo, hi, los, his = iv
    if lo is not None and hi is not None and lo == hi and not los and not his:
        # 闭区间退化为单点 = 精确值，直接裁决
        if op == "Gt":
            return YES if lo > 0 else NO
        if op == "Ge":
            return YES if lo >= 0 else NO
        if op == "Lt":
            return YES if lo < 0 else NO
        return YES if lo <= 0 else NO
    if op == "Gt":
        if (lo is not None and lo > 0) or (lo == 0 and los):
            return YES
        if (hi is not None and hi < 0) or (hi == 0 and his):
            return NO
    elif op == "Ge":
        if lo is not None and lo >= 0:
            return YES
        if (hi is not None and hi < 0) or (hi == 0 and his):
            return NO
    elif op == "Lt":
        if (hi is not None and hi < 0) or (hi == 0 and his):
            return YES
        if (lo is not None and lo > 0) or (lo == 0 and los):
            return NO
    else:  # Le
        if hi is not None and hi <= 0:
            return YES
        if (lo is not None and lo > 0) or (lo == 0 and los):
            return NO
    return None


# ---------------------------------------------------------------------------
# 符号结构引理（原 cas/domain.py RealDomain 的可判定部分，模块废除后归位）
# ---------------------------------------------------------------------------

def _func_bound(name):
    """函数值域界（图书馆声明）：返回 (lo|None, hi|None) 或 None。"""
    d = library.lookup_function(name)
    return d.bound if d is not None else None


def _nonneg_zero_arg(t):
    """t = g(u) 且 g 声明"非负下界 0 + g(u)=0⟺u=0"（绝对值/范数类）→ 返回 u。

    判定据图书馆声明（zero_iff_arg_zero + bound 下界为 0），不据函数名。"""
    if not isinstance(t, T.Expr) or not isinstance(t.head, T.Sym) \
            or len(t.args) != 1:
        return None
    d = library.lookup_function(t.head.name)
    if d is None or not d.zero_iff_arg_zero:
        return None
    bd = d.bound
    if bd is None or bd[0] is None or bd[0] != 0:
        return None
    return t.args[0]


def _nneg(t, ctx):
    """非负结构判定：True/False/None（不回调 decide，只读结构与账本）。"""
    if T.is_num(t):
        return T.sign_num(t) >= 0
    if isinstance(t, T.Const) and library.const_positive(t) is True:
        return True
    if isinstance(t, T.Expr):
        name = t.head.name
        if name == "Power":
            b, e = t.args
            if isinstance(e, T.Int) and e.v % 2 == 0:
                return True
            if (
                isinstance(e, T.Rat)
                and e.f.denominator % 2 == 1
                and _pos(b, ctx) is True
            ):
                return True
        bd = _func_bound(name)
        if bd is not None and bd[0] is not None and bd[0] >= 0:
            return True
    if ctx is not None:
        for e in ctx.entries:
            f = e.fact
            if isinstance(f, T.Expr) and f.head.name in ("Gt", "Ge"):
                if f.args[0] is t and f.args[1] is T.ZERO:
                    return True
            if isinstance(f, T.Expr) and f.head.name in ("Lt", "Le"):
                if f.args[0] is t and f.args[1] is T.ZERO:
                    return False
    return None


def _pos(t, ctx):
    """正性结构判定：True/False/None。"""
    if T.is_num(t):
        return T.sign_num(t) > 0
    if isinstance(t, T.Const) and library.const_positive(t) is True:
        return True
    if ctx is not None:
        for e in ctx.entries:
            f = e.fact
            if isinstance(f, T.Expr) and f.head.name == "Gt":
                if f.args[0] is t and f.args[1] is T.ZERO:
                    return True
            if isinstance(f, T.Expr) and f.head.name == "Le":
                if f.args[0] is t and f.args[1] is T.ZERO:
                    return False
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
    nneg = _nneg(a, ctx)
    pos = _pos(a, ctx)
    if op == "Gt":
        if pos is True:
            return YES
        if nneg is False or (nneg is True and pos is False):
            return NO
        return None
    if op == "Ge":
        if nneg is True:
            return YES
        if nneg is False:
            return NO
        return None
    if op == "Lt":
        if pos is True:
            return NO
        if nneg is False:
            return YES
        if nneg is True and pos is False:
            return NO
        return None
    if op == "Le":
        if pos is True:
            return NO
        if nneg is False:
            return YES
        if nneg is True and pos is False:
            return YES
        return None
    return None


@derive("ne-from-ord", lambda f: f.head.name == "Ne")
def _rule_ne_from_ord(f, ctx, q):
    a, b = f.args
    if q(T.mk(S("Gt"), (a, b))) is YES or q(T.mk(S("Lt"), (a, b))) is YES:
        return YES
    if q(T.mk(S("Eq"), (a, b))) is YES:
        return NO
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
    if isinstance(t, T.Const) and library.const_positive(t) is True:
        return 1
    r = q(T.mk(S("Gt"), (t, T.ZERO)))
    if r is YES:
        return 1
    r = q(T.mk(S("Lt"), (t, T.ZERO)))
    if r is YES:
        return -1
    r = q(T.mk(S("Eq"), (t, T.ZERO)))
    if r is YES:
        return 0
    r = q(T.mk(S("Ge"), (t, T.ZERO)))
    if r is YES:
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
        return NO if op in ("Gt", "Lt") else YES
    odd = neg_count % 2 == 1
    # 存在未定非负因子：被未确认条件挡住，答案可随条件清偿翻转
    guarded = unknown(Reason.GUARDED) if s_nn else unknown()
    if op == "Gt":
        if odd:
            return NO
        return YES if not s_nn else guarded
    if op == "Ge":
        if odd and not s_nn:
            return NO
        return guarded if odd else YES
    if op == "Lt":
        if odd and not s_nn:
            return YES
        return guarded if odd else NO
    return YES if odd else (guarded if s_nn else NO)


@derive("sign-even-power", lambda f: _is_ord(f) and f.args[1] is T.ZERO and isinstance(f.args[0], T.Expr) and f.args[0].head.name == "Power" and isinstance(f.args[0].args[1], T.Int) and f.args[0].args[1].v % 2 == 0)
def _rule_sign_even_power(f, ctx, q):
    op = f.head.name
    b = f.args[0].args[0]
    if op in ("Ge",):
        return YES
    if op == "Lt":
        return NO
    if op == "Gt":
        r = q(T.mk(S("Ne"), (b, T.ZERO)))
        if r is YES:
            return YES
        r = q(T.mk(S("Eq"), (b, T.ZERO)))
        if r is YES:
            return NO
        return None
    r = q(T.mk(S("Eq"), (b, T.ZERO)))
    if r is YES:
        return YES
    r = q(T.mk(S("Ne"), (b, T.ZERO)))
    if r is YES:
        return NO
    return None


@derive("sign-nonneg-zero",
        lambda f: _is_ord(f) and f.args[1] is T.ZERO
        and _nonneg_zero_arg(f.args[0]) is not None)
def _rule_sign_nonneg_zero(f, ctx, q):
    """g(u) 对 0 的符号（g 声明非负且 g(u)=0⟺u=0，如绝对值/范数）：
    g≥0 恒真、g<0 恒假；g>0⟺u≠0、g≤0⟺u=0。判定据图书馆声明，不据名。"""
    op = f.head.name
    u = _nonneg_zero_arg(f.args[0])
    if op == "Ge":
        return YES
    if op == "Lt":
        return NO
    if op == "Gt":
        r = q(T.mk(S("Ne"), (u, T.ZERO)))
        if r is YES:
            return YES
        r = q(T.mk(S("Eq"), (u, T.ZERO)))
        if r is YES:
            return NO
        return None
    r = q(T.mk(S("Eq"), (u, T.ZERO)))
    if r is YES:
        return YES
    r = q(T.mk(S("Ne"), (u, T.ZERO)))
    if r is YES:
        return NO
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
            if r is not YES:
                all_ge = False
                break
            r2 = q(T.mk(S("Gt"), (t_, T.ZERO)))
            if r2 is YES:
                any_pos = True
        if all_ge and any_pos:
            return YES
        all_le = True
        any_neg = False
        for t_ in a.args:
            r = q(T.mk(S("Le"), (t_, T.ZERO)))
            if r is not YES:
                all_le = False
                break
            r2 = q(T.mk(S("Lt"), (t_, T.ZERO)))
            if r2 is YES:
                any_neg = True
        if all_le and any_neg:
            return NO
        return None
    all_le = True
    any_neg = False
    for t_ in a.args:
        r = q(T.mk(S("Le"), (t_, T.ZERO)))
        if r is not YES:
            all_le = False
            break
        r2 = q(T.mk(S("Lt"), (t_, T.ZERO)))
        if r2 is YES:
            any_neg = True
    if all_le and any_neg:
        return YES
    all_ge = True
    any_pos = False
    for t_ in a.args:
        r = q(T.mk(S("Ge"), (t_, T.ZERO)))
        if r is not YES:
            all_ge = False
            break
        r2 = q(T.mk(S("Gt"), (t_, T.ZERO)))
        if r2 is YES:
            any_pos = True
    if all_ge and any_pos:
        return NO
    return None


@derive("eq-times-zero", lambda f: f.head.name == "Eq" and isinstance(f.args[0], T.Expr) and f.args[0].head.name == "Times")
def _rule_eq_times_zero(f, ctx, q):
    """积判零。前提：本系统构造的系数结构（ℚ、K[x]、K(x)、代数/超越塔）
    均为整环——ab=0 ⟺ a=0 ∨ b=0。将来若引入矩阵环等非整环结构，
    本规则必须按环境域门控。"""
    a = f.args[0]
    any_zero = NO
    for fac in a.args:
        r = q(T.mk(S("Eq"), (fac, T.ZERO)))
        if r is YES:
            return YES
        if r is not NO:
            any_zero = unknown()
    return any_zero


@derive("sign-num", lambda f: _is_ord(f) and f.args[1] is T.ZERO and T.is_num(f.args[0]))
def _rule_sign_num(f, ctx, q):
    s = T.sign_num(f.args[0])
    op = f.head.name
    if op == "Gt":
        return YES if s > 0 else NO
    if op == "Ge":
        return YES if s >= 0 else NO
    if op == "Lt":
        return YES if s < 0 else NO
    return YES if s <= 0 else NO


@derive("eq-num", lambda f: f.head.name in ("Eq", "Ne") and T.is_num(f.args[0]) and T.is_num(f.args[1]))
def _rule_eq_num(f, ctx, q):
    if f.head.name == "Eq":
        return YES if T.num_val(f.args[0]) == T.num_val(f.args[1]) else NO
    return YES if T.num_val(f.args[0]) != T.num_val(f.args[1]) else NO


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


@axiom
def _axiom_constants(fact, ctx):
    """常数粗界引理（来自图书馆 const_bounds 声明）。"""
    if not (isinstance(fact, T.Expr) and fact.head.name in ("Gt", "Ge", "Lt", "Le")):
        return None
    a, b = fact.args
    bounds = library.const_bounds(a)
    if bounds is None or not T.is_num(b):
        return None
    lo, hi = bounds
    bv = T.num_val(b)
    op = fact.head.name
    if op in ("Gt", "Ge"):
        if bv <= lo:
            return YES
        if bv >= hi:
            return NO
    else:
        if bv >= hi:
            return YES
        if bv <= lo:
            return NO
    return None


@axiom
def _axiom_function_bounds(fact, ctx):
    """函数值域粗界引理（图书馆 FunctionDecl.bound 声明）。

    |f| 类界消费留给区间通道；此处只处理 f(u) op 数值 的直接比较。
    界端点可为 None（该侧无界），只就有界的一侧背书。"""
    if not (isinstance(fact, T.Expr) and fact.head.name in ("Gt", "Ge", "Lt", "Le")):
        return None
    a, b = fact.args
    if not (isinstance(a, T.Expr) and isinstance(a.head, T.Sym)) or not T.is_num(b):
        return None
    d = library.lookup_function(a.head.name)
    if d is None or d.bound is None:
        return None
    lo, hi = d.bound
    bv = T.num_val(b)
    op = fact.head.name
    # 界端点可达（lo ≤ f(u) ≤ hi）：严格不等式与弱不等式的背书条件不同
    if op == "Gt":
        if lo is not None and bv < lo:
            return YES
        if hi is not None and bv >= hi:
            return NO
    elif op == "Ge":
        if lo is not None and bv <= lo:
            return YES
        if hi is not None and bv > hi:
            return NO
    elif op == "Lt":
        if hi is not None and bv > hi:
            return YES
        if lo is not None and bv <= lo:
            return NO
    else:  # Le
        if hi is not None and bv >= hi:
            return YES
        if lo is not None and bv < lo:
            return NO
    return None


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
    # 公理层（图书馆界数据）是**兜底**，不是死代码：
    # 它与区间通道消费同一份图书馆声明（const_bounds / FunctionDecl.bound），
    # 但区间通道更通用（能对复合表达式 a−b 整体求区间），故通常先由它
    # 定案，本层只在所有前序通道都让位（返回 None）时才轮到。
    # 实测：屏蔽 _cmp_interval 后本层仍能正确裁决 pi>3 / e>2 / sin(x)>2。
    # 二者不是重复实现——区间通道覆盖广，本层是引理直读，删它会让
    # 图书馆界数据只剩单一消费路径。关系由 tests/test_decide_axioms.py 锁定。
    for ax in _AXIOM_CHECKS:
        r = ax(fact, ctx)
        if r is not None:
            return r
    return unknown()


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
                if not r.is_unknown():
                    return r
    return None


def decide(fact, ctx, _depth=0) -> Verdict:
    if _depth > _MAX_DEPTH:
        return unknown(Reason.BUDGET)
    if fact is T.TRUE:
        return YES
    if fact is T.FALSE:
        return NO
    if isinstance(fact, T.Expr):
        name = fact.head.name
        if name in _CMP:
            if name == "Eq":
                r = _eq_subst(fact, ctx, _depth)
                if r is not None:
                    return r
            return _family_cmp(fact, ctx, _depth)
        if name == "And":
            r = YES
            for a in fact.args:
                r = and3(r, decide(a, ctx, _depth))
                if r is NO:
                    return r
            return r
        if name == "Or":
            r = NO
            for a in fact.args:
                r = or3(r, decide(a, ctx, _depth))
                if r is YES:
                    return r
            return r
        if name == "Not":
            return not3(decide(fact.args[0], ctx, _depth))
    return unknown()


def satisfiable(constraints, ctx) -> Verdict:
    for i, c in enumerate(constraints):
        tmp = ctx.clone()
        for j, d in enumerate(constraints):
            if j != i:
                tmp.assume(d, origin="_sat")
        if decide(c, tmp) is NO or decide(negate(c), tmp) is YES:
            return NO
    return YES if not constraints else unknown()


def domain_ok(fact, ctx) -> Verdict:
    from cas.math.domcond import dom_condition

    return satisfiable(dom_condition(fact), ctx)


def contradicted(fact, ctx) -> bool:
    return decide(fact, ctx) is NO or decide(negate(fact), ctx) is YES


# 判等阶段注册表：管线分派从硬编码变为声明式数据。
# 阶段契约：run(r, a, b, ctx) -> Verdict 结论 | None（无结论则继续下阶段）。
# 阶段内部异常 = 阶段实现有 bug，直接向上传播（失败是返回值的一部分，
# 禁止吞掉；确需"无结论"请显式返回 None）。
_EQ_STAGES = []


def register_eq_stage(name, run, prepend=False):
    entry = (name, run)
    if prepend:
        _EQ_STAGES.insert(0, entry)
    else:
        _EQ_STAGES.append(entry)
    return name


def equivalent(a, b, ctx=None, budget=100000) -> Verdict:
    """统一判等管线：指针 -> 数值常量 -> 标准形归零 -> 注册阶段序列 -> 诚实 UNKNOWN。

    域标准形归零经 autosimplify + 投影判零；塔规范形重建后由注册阶段接入。"""
    from cas.math.simplify import autosimplify
    # 延迟导入：这是 cas.math.decide ↔ cas.kernel.context 环的回边。context 顶层
    # `from cas.math.decide import decide/contradicted/domain_ok`（去边），
    # 本处是反向。环的成因是上下文把判定当作事实查询的实现，而判定又
    # 需要造默认上下文；把默认上下文的构造移出 decide 即可拆环。
    from cas.kernel.context import Context

    if a is b:
        return YES
    if T.is_num(a) and T.is_num(b):
        return YES if T.num_val(a) == T.num_val(b) else NO
    a = _qfold(a)
    b = _qfold(b)
    if a is b:
        return YES
    if T.is_num(a) and T.is_num(b):
        return YES if T.num_val(a) == T.num_val(b) else NO
    r = autosimplify(T.plus(a, T.neg(b)), budget)
    if r is T.ZERO:
        return YES
    from cas.math.project import zero_of
    z = zero_of(r)
    if z is True:
        return YES
    if z is False:
        return NO
    if ctx is None:
        ctx = Context()
    for _name, run in _EQ_STAGES:
        d = run(r, a, b, ctx)
        if d is not None and not d.is_unknown():
            return d
    return unknown()


def _stage_decide(r, a, b, ctx):
    d = decide(T.mk(S("Eq"), (r, T.ZERO)), ctx)
    return None if d.is_unknown() else d


# TODO: 三角基归零阶段随函数结构层重建（原走 cas.trig.trig_reduce）
register_eq_stage("ledger_decide", _stage_decide)

# 数值采样阶段被纯符号约束永久移除。未找到与不存在是两个结论，
# 采样从未有资格产出后者；如需概率通道须先修订宪章。


# ---------------------------------------------------------------------------
# 上下文上的判定操作（自 kernel/context.py 移出，v4 §四）
#
# 这两个操作要调用本模块的判定器，故只能住在 math 侧：`kernel → 具体数学模块`
# 被 §四 严格禁止。它们引用 kernel 的 Context/Branch（math → kernel，合规）。
# ---------------------------------------------------------------------------

def check_and_assume(ctx, fact, origin="user", kind="fact"):
    """域检查 + 矛盾检查通过后把 fact 加入假设。返回 (Verdict, 原因)。"""
    from cas.kernel.verdict import NO, YES
    if domain_ok(fact, ctx) is NO:
        return NO, "domain"
    if contradicted(fact, ctx):
        return NO, "contradiction"
    ctx.assume(fact, origin=origin, kind=kind)
    return YES, None


def branch(ctx, *conds):
    """为每个条件克隆一个分支上下文；域外条件得到空分支。"""
    from cas.kernel.context import Branch
    from cas.kernel.verdict import NO
    out = []
    for c in conds:
        bctx = ctx.clone()
        st, _why = check_and_assume(bctx, c, origin="branch", kind="branch")
        out.append(Branch(c, bctx, "empty" if st is NO else "open"))
    return out
