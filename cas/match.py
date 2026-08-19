from cas import term as T
from cas.errors import BudgetExceeded

# 类型洞谓词（结构检查，无需上下文；语义谓词如正负走规则 guard/decide）
_PREDS = {
    "num": lambda t: T.is_num(t),
    "int": lambda t: isinstance(t, T.Int),
    "rat": lambda t: isinstance(t, T.Rat),
    "sym": lambda t: isinstance(t, T.Sym),
    "const": lambda t: isinstance(t, T.Const) or T.is_num(t),
    "expr": lambda t: isinstance(t, T.Expr),
}


def _pred_ok(pat, tgt):
    if pat.pred is None:
        return True
    fn = _PREDS.get(pat.pred)
    return fn is not None and fn(tgt)


# OneIdentity（mathics-core attributes.py 同款实据）：带单位元的 AC 头允许
# 模式匹配裸项——?a+?b 可匹配 x（另一洞取 0），?a*?b 可匹配 x（另一洞取 1）。
# 只有洞（PatVar/PatSeq）与字面单位元可吸收单位元；非洞子模式必须如实匹配。
_ONE_ID = {}


def _one_identity():
    if not _ONE_ID:
        _ONE_ID.update({"Plus": T.ZERO, "Times": T.ONE})
    return _ONE_ID


def _bind_identity(p, ident, sub):
    """模式参数 p 绑定到单位元：PatVar 新绑/一致检查，PatSeq 绑空元组。"""
    if isinstance(p, T.PatVar):
        if not _pred_ok(p, ident):
            return None
        cur = sub.get(p.name)
        if cur is None:
            s2 = dict(sub)
            s2[p.name] = ident
            return s2
        return sub if cur is ident else None
    if isinstance(p, T.PatSeq):
        cur = sub.get(p.name)
        if cur is None:
            s2 = dict(sub)
            s2[p.name] = ()
            return s2
        return sub if cur == () else None
    return sub if p is ident else None


def _all_identity(pats, ident, sub, st):
    """剩余模式参数全部吸收单位元。"""
    if not pats:
        yield sub
        return
    s2 = _bind_identity(pats[0], ident, sub)
    if s2 is not None:
        yield from _all_identity(pats[1:], ident, s2, st)


def _match_one_id(pats, ident, tgt, sub, st):
    """OneIdentity 通道：模式参数逐个竞争匹配 tgt，其余吸收单位元。"""
    st[0] -= 1
    if st[0] < 0:
        raise BudgetExceeded()
    if not pats:
        return
    p, rest = pats[0], pats[1:]
    # p 消费 tgt，其余全部取单位元
    for s2 in _match(p, tgt, sub, st):
        yield from _all_identity(rest, ident, s2, st)
    # p 吸收单位元，tgt 留给后续参数
    s2 = _bind_identity(p, ident, sub)
    if s2 is not None:
        yield from _match_one_id(rest, ident, tgt, s2, st)


def _match(pat, tgt, sub, st):
    st[0] -= 1
    if st[0] < 0:
        raise BudgetExceeded()
    k = pat.__class__
    if k is T.PatVar:
        if not _pred_ok(pat, tgt):
            return
        cur = sub.get(pat.name)
        if cur is None:
            s2 = dict(sub)
            s2[pat.name] = tgt
            yield s2
        elif cur is tgt:
            yield sub
        return
    if k is T.PatSeq:
        cur = sub.get(pat.name)
        if cur is None:
            s2 = dict(sub)
            s2[pat.name] = (tgt,)
            yield s2
        elif cur == (tgt,):
            yield sub
        return
    if k is T.Expr:
        if isinstance(tgt, T.Expr) and tgt.head is pat.head:
            if pat.head.name in T.AC:
                yield from _match_orderless(list(pat.args), list(tgt.args), sub, st)
            else:
                yield from _match_seq(list(pat.args), list(tgt.args), sub, st)
            return
        ident = _one_identity().get(pat.head.name)
        if ident is not None:
            yield from _match_one_id(list(pat.args), ident, tgt, sub, st)
        return
    if k is T.Bound:
        if isinstance(tgt, T.Bound):
            yield from _match(pat.body, tgt.body, sub, st)
        return
    if pat is tgt:
        yield sub
    return


def _match_seq(pats, terms, sub, st):
    if not pats:
        if not terms:
            yield sub
        return
    p = pats[0]
    if isinstance(p, T.PatSeq):
        n = len(terms)
        for k in range(1, n + 1):
            cur = sub.get(p.name)
            if cur is None:
                s2 = dict(sub)
                s2[p.name] = tuple(terms[:k])
                yield from _match_seq(pats[1:], terms[k:], s2, st)
            else:
                if tuple(terms[:k]) == cur:
                    yield from _match_seq(pats[1:], terms[k:], sub, st)
        return
    if not terms:
        return
    for s2 in _match(p, terms[0], sub, st):
        yield from _match_seq(pats[1:], terms[1:], s2, st)


def _match_orderless(pats, terms, sub, st):
    st[0] -= 1
    if st[0] < 0:
        raise BudgetExceeded()
    if not pats:
        if not terms:
            yield sub
        return
    p = pats[0]
    if not isinstance(p, (T.PatVar, T.PatSeq)) and not _has_holes(p):
        if p in terms:
            rest = list(terms)
            rest.remove(p)
            yield from _match_orderless(pats[1:], rest, sub, st)
        return
    if isinstance(p, T.PatSeq):
        n = len(terms)
        for i in range(n):
            for ln in range(1, n - i + 1):
                seq = tuple(terms[i : i + ln])
                rest = terms[:i] + terms[i + ln :]
                cur = sub.get(p.name)
                if cur is None:
                    s2 = dict(sub)
                    s2[p.name] = seq
                    yield from _match_orderless(pats[1:], rest, s2, st)
                elif cur == seq:
                    yield from _match_orderless(pats[1:], rest, sub, st)
        return
    for i, t in enumerate(terms):
        rest = terms[:i] + terms[i + 1 :]
        for s2 in _match(p, t, sub, st):
            yield from _match_orderless(pats[1:], rest, s2, st)


def _has_holes(p):
    if isinstance(p, (T.PatVar, T.PatSeq)):
        return True
    if isinstance(p, T.Expr):
        return any(_has_holes(a) for a in p.args)
    if isinstance(p, T.Bound):
        return _has_holes(p.body)
    return False


def _sub_key(sub):
    items = []
    for k, v in sub.items():
        if isinstance(v, tuple):
            items.append((k, tuple(x._h for x in v)))
        else:
            items.append((k, v._h))
    return tuple(sorted(items, key=lambda kv: kv[0]))


def matches(pat, tgt, sub=None, budget=10000):
    st = [budget]
    base = dict(sub) if sub else {}
    seen = set()
    if isinstance(pat, T.PatVar):
        if not _pred_ok(pat, tgt):
            return
        cur = base.get(pat.name)
        if cur is None or cur is tgt:
            s2 = dict(base)
            s2[pat.name] = tgt
            yield s2
        return
    for s in _match(pat, tgt, base, st):
        k = _sub_key(s)
        if k in seen:
            continue
        seen.add(k)
        yield s
