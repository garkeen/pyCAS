# -*- coding: utf-8 -*-
"""模式匹配（v4 §5.2 模式元语言）。

被匹配的**主体**只有两类：`Pattern`（含洞）与 `Term`（字面量，指针相等即
匹配——驻留项 AC 规范化的红利）。模式变量不再出现在项里，故本模块是模式
变量唯一被解释的地方之一（另一处是 pattern.instantiate）。

类型洞谓词（结构检查，无需上下文；语义谓词如正负走规则 guard/decide）
"""

from cas.syntax import term as T
from cas.syntax import pattern as P
from cas.errors import BudgetExceeded

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
# 只有洞（PatternVar/PatternSeq）与字面单位元可吸收单位元；非洞子模式必须如实匹配。
_ONE_ID = {}


def _one_identity():
    if not _ONE_ID:
        _ONE_ID.update({"Plus": T.ZERO, "Times": T.ONE})
    return _ONE_ID


def _bind_identity(p, ident, sub):
    """模式参数 p 绑定到单位元：PatternVar 新绑/一致检查，PatternSeq 绑空元组。"""
    if isinstance(p, P.PatternVar):
        if not _pred_ok(p, ident):
            return None
        cur = sub.get(p.name)
        if cur is None:
            s2 = dict(sub)
            s2[p.name] = ident
            return s2
        return sub if cur is ident else None
    if isinstance(p, P.PatternSeq):
        cur = sub.get(p.name)
        if cur is None:
            s2 = dict(sub)
            s2[p.name] = ()
            return s2
        return sub if cur == () else None
    # 字面量：必须就是该单位元
    return sub if p is ident else None


def _all_identity(pats, ident, sub, st, binds=()):
    """剩余模式参数全部吸收单位元。"""
    if not pats:
        yield sub
        return
    s2 = _bind_identity(pats[0], ident, sub)
    if s2 is not None:
        yield from _all_identity(pats[1:], ident, s2, st, binds)


def _match_one_id(pats, ident, tgt, sub, st, binds=()):
    """OneIdentity 通道：模式参数逐个竞争匹配 tgt，其余吸收单位元。"""
    st[0] -= 1
    if st[0] < 0:
        raise BudgetExceeded()
    if not pats:
        return
    p, rest = pats[0], pats[1:]
    # p 消费 tgt，其余全部取单位元
    for s2 in _match(p, tgt, sub, st, binds):
        yield from _all_identity(rest, ident, s2, st, binds)
    # p 吸收单位元，tgt 留给后续参数
    s2 = _bind_identity(p, ident, sub)
    if s2 is not None:
        yield from _match_one_id(rest, ident, tgt, s2, st, binds)


def _restore_db(t, binds):
    """洞在 Bound 体内匹配到的 DB(i) 还原为绑定变量符号。

    de Bruijn 索引只在原绑定作用域内有效；洞绑定值要离开作用域实例化
    模板，若直接携带 DB 索引，重新抽象（mk_bound）时会被整体提升（#1 泄漏）。
    还原为符号后由 replace_at 的 mk_bound 重新抽象成正确索引。
    """
    if isinstance(t, T.DB) and binds and t.i < len(binds):
        return T.S(binds[-1 - t.i])
    return t


def _match(pat, tgt, sub, st, binds=()):
    st[0] -= 1
    if st[0] < 0:
        raise BudgetExceeded()
    # 字面量（Term）：驻留项指针相等即匹配
    if isinstance(pat, T.Term):
        if pat is tgt:
            yield sub
        return
    k = pat.__class__
    if k is P.PatternVar:
        if not _pred_ok(pat, tgt):
            return
        tgt = _restore_db(tgt, binds)
        cur = sub.get(pat.name)
        if cur is None:
            s2 = dict(sub)
            s2[pat.name] = tgt
            yield s2
        elif cur is tgt:
            yield sub
        return
    if k is P.PatternSeq:
        tgt = _restore_db(tgt, binds)
        cur = sub.get(pat.name)
        if cur is None:
            s2 = dict(sub)
            s2[pat.name] = (tgt,)
            yield s2
        elif cur == (tgt,):
            yield sub
        return
    if k is P.PatternCall:
        if isinstance(tgt, T.Expr) and tgt.head is pat.head:
            if pat.head.name in T.AC:
                yield from _match_orderless(list(pat.args), list(tgt.args), sub, st, binds)
            else:
                yield from _match_seq(list(pat.args), list(tgt.args), sub, st, binds)
            return
        ident = _one_identity().get(pat.head.name)
        if ident is not None:
            yield from _match_one_id(list(pat.args), ident, tgt, sub, st, binds)
        return
    return


def _match_seq(pats, terms, sub, st, binds=()):
    if not pats:
        if not terms:
            yield sub
        return
    p = pats[0]
    if isinstance(p, P.PatternSeq):
        n = len(terms)
        for k in range(1, n + 1):
            seg = tuple(_restore_db(x, binds) for x in terms[:k])
            cur = sub.get(p.name)
            if cur is None:
                s2 = dict(sub)
                s2[p.name] = seg
                yield from _match_seq(pats[1:], terms[k:], s2, st, binds)
            else:
                if seg == cur:
                    yield from _match_seq(pats[1:], terms[k:], sub, st, binds)
        return
    if not terms:
        return
    for s2 in _match(p, terms[0], sub, st, binds):
        yield from _match_seq(pats[1:], terms[1:], s2, st, binds)


def _match_orderless(pats, terms, sub, st, binds=()):
    st[0] -= 1
    if st[0] < 0:
        raise BudgetExceeded()
    if not pats:
        if not terms:
            yield sub
        return
    p = pats[0]
    # 字面量快通道：驻留项指针相等（AC 规范化使置换等价化为同一对象）
    if isinstance(p, T.Term):
        if p in terms:
            rest = list(terms)
            rest.remove(p)
            yield from _match_orderless(pats[1:], rest, sub, st, binds)
        return
    if isinstance(p, P.PatternSeq):
        n = len(terms)
        for i in range(n):
            for ln in range(1, n - i + 1):
                seg = tuple(_restore_db(x, binds) for x in terms[i : i + ln])
                rest = terms[:i] + terms[i + ln :]
                cur = sub.get(p.name)
                if cur is None:
                    s2 = dict(sub)
                    s2[p.name] = seg
                    yield from _match_orderless(pats[1:], rest, s2, st, binds)
                elif cur == seg:
                    yield from _match_orderless(pats[1:], rest, sub, st, binds)
        return
    for i, t in enumerate(terms):
        rest = terms[:i] + terms[i + 1 :]
        for s2 in _match(p, t, sub, st, binds):
            yield from _match_orderless(pats[1:], rest, s2, st, binds)


def _sub_key(sub):
    items = []
    for k, v in sub.items():
        if isinstance(v, tuple):
            items.append((k, tuple(x._h for x in v)))
        else:
            items.append((k, v._h))
    return tuple(sorted(items, key=lambda kv: kv[0]))


def matches(pat, tgt, sub=None, budget=10000):
    """pat（Pattern | Term）对 tgt（Term）匹配，产出绑定字典生成器。"""
    st = [budget]
    base = dict(sub) if sub else {}
    seen = set()
    if isinstance(pat, P.PatternVar):
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
