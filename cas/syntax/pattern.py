# -*- coding: utf-8 -*-
"""模式元语言（v4 §5.2 / 不变量 2）：模式不是项。

`PatternVar` / `PatternSeq` 不再是 `Term` 子类，从而**不可能**出现在用户
表达式、域投影与数学判等中——项层只装数学对象。

字面量直接以 `Term` 充当模式：驻留项的指针相等即字面匹配，无需包装类型。
故模式参数的类型是 `Pattern | Term`；本模块记作 PatternLike。

规则声明（DSL）经 loader 以 pattern 模式解析，产物是本模块的 Pattern；
模板实例化 `instantiate` 产出 Term。模式变量只在匹配与实例化两处出现。
"""

from cas.syntax import term as T
from cas.errors import BudgetExceeded, ParseError

_hp = 0


def _next_hp():
    global _hp
    _hp += 1
    return _hp


class Pattern:
    """模式封闭层次基类：驻留指针语义，与 Term 同构。"""

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
        self.head = head                  # Term（符号）
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
    """AC 头的句法折叠：与项层 _flatten_ac 同构（拉平同类嵌套 + 确定性排序）。"""
    flat = []
    for a in args:
        if isinstance(a, PatternCall) and a.head is head:
            flat.extend(a.args)
        else:
            flat.append(a)
    return sorted(flat, key=sort_key)


def pcall(head, args):
    """PatternCall 驻留构造器：AC 头做与项层一致的拉平+排序。"""
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
    """模式排序键。项沿用 T.sort_key，保证字面量之间的相对序与项层一致。"""
    if isinstance(p, T.Term):
        return (10,) + T.sort_key(p)
    k = p.__class__
    if k is PatternVar:
        return (0, p.name, p.pred or "")
    if k is PatternSeq:
        return (1, p.name)
    return (11, T.sort_key(p.head), tuple(sort_key(a) for a in p.args))


def has_holes(p):
    """是否含模式洞。Term 恒为 False（不变量 2：项里不可能有洞）。"""
    if isinstance(p, T.Term):
        return False
    if p.__class__ is PatternCall:
        return any(has_holes(a) for a in p.args)
    return True


def root_key(p):
    """规则索引键：AC 头按头名分桶，洞归 '*'（与项层 root_key 同构）。"""
    if isinstance(p, T.Term):
        if isinstance(p, T.Expr):
            return p.head.name
        return p.__class__.__name__ + ":" + repr(p)
    if p.__class__ is PatternCall:
        return p.head.name
    return "*"


def instantiate(pat, sub):
    """模板实例化：Pattern -> Term。

    未绑定的洞（模板变量未被模式覆盖）是规则声明缺陷——显式报错，绝不让
    模式变量漏进项层（那正是 v4 要消除的泄漏）。
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
        # quote 内部保 held 结构：raw 重建（不 AC 规范化）
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
    """instantiate 的 held 通道：重建走 _intern_expr，不做 AC 规范化。"""
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
