import re

from fractions import Fraction as Fr

import library

from cas import term as T
from cas.term import S, N, mk, INFINITY, TRUE, FALSE, PV, PS
from cas.errors import ParseError

_TOKEN = re.compile(
    r"\s*(?:"
    r"(?P<num>\d+\.\d+|\d+)"
    r"|(?P<seq>\?\?[_A-Za-z]\w*)"
    r"|(?P<pvar>\?[_A-Za-z]\w*(?:::[_A-Za-z]\w*)?)"
    r"|(?P<id>[A-Za-z_]\w*)"
    r"|(?P<op>&&|\|\||==|!=|<=|>=|->|[-+*/^()<>,='])"
    r")"
)

# 句法层原子：属于语言的记号（Special/BVal），不是数学常数，不进图书馆。
# 数学常数一律经 library 按名查询，内核不存名字→原子的副本。
_SYNTAX_ATOMS = {"infinity": INFINITY, "true": TRUE, "false": FALSE}

_BINDERS = {"Integrate", "Sum", "Product", "Limit"}

_PREC = {"=": 1, "==": 2, "!=": 2, "<": 2, ">": 2, "<=": 2, ">=": 2,
         "+": 3, "-": 3, "*": 4, "/": 4, "^": 6}

_HEADMAP = {
    "==": "Eq", "!=": "Ne", "<": "Lt", ">": "Gt", "<=": "Le", ">=": "Ge",
    "+": "Plus", "-": "Plus", "*": "Times", "/": "Times", "^": "Power",
}


def tokenize(s):
    out = []
    i = 0
    while i < len(s):
        m = _TOKEN.match(s, i)
        if not m:
            if s[i].isspace():
                i += 1
                continue
            raise ParseError(f"bad char {s[i]!r} at {i}")
        i = m.end()
        kind = m.lastgroup
        val = m.group(kind)
        out.append((kind, val))
    out.append(("end", ""))
    return out


class Parser:
    """表达式解析器。

    raw 通道（quote 内容，'...' 内部自动切换）：构造走 _intern_expr 纯驻留，
    保留反化简形——不合并同类项/同底幂、不折叠常量，'cos(x)/cos(x)^2 保留为
    Times(cos, Power(cos, -2))；域约束随之保留（dom_condition 递归 Quote 提取）。
    正常通道构造走 mk（AC 拉平排序）。两通道共用同一套文法，仅构造原语不同。
    """

    def __init__(self, toks, raw=False):
        self.toks = toks
        self.i = 0
        self.raw = raw

    # --- 构造原语：两通道唯一的差异点 ---

    def _mk(self, head, args):
        return T._intern_expr(head, tuple(args)) if self.raw \
            else mk(head, tuple(args))

    def _neg(self, e):
        return T._intern_expr(S("Times"), (T.MONE, e)) if self.raw \
            else T.neg(e)

    def _recip(self, e):
        # a/b 的倒数因子即 b^-1（两通道统一；历史上的 ×1 残余已清除）
        return self._mk(S("Power"), (e, T.MONE))

    # --- 文法 ---

    def peek(self):
        return self.toks[self.i]

    def next(self):
        t = self.toks[self.i]
        self.i += 1
        return t

    def expect(self, val):
        k, v = self.next()
        if v != val:
            raise ParseError(f"expected {val!r}, got {v!r}")

    def parse(self):
        e = self.expr(0)
        k, v = self.peek()
        if k != "end":
            raise ParseError(f"unexpected {v!r}")
        return e

    def expr(self, minp):
        left = self.unary()
        while True:
            k, v = self.peek()
            op = None
            if k == "id" and v == "and":
                op, p = "&&", 1
            elif k == "id" and v == "or":
                op, p = "||", 1
            elif k == "op" and v in ("&&", "||"):
                op, p = v, 1
            if op is None and not (k == "op" and _PREC.get(v) is not None):
                break
            if op is not None:
                if p < minp:
                    break
                self.next()
                right = self.expr(p + 1)
                head = S("And") if op == "&&" else S("Or")
                left = self._mk(head, (left, right))
                continue
            p = _PREC.get(v)
            if p is None or p < minp:
                break
            self.next()
            if v == "=":
                v = "=="
            # ^ 右结合（2^3^2 = 2^(3^2)）；其余算子左结合
            right = self.expr(p if v == "^" else p + 1)
            hname = _HEADMAP[v]
            if v == "-":
                right = self._neg(right)
            if v == "/":
                right = self._recip(right)
            left = self._mk(S(hname), (left, right))
        return left

    def unary(self):
        k, v = self.peek()
        if k == "op" and v == "-":
            self.next()
            e = self.unary()
            # 前缀 - 绑定松于 ^：-x^2 = -(x^2)；^ 链右结合
            if self.peek() == ("op", "^"):
                self.next()
                rhs = self.expr(_PREC["^"])
                e = self._mk(S("Power"), (e, rhs))
            return self._neg(e)
        if k == "op" and v == "'":
            self.next()
            # quote 内容保 held 形：本子表达式切 raw 通道，返回后恢复原通道
            old, self.raw = self.raw, True
            try:
                return T.quote(self.expr(1))
            finally:
                self.raw = old
        if k == "op" and v == "(":
            self.next()
            e = self.expr(0)
            self.expect(")")
            return e
        if k == "num":
            self.next()
            f = Fr(v)
            return N(f)
        if k == "seq":
            self.next()
            return PS(v[2:])
        if k == "pvar":
            self.next()
            body = v[1:]
            # 类型洞 ?x::pred（yacas _x_IsNumber 同款）：谓词在匹配时结构检查
            if "::" in body:
                nm, pd = body.split("::", 1)
                return PV(nm, pd)
            return PV(body)
        if k == "id":
            self.next()
            if v in _SYNTAX_ATOMS:
                return _SYNTAX_ATOMS[v]
            d = library.const_by_name(v)
            if d is not None:
                return d.atom
            nk, nv = self.peek()
            if nk == "op" and nv == "(":
                self.next()
                args = []
                if not (self.peek()[0] == "op" and self.peek()[1] == ")"):
                    args.append(self.expr(0))
                    while self.peek() == ("op", ","):
                        self.next()
                        args.append(self.expr(0))
                self.expect(")")
                # 绑定词大小写不敏感（integrate/Integrate 都生成绑定形式）
                bv = v[0].upper() + v[1:] if v else v
                if bv in _BINDERS and len(args) == 2:
                    return self._mk(S(bv), (T.mk_bound(args[1], args[0]),))
                if v == "sqrt" and len(args) == 1:
                    return self._mk(S("Power"), (args[0], N(Fr(1, 2))))
                if v == "ln":
                    v = "Log"
                if v[0].islower() and len(v) > 1 and v not in ("and", "or", "not"):
                    v = v[0].upper() + v[1:]
                return self._mk(S(v), tuple(args))
            return S(v)
        raise ParseError(f"unexpected {v!r}")


def parse(s):
    return Parser(tokenize(s)).parse()
