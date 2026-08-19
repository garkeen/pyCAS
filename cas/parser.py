import re

from fractions import Fraction as Fr

from cas import term as T
from cas.term import S, N, mk, Expr, Sym, PI, E, IU, GAMMA, INFINITY, TRUE, FALSE, PV, PS
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

_CONSTS = {"pi": PI, "e": E, "i": IU, "gamma": GAMMA, "infinity": INFINITY, "true": TRUE, "false": FALSE}

_BINDERS = {"Integrate", "Sum", "Product", "Limit"}

_PREC = {"=": 1, "==": 2, "!=": 2, "<": 2, ">": 2, "<=": 2, ">=": 2,
         "+": 3, "-": 3, "*": 4, "/": 4, "^": 6}


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
    def __init__(self, toks):
        self.toks = toks
        self.i = 0

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
                left = mk(head, (left, right))
                continue
            p = _PREC.get(v)
            if p is None or p < minp:
                break
            self.next()
            if v == "=":
                v = "=="
            # ^ 右结合（2^3^2 = 2^(3^2)）；其余算子左结合
            right = self.expr(p if v == "^" else p + 1)
            headmap = {
                "==": "Eq", "!=": "Ne", "<": "Lt", ">": "Gt", "<=": "Le", ">=": "Ge",
                "+": "Plus", "-": "Plus", "*": "Times", "/": "Times", "^": "Power",
            }
            hname = headmap[v]
            if v == "-":
                right = T.neg(right)
            if v == "/":
                right = T.div(T.ONE, right)
            left = mk(S(hname), (left, right))
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
                e = mk(S("Power"), (e, rhs))
            return T.neg(e)
        if k == "op" and v == "'":
            self.next()
            return T.quote(self.expr(1))
        if k == "op" and v == "(":
            self.next()
            e = self.expr(0)
            self.expect(")")
            return self.postfix(e)
        if k == "num":
            self.next()
            f = Fr(v)
            return self.postfix(N(f))
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
            if v in _CONSTS:
                return self.postfix(_CONSTS[v])
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
                if v in _BINDERS and len(args) == 2:
                    return self.postfix(mk(S(v), (T.mk_bound(args[1], args[0]),)))
                if v == "sqrt" and len(args) == 1:
                    return self.postfix(T.sqrt(args[0]))
                if v == "ln":
                    v = "Log"
                if v[0].islower() and len(v) > 1 and v not in ("and", "or", "not"):
                    v = v[0].upper() + v[1:]
                return self.postfix(mk(S(v), tuple(args)))
            return self.postfix(S(v))
        raise ParseError(f"unexpected {v!r}")

    def postfix(self, e):
        return e


def parse(s):
    return Parser(tokenize(s)).parse()
