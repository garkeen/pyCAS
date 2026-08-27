from cas import term as T
from cas.term import S, Int, Rat
import library

# 函数头定义域条件注入点：{head_name -> callable(t) -> [constraint]}。
# 内核不硬连任何函数声明总表；宿主在启动时按需注册。
DOM_HOOKS = {}


def dom_condition(t, out=None):
    """递归提取定义域约束（纯结构，不判值）。

    Power 约束为结构性通用规则：负整数幂 a^-k -> a≠0；偶分母有理幂
    a^(p/q) -> a≥0；负有理幂 a^-e：偶分母 -> a>0（非负且非零），
    奇分母 -> a≠0。其余函数头经 DOM_HOOKS 注入。
    """
    if out is None:
        out = []
    if isinstance(t, T.Expr):
        name = t.head.name
        if name == "Power":
            b, e = t.args
            if isinstance(e, Int) and e.v < 0:
                out.append(T.mk(S("Ne"), (b, T.ZERO)))
            elif isinstance(e, Rat):
                if e.f >= 0 and e.f.denominator % 2 == 0:
                    out.append(T.mk(S("Ge"), (b, T.ZERO)))
                elif e.f < 0:
                    if e.f.denominator % 2 == 0:
                        out.append(T.mk(S("Gt"), (b, T.ZERO)))
                    else:
                        out.append(T.mk(S("Ne"), (b, T.ZERO)))
        else:
            h = DOM_HOOKS.get(name)
            if h is not None:
                out.extend(h(t))
            else:
                fn = library.lookup_domain_cond(name)
                if fn is not None:
                    out.extend(fn(t))
        for a in t.args:
            dom_condition(a, out)
    return out


class Domain:
    name = "?"

    def nonneg(self, t, ctx=None):
        return None

    def pos(self, t, ctx=None):
        return None

    def contains(self, t):
        return None


class RealDomain(Domain):
    name = "R"

    def nonneg(self, t, ctx=None):
        if T.is_num(t):
            return T.sign_num(t) >= 0
        if library.const_positive(t) is True:
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
                    and self.pos(b, ctx) is True
                ):
                    return True
            if name == "Abs":
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

    def pos(self, t, ctx=None):
        if T.is_num(t):
            return T.sign_num(t) > 0
        if library.const_positive(t) is True:
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

    def contains(self, t):
        if T.is_num(t) or library.const_real(t) is True:
            return True
        if isinstance(t, T.Sym):
            return True
        if isinstance(t, T.Expr):
            name = t.head.name
            if name == "Power":
                b, e = t.args
                if (
                    isinstance(e, T.Rat)
                    and self.contains(b) is True
                    and self.nonneg(b) is True
                ):
                    return True
                if isinstance(e, T.Int):
                    return True
            if name == "Abs":
                return True
        return None


class RationalDomain(Domain):
    name = "Q"

    def nonneg(self, t, ctx=None):
        if T.is_num(t):
            return T.sign_num(t) >= 0
        return None

    def pos(self, t, ctx=None):
        if T.is_num(t):
            return T.sign_num(t) > 0
        return None

    def contains(self, t):
        return T.is_num(t) or None


class IntegerDomain(Domain):
    name = "Z"

    def nonneg(self, t, ctx=None):
        if isinstance(t, T.Int):
            return t.v >= 0
        return None

    def pos(self, t, ctx=None):
        if isinstance(t, T.Int):
            return t.v > 0
        return None

    def contains(self, t):
        return isinstance(t, T.Int) or None


class ComplexDomain(Domain):
    name = "C"

    def nonneg(self, t, ctx=None):
        return None

    def pos(self, t, ctx=None):
        return None

    def contains(self, t):
        if isinstance(t, T.Sym):
            return False
        return True


R = RealDomain()
Q = RationalDomain()
Z = IntegerDomain()
C = ComplexDomain()

DEFAULT_DOMAIN = R


def domain_of(name):
    for d in (R, Q, Z, C):
        if d.name == name:
            return d
    return R