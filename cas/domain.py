from cas import term as T
from cas.term import PI, E, S, Int, Rat


def dom_condition(t, out=None):
    if out is None:
        out = []
    if isinstance(t, T.Expr):
        name = t.head.name
        if name == "Log":
            out.append(T.mk(S("Gt"), (t.args[0], T.ZERO)))
        elif name == "Power":
            b, e = t.args
            if isinstance(e, Int) and e.v < 0:
                out.append(T.mk(S("Ne"), (b, T.ZERO)))
            elif isinstance(e, Rat):
                if e.f.denominator % 2 == 0:
                    out.append(T.mk(S("Ge"), (b, T.ZERO)))
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
        if t is PI or t is E:
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
        if t is PI or t is E:
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
        if T.is_num(t) or t is PI or t is E:
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