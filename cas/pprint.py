from cas import term as T
from cas.term import Expr, Int, Rat, Sym, Const, Bound, PatVar, PatSeq, BVal, Special, DB

_PREC = {"Eq": 2, "Ne": 2, "Lt": 2, "Le": 2, "Gt": 2, "Ge": 2, "Plus": 3, "Times": 4, "Power": 6}

_SYM_REPR = {"pi": "π"}


def _atom_str(a):
    if isinstance(a, Sym):
        return _SYM_REPR.get(a.name, a.name)
    if isinstance(a, Const):
        return _SYM_REPR.get(a.name, a.name)
    if isinstance(a, BVal):
        return "true" if a.val else "false"
    if isinstance(a, Int):
        return str(a.v)
    if isinstance(a, Rat):
        return f"{a.f.numerator}/{a.f.denominator}"
    if isinstance(a, Special):
        return a.name
    if isinstance(a, (PatVar, PatSeq)):
        return repr(a)
    if isinstance(a, DB):
        return f"#{a.i}"
    return repr(a)


def _name_of(h):
    low = {"Sin": "sin", "Cos": "cos", "Tan": "tan", "Exp": "exp", "Log": "log", "Abs": "abs"}
    if isinstance(h, Sym):
        return low.get(h.name, h.name.lower() if len(h.name) > 1 else h.name.lower())
    return repr(h)


def to_str(t, prec=0, hint=None):
    if not isinstance(t, Expr):
        if isinstance(t, Bound):
            return to_str(t.body, 0, t.hint)
        return _atom_str(t)
    name = t.head.name
    if name == "Bound":
        pass
    if name == "Quote":
        return "'" + to_str(t.args[0], 0)
    if name in ("Integrate", "Sum", "Product", "Limit") and len(t.args) == 1 and isinstance(t.args[0], Bound):
        b = t.args[0]
        sym = {"Integrate": "∫", "Sum": "Σ", "Product": "Π", "Limit": "lim"}[name]
        return f"{sym}[{to_str(b.body)}] d{b.hint}"
    if name in _PREC:
        p = _PREC[name]
        if name == "Plus":
            parts = []
            for i, a in enumerate(t.args):
                sa = to_str(a, p)
                neg = sa.startswith("-")
                parts.append(sa if i == 0 else ("- " + sa[1:] if neg else "+ " + sa))
            s = " ".join(parts)
        elif name == "Times":
            facs = []
            nums = [a for a in t.args if T.is_num(a)]
            rest = [a for a in t.args if not T.is_num(a)]
            den = None
            keep = []
            for a in rest:
                if (
                    den is None
                    and isinstance(a, Expr)
                    and a.head.name == "Power"
                    and a.args[1] is T.MONE
                ):
                    den = a.args[0]
                else:
                    keep.append(a)
            coef = ""
            for n in nums:
                v = T.num_val(n)
                if v == -1:
                    coef = "-"
                elif v != 1:
                    coef = _atom_str(n)
            for a in keep:
                sa = to_str(a, p)
                if isinstance(a, Expr) and a.head.name in ("Plus",):
                    sa = "(" + sa + ")"
                facs.append(sa)
            body = "*".join(facs) if facs else (coef if coef not in ("", "-") else "1")
            if coef and coef != "-" and facs:
                body = coef + "*" + body
            elif coef == "-":
                body = "-" + body
            elif coef and not facs:
                body = coef
            if den is not None:
                s = body + "/" + to_str(den, 5)
            else:
                s = body
        elif name == "Power":
            b, e = t.args
            sb = to_str(b, p)
            if T.is_num(b) and (T.num_val(b) < 0 or isinstance(b, Rat)):
                sb = "(" + sb + ")"
            se = to_str(e, p + 1)
            s = f"{sb}^{se}"
        else:
            parts = [to_str(a, p + 1) for a in t.args]
            op = T._INFIX.get(name, name)
            s = f" {op} ".join(parts)
        if prec > p:
            return "(" + s + ")"
        return s
    args = ", ".join(to_str(a, 0) for a in t.args)
    return f"{_name_of(t.head)}({args})"
