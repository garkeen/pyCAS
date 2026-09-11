from cas.runtime import dispatch as rt

from cas.syntax import term as T
from cas.syntax import pattern as P
from cas.syntax.term import Expr, Int, Rat, Sym, Const, Bound, BVal, Special, DB
from cas.syntax.termpath import postorder

_PREC = {"Eq": 2, "Ne": 2, "Lt": 2, "Le": 2, "Gt": 2, "Ge": 2, "Plus": 3, "Times": 4, "Power": 6}


def _atom_str(a, src=False):
    """Render an atom.

    Sym is a user symbol and is never remapped -- remapping would print a custom
    symbol named pi as the constant pi. Only constants declared in the declaration
    layer take a print_name.

    src=True (parseable source form) always emits the internal name: the display
    names for pi/gamma are not in the lexer, so emitting them would be unparseable.
    Display and source are two purposes and take separate routes.
    """
    if isinstance(a, Sym):
        return a.name
    if isinstance(a, Const):
        if src:
            return a.name
        d = rt.const_by_atom(a)
        return d.print_name if d is not None else a.name
    if isinstance(a, BVal):
        return "true" if a.val else "false"
    if isinstance(a, Int):
        return str(a.v)
    if isinstance(a, Rat):
        return f"{a.f.numerator}/{a.f.denominator}"
    if isinstance(a, Special):
        if a is T.EMPTY_SET:
            return "{}"
        return a.name
    if isinstance(a, DB):
        return f"#{a.i}"
    return repr(a)


def _name_of(h):
    if isinstance(h, Sym):
        pn = rt.print_name(h.name)
        return pn if pn is not None else h.name.lower()
    return repr(h)


def _wrap(child, need):
    """Parenthesize decision for a child (body string, own precedence) in a context
    of precedence `need`."""
    s, p = child
    return "(" + s + ")" if need > p else s


_ATOM_P = 100   # own precedence of a node absent from _PREC: never needs parentheses


def to_str(t, prec=0, hint=None, src=False):
    """Explicit-stack postorder rebuild: each node yields a body string without outer
    parentheses plus its own precedence, and the parent adds parentheses by context
    precedence (case-for-case equivalent to the original recursive precedence
    mechanism).

    With src=True it emits a parseable source form (binder words print as function
    calls integrate(f,x)/sum(f,x)/product(f,x)/limit(f,x,pt)) so that a % history
    expansion can be reparsed.
    """
    val = {}
    for u in reversed(postorder(t)):
        if not isinstance(u, Expr):
            if isinstance(u, Bound):
                val[u] = val[u.body]
            else:
                val[u] = (_atom_str(u, src), _ATOM_P)
            continue
        name = u.head.name
        if name == "Quote":
            val[u] = ("'" + _wrap(val[u.args[0]], 0), _ATOM_P)
            continue
        if name == "DefIntegrate" and len(u.args) == 3 and isinstance(u.args[0], Bound):
            b, lo, hi = u.args
            _v, ob = T.open_bound(b)
            if src:
                val[u] = (f"int({to_str(ob, src=True)}, {b.hint}, "
                          f"{to_str(lo, src=True)}, {to_str(hi, src=True)})", _ATOM_P)
            else:
                val[u] = (f"∫_{to_str(lo)}^{to_str(hi)}[{to_str(ob)}] d{b.hint}", _ATOM_P)
            continue
        if name in ("Integrate", "Sum", "Product", "Limit") and len(u.args) == 1 and isinstance(u.args[0], Bound):
            b = u.args[0]
            sym = {"Integrate": "∫", "Sum": "Σ", "Product": "Π", "Limit": "lim"}[name]
            fn = {"Integrate": "integrate", "Sum": "sum", "Product": "product", "Limit": "limit"}[name]
            _v, ob = T.open_bound(b)   # restore the DB index to the bound variable name before rendering
            if src:
                val[u] = (f"{fn}({to_str(ob, src=True)}, {b.hint})", _ATOM_P)
            else:
                val[u] = (f"{sym}[{to_str(ob)}] d{b.hint}", _ATOM_P)
            continue
        if name == "Piecewise" and len(u.args) % 2 == 0:
            parts = [
                f"{_wrap(val[u.args[i]], 0)} if {_wrap(val[u.args[i + 1]], 0)}"
                for i in range(0, len(u.args), 2)
            ]
            val[u] = ("piecewise(" + ", ".join(parts) + ")", _ATOM_P)
            continue
        if name == "FiniteSet":
            val[u] = ("{" + ", ".join(_wrap(val[a], 0) for a in u.args) + "}", _ATOM_P)
            continue
        if name == "Interval" and len(u.args) == 4:
            lo, hi, lo_o, hi_o = u.args
            lb = "(" if (isinstance(lo_o, BVal) and lo_o.val) else "["
            rb = ")" if (isinstance(hi_o, BVal) and hi_o.val) else "]"
            val[u] = (f"{lb}{_wrap(val[lo], 0)}, {_wrap(val[hi], 0)}{rb}", _ATOM_P)
            continue
        if name == "Union":
            val[u] = (" U ".join(_wrap(val[a], 0) for a in u.args), _ATOM_P)
            continue
        if name == "O" and len(u.args) == 1:
            val[u] = ("O(" + _wrap(val[u.args[0]], 0) + ")", _ATOM_P)
            continue
        if name == "RootOf" and len(u.args) == 2:
            # Emit the exact capitalized form: the parser capitalizes the first letter
            # of a lowercase head (rootof -> Rootof, which differs from RootOf), and
            # round-tripping requires the exact shape.
            val[u] = (f"RootOf({_wrap(val[u.args[0]], 0)}, {val[u.args[1]][0]})", _ATOM_P)
            continue
        if name in _PREC:
            p = _PREC[name]
            if name == "Plus":
                parts = []
                for i, a in enumerate(u.args):
                    sa = _wrap(val[a], p)
                    neg = sa.startswith("-")
                    parts.append(sa if i == 0 else ("- " + sa[1:] if neg else "+ " + sa))
                s = " ".join(parts)
            elif name == "Times":
                facs = []
                nums = [a for a in u.args if T.is_num(a)]
                rest = [a for a in u.args if not T.is_num(a)]
                dens = []
                keep = []
                for a in rest:
                    # negative integer power factor -> denominator (b^-k -> /b^k),
                    # several allowed; store only (base, exponent) and never build a
                    # new term, since a new term is not in the postorder and looking it
                    # up in val would raise KeyError
                    if (
                        isinstance(a, Expr)
                        and a.head.name == "Power"
                        and isinstance(a.args[1], T.Int)
                        and a.args[1].v < 0
                    ):
                        dens.append((a.args[0], -a.args[1].v))
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
                    facs.append(_wrap(val[a], p))   # the precedence mechanism already parenthesizes subexpressions
                body = "*".join(facs) if facs else (coef if coef not in ("", "-") else "1")
                if coef and coef != "-" and facs:
                    body = coef + "*" + body
                elif coef == "-":
                    body = "-" + body
                elif coef and not facs:
                    body = coef
                if dens:
                    ds = []
                    for base, be in dens:
                        sb = _wrap(val[base], 6)   # render the denominator power base at Power precedence
                        if T.is_num(base) and (T.num_val(base) < 0 or isinstance(base, Rat)):
                            sb = "(" + sb + ")"
                        ds.append(sb if be == 1 else f"{sb}^{be}")
                    den_s = ds[0] if len(ds) == 1 else "(" + "*".join(ds) + ")"
                    s = body + "/" + den_s
                else:
                    s = body
            elif name == "Power":
                b, e = u.args
                sb = _wrap(val[b], p)
                if T.is_num(b) and (T.num_val(b) < 0 or isinstance(b, Rat)):
                    sb = "(" + sb + ")"
                se = _wrap(val[e], p + 1)
                if isinstance(e, Rat):
                    se = "(" + se + ")"   # 3^1/2 is ambiguous (^ binds tighter than /), so a fractional exponent needs parentheses
                s = f"{sb}^{se}"
            else:
                parts = [_wrap(val[a], p + 1) for a in u.args]
                op = T._INFIX.get(name, name)
                s = f" {op} ".join(parts)
            val[u] = (s, p)
            continue
        args = ", ".join(_wrap(val[a], 0) for a in u.args)
        val[u] = (f"{_name_of(u.head)}({args})", _ATOM_P)
    s, p = val[t]
    # top-level precedence only applies to _PREC heads (case-for-case equivalent to
    # the original recursive version; atoms and function heads get no parentheses)
    if prec > p and isinstance(t, Expr) and t.head.name in _PREC:
        return "(" + s + ")"
    return s


# ---------------------------------------------------------------------------
# Pattern rendering: rule listing display, emitting a reparsable DSL form
# ---------------------------------------------------------------------------

def _pat_prec(a):
    if isinstance(a, P.PatternCall) and isinstance(a.head, Sym) and a.head.name in _PREC:
        return _PREC[a.head.name]
    return _ATOM_P


def pat_to_str(p, src=False):
    """Render a pattern. A literal term goes to to_str; a hole prints as
    ?name / ??name / ?name::pred; a PatternCall renders infix via _PREC/_INFIX,
    matching term printing."""
    if isinstance(p, T.Term):
        return to_str(p, src=src)
    if isinstance(p, P.PatternVar):
        return "?" + p.name + (("::" + p.pred) if p.pred else "")
    if isinstance(p, P.PatternSeq):
        return "??" + p.name
    name = p.head.name if isinstance(p.head, Sym) else repr(p.head)
    if name in _PREC:
        pr = _PREC[name]
        if name == "Power":
            b, e = p.args
            sb = _wrap((pat_to_str(b, src), _pat_prec(b)), pr)
            se = _wrap((pat_to_str(e, src), _pat_prec(e)), pr + 1)
            return f"{sb}^{se}"
        parts = [_wrap((pat_to_str(a, src), _pat_prec(a)), pr + 1) for a in p.args]
        return f" {T._INFIX.get(name, name)} ".join(parts)
    args = ", ".join(pat_to_str(a, src) for a in p.args)
    return f"{_name_of(p.head)}({args})"
