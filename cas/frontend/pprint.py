from cas.runtime import dispatch as rt

from cas.syntax import term as T
from cas.syntax import pattern as P
from cas.syntax.parse import atom_notation
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

    An atom whose notation the lexer accepts asks the syntax layer for that notation;
    an atom without one (the empty solution set, Undefined) has no parseable spelling
    and falls back to the display spelling.
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
        if src:
            n = atom_notation(a)
            if n is not None:
                return n
        if a is T.EMPTY_SET:
            return "{}"
        return a.name
    if isinstance(a, DB):
        # the lexer's placeholder notation is `@n` (`#n` is the template display form
        # and is not a token), so the source form uses the notation the lexer accepts
        return f"@{a.i}" if src else f"#{a.i}"
    return repr(a)


def _name_of(h, src=False):
    """The spelling of a head: the declared print name when there is one, else the
    display name (lowercased) or, in source mode, the canonical head name.

    The parser holds no case convention, so the source form must emit a spelling the
    declarations map back to this head: a lowercased undeclared head would re-parse as
    a different head. The display form keeps the friendly lowercase because it is not
    meant to be re-parsed. A declared print name resolves through the alias table,
    which is what makes the source form of a declared function round-trip.
    """
    if isinstance(h, Sym):
        pn = rt.print_name(h.name)
        if pn is not None:
            return pn
        return h.name if src else h.name.lower()
    return repr(h)


def _wrap(child, need):
    """Parenthesize decision for a child (body string, own precedence) in a context
    of precedence `need`."""
    s, p = child
    return "(" + s + ")" if need > p else s


def _call_str(name, val, args):
    """Canonical call spelling of a structure: its head name plus its arguments.

    The parser reproduces a call of any head by that name, so this is the source form
    of a container whose display notation (set braces, interval brackets, an infix
    union) is not part of the lexer.
    """
    return f"{name}(" + ", ".join(_wrap(val[a], 0) for a in args) + ")"


# Display notation of the standard binder heads: presentation only. Display mode
# is not promised to re-parse, so the friendly symbols may live in a table; the
# **source** form never consults it (see the declared-binder branch of to_str). A
# declared binder without an entry falls back to the canonical call spelling with
# the bound variable visible, since there is no notation to invent for it.
_BINDER_SYMBOLS = {"Integrate": "∫", "Sum": "Σ", "Product": "Π", "Limit": "lim"}


def _binder_display(u, b, ob):
    """Display spelling of one declared binder node (presentation only).

    The definite-integral shape carries its limits; the four traditional words
    keep their symbol; anything else prints as a call so the bound variable
    stays visible.
    """
    if u.head.name == "DefIntegrate" and len(u.args) == 3:
        lo, hi = u.args[1], u.args[2]
        return f"∫_{to_str(lo)}^{to_str(hi)}[{to_str(ob)}] d{b.hint}"
    sym = _BINDER_SYMBOLS.get(u.head.name)
    if sym is not None and len(u.args) == 1:
        return f"{sym}[{to_str(ob)}] d{b.hint}"
    parts = [to_str(ob), b.hint] + [to_str(a) for a in u.args[1:]]
    return f"{_name_of(u.head)}({', '.join(parts)})"


_ATOM_P = 100   # own precedence of a node absent from _PREC: never needs parentheses


def to_str(t, prec=0, hint=None, src=False):
    """Explicit-stack postorder rebuild: each node yields a body string without outer
    parentheses plus its own precedence, and the parent adds parentheses by context
    precedence (case-for-case equivalent to the original recursive precedence
    mechanism).

    With src=True it emits a parseable source form: a declared binder head prints
    as a canonical call `Head(body, var, ...)` -- binder recognition runs on the
    canonical head after alias resolution, so the emitted spelling always
    re-parses, and a newly declared binder or a renamed surface word needs no
    printer change. Container heads print as canonical calls (Piecewise(...),
    FiniteSet(...), Interval(...), Union(...)) instead of set notation the lexer
    does not accept. Every spelling the source form emits therefore re-parses to
    the same term.
    """
    val = {}
    for u in reversed(postorder(t)):
        if not isinstance(u, Expr):
            if isinstance(u, Bound):
                # A Bound alone has no notation: only the parent node knows whether
                # a declared binder head can render the binding.
                val[u] = val[u.body]
            else:
                val[u] = (_atom_str(u, src), _ATOM_P)
            continue
        name = u.head.name
        if name == "Quote":
            val[u] = ("'" + _wrap(val[u.args[0]], 0), _ATOM_P)
            continue
        if u.args and isinstance(u.args[0], Bound) \
                and isinstance(u.head, Sym) and rt.is_binder(u.head.name):
            # A declared binder head, asked of the same runtime query the parser
            # uses: no binder head name is a literal here. The source form is the
            # canonical head with body and bound variable (plus trailing
            # arguments); alias resolution maps a surface word to the canonical
            # head, where binder recognition runs, so this spelling re-parses even
            # for a fresh binder or after the surface word was renamed.
            b = u.args[0]
            _v, ob = T.open_bound(b)
            if src:
                parts = [to_str(ob, src=True), b.hint]
                parts.extend(to_str(a, src=True) for a in u.args[1:])
                val[u] = (f"{u.head.name}(" + ", ".join(parts) + ")", _ATOM_P)
            else:
                val[u] = (_binder_display(u, b, ob), _ATOM_P)
            continue
        if name == "Piecewise" and len(u.args) % 2 == 0:
            if src:
                val[u] = (_call_str(name, val, u.args), _ATOM_P)
            else:
                parts = [
                    f"{_wrap(val[u.args[i]], 0)} if {_wrap(val[u.args[i + 1]], 0)}"
                    for i in range(0, len(u.args), 2)
                ]
                val[u] = ("piecewise(" + ", ".join(parts) + ")", _ATOM_P)
            continue
        if name == "FiniteSet":
            if src:
                val[u] = (_call_str(name, val, u.args), _ATOM_P)
            else:
                val[u] = ("{" + ", ".join(_wrap(val[a], 0) for a in u.args) + "}", _ATOM_P)
            continue
        if name == "Interval" and len(u.args) == 4:
            if src:
                val[u] = (_call_str(name, val, u.args), _ATOM_P)
            else:
                lo, hi, lo_o, hi_o = u.args
                lb = "(" if (isinstance(lo_o, BVal) and lo_o.val) else "["
                rb = ")" if (isinstance(hi_o, BVal) and hi_o.val) else "]"
                val[u] = (f"{lb}{_wrap(val[lo], 0)}, {_wrap(val[hi], 0)}{rb}", _ATOM_P)
            continue
        if name == "Union":
            if src:
                val[u] = (_call_str(name, val, u.args), _ATOM_P)
            else:
                val[u] = (" U ".join(_wrap(val[a], 0) for a in u.args), _ATOM_P)
            continue
        if name == "O" and len(u.args) == 1:
            val[u] = ("O(" + _wrap(val[u.args[0]], 0) + ")", _ATOM_P)
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
        # An undeclared head (or a declared one used without a bound first
        # argument): a Bound renders as its body, because there is no notation
        # that could re-parse the binding; declared binders were rendered above
        # with the variable kept.
        args = ", ".join(_wrap(val[a], 0) for a in u.args)
        val[u] = (f"{_name_of(u.head, src)}({args})", _ATOM_P)
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
    return f"{_name_of(p.head, src)}({args})"
