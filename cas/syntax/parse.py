"""Expression parser: the term language's own grammar.

Surface names carry no case convention. An identifier reaches a canonical head
**only** through declared data -- the alias table, a constant declaration, a
function declaration or a binder declaration -- each injected as a query by the
caller (`alias_fn` / `const_fn` / `binder_fn`). With no injection a name is a
symbol, so `foo` and `Foo` are two different heads and a lowercase declaration
(`function foo`) is directly reachable from the surface syntax. The syntax layer
therefore knows no mathematical head; it knows the term language's own structure
(ring signature, comparisons, boolean structure, Quote, and binders that the
declaration layer reports as such).
"""
import re

from fractions import Fraction as Fr

from cas.syntax import term as T
from cas.syntax import pattern as P
from cas.syntax.term import S, N, mk, INFINITY, TRUE, FALSE
from cas.errors import ParseError

_TOKEN = re.compile(
    r"\s*(?:"
    r"(?P<num>\d+\.\d+|\d+)"
    r"|(?P<seq>\?\?[_A-Za-z]\w*)"
    r"|(?P<pvar>\?[_A-Za-z]\w*(?:::[_A-Za-z]\w*)?)"
    r"|(?P<db>@\d+)"
    r"|(?P<id>[A-Za-z_]\w*)"
    r"|(?P<op>&&|\|\||==|!=|<=|>=|->|[-+*/^()<>,='])"
    r")"
)

# Syntactic atoms: notation belonging to the language (Special/BVal), not
# mathematical constants, so they do not enter declarations. Mathematical constants
# are always looked up by name from the declaration layer; the kernel keeps no copy
# of a name-to-atom mapping.
_SYNTAX_ATOMS = {"infinity": INFINITY, "true": TRUE, "false": FALSE}

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
    """Expression parser.

    The raw channel (quote contents, entered automatically inside '...') builds
    through intern_expr, which interns without simplifying, preserving the
    anti-normalized shape: like terms and like-base powers are not merged and
    constants are not folded, so 'cos(x)/cos(x)^2 stays as
    Times(cos, Power(cos, -2)) and the domain constraint is preserved with it
    (dom_condition extracts it by recursing through Quote). The normal channel builds
    through mk (AC flattening and ordering). Both channels share one grammar; only
    the construction primitives differ.

    The pattern channel builds calls as PatternCall and ?x/??x as
    PatternVar/PatternSeq, producing a Pattern from cas.syntax.pattern, **not a
    Term**. The rule DSL (LHS/RHS/guard) is parsed through this channel, which is why
    pattern variables cannot reach the term layer.
    """

    def __init__(self, toks, raw=False, pattern=False, constants=None,
                 alias_fn=None, const_fn=None, binder_fn=None):
        self.toks = toks
        self.i = 0
        self.raw = raw
        self.pattern = pattern
        # Constant atom table: a dict means use it (the declaration DSL channel,
        # where the runtime is not ready while templates are parsed at bootstrap);
        # None means use the injected const_fn (the ordinary expression channel,
        # resolved by the frontend shim against the assembled runtime).
        self.constants = constants
        self._alias_fn = alias_fn
        self._const_fn = const_fn
        self._binder_fn = binder_fn

    # --- construction primitives: the only point where the channels differ ---

    def _alias(self, name):
        """Surface name -> canonical head (a declared alias such as ln->Log,
        sqrt->Sqrt).

        The declaration DSL channel (constants injected) skips aliasing, since
        templates are written with canonical heads; the ordinary channel uses the
        injected alias_fn, which the frontend shim supplies from the runtime's
        declared alias table. With no alias_fn the name is returned as-is.
        """
        if self.constants is not None:
            return name
        if self._alias_fn is not None:
            h = self._alias_fn(name)
            return h if h is not None else name
        return name

    def _is_binder(self, head):
        """Whether a canonical head is a declared binder head.

        Binder heads are declaration data (`binder <Head>` in the declaration DSL),
        injected as a query exactly like the alias and constant channels. With no
        injected query nothing is a binder, so the syntax layer on its own knows no
        mathematical head. A surface word reaches this query only after the alias
        table has resolved it, which is what makes a declared surface word such as
        `integrate` produce the declared binder head `Integrate` without any case
        rewriting.
        """
        return self._binder_fn is not None and self._binder_fn(head)

    def _const_atom(self, name):
        """Identifier -> mathematical constant atom (None when absent, so the caller
        degrades to a symbol).

        The DSL channel uses the injected constant table; the ordinary channel uses
        the injected const_fn, which the frontend shim resolves against the assembled
        runtime. With neither, no constant is found and the identifier degrades to a
        symbol.
        """
        if self.constants is not None:
            return self.constants.get(name)
        if self._const_fn is not None:
            return self._const_fn(name)
        return None

    def _mk(self, head, args):
        if self.pattern:
            return P.pcall(head, tuple(args))
        return T.intern_expr(head, tuple(args)) if self.raw \
            else mk(head, tuple(args))

    def _neg(self, e):
        if self.pattern:
            return P.pcall(S("Times"), (T.MONE, e))
        return T.intern_expr(S("Times"), (T.MONE, e)) if self.raw \
            else T.neg(e)

    def _quote(self, e):
        if self.pattern:
            return P.pcall(S("Quote"), (e,))
        return T.quote(e)

    def _recip(self, e):
        # the reciprocal factor of a/b is b^-1 (both channels agree)
        return self._mk(S("Power"), (e, T.MONE))

    # --- grammar ---

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
            # ^ is right associative (2^3^2 = 2^(3^2)); every other operator is left
            # associative
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
            # prefix - binds looser than ^: -x^2 = -(x^2); ^ chains right
            if self.peek() == ("op", "^"):
                self.next()
                rhs = self.expr(_PREC["^"])
                e = self._mk(S("Power"), (e, rhs))
            return self._neg(e)
        if k == "op" and v == "'":
            self.next()
            # quote contents stay held: this subexpression switches to the raw
            # channel and restores the previous channel on return
            old, self.raw = self.raw, True
            try:
                return self._quote(self.expr(1))
            finally:
                self.raw = old
        if k == "op" and v == "(":
            self.next()
            e = self.expr(0)
            self.expect(")")
            return e
        if k == "db":
            self.next()
            # the de Bruijn placeholder `@0` marks the argument slot of a bound body
            # (derivative templates, domain-condition templates); the syntax layer
            # owns binding abstraction and instantiation (mk_bound / lift)
            return T.DB_(int(v[1:]))
        if k == "num":
            self.next()
            f = Fr(v)
            return N(f)
        if k == "seq":
            self.next()
            if not self.pattern:
                raise ParseError(f"pattern hole {v!r} outside pattern context")
            return P.PS(v[2:])
        if k == "pvar":
            self.next()
            if not self.pattern:
                raise ParseError(f"pattern hole {v!r} outside pattern context")
            body = v[1:]
            # typed hole ?x::pred: the predicate is a structural check at match time
            if "::" in body:
                nm, pd = body.split("::", 1)
                return P.PV(nm, pd)
            return P.PV(body)
        if k == "id":
            self.next()
            if v in _SYNTAX_ATOMS:
                return _SYNTAX_ATOMS[v]
            atom = self._const_atom(v)
            if atom is not None:
                return atom
            v = self._alias(v)
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
                # A declared binder word binds its second argument: word(body, var)
                # produces Head(Bound(var, body)), and any further arguments follow
                # the bound body, so the definite-integral word
                # word(body, var, lo, hi) produces Head(Bound(var, body), lo, hi).
                # Which heads are binder words is declaration data (binder_fn), not
                # a table in the syntax layer.
                if self._is_binder(v) and len(args) >= 2:
                    if self.pattern and P.has_holes(args[1]):
                        raise ParseError(
                            "binder pattern with a hole in variable position is not supported")
                    return self._mk(S(v), (T.mk_bound(args[1], args[0]),) + tuple(args[2:]))
                return self._mk(S(v), tuple(args))
            return S(v)
        raise ParseError(f"unexpected {v!r}")


def parse(s, pattern=False, constants=None, alias_fn=None, const_fn=None,
          binder_fn=None):
    """Parse an expression.

    `constants` is an optional name-to-constant-atom table for the declaration DSL
    channel (parsed at bootstrap, when the runtime is not ready, so it injects the
    table instead of calling back into the runtime). The ordinary expression channel
    passes `alias_fn` / `const_fn` / `binder_fn` instead; the frontend shim supplies
    the runtime-backed triple. With none of these, names degrade to symbols, no
    alias is applied and nothing is a binder, so this module depends on neither
    the runtime nor any math module.
    """
    return Parser(tokenize(s), pattern=pattern, constants=constants,
                  alias_fn=alias_fn, const_fn=const_fn,
                  binder_fn=binder_fn).parse()


def atom_notation(atom):
    """The surface spelling of a language atom (None when the atom has no notation).

    The spelling belongs to the language, so it lives next to the atom table
    instead of being repeated by the printer: the source form of an atom that the
    lexer accepts must re-parse to the same atom, and the atom whose notation the
    lexer accepts is asked for here rather than being transcribed a second time.
    """
    for name, a in _SYNTAX_ATOMS.items():
        if a is atom:
            return name
    return None
