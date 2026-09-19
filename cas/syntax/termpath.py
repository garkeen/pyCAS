"""Tree traversal and rewriting: substitution, path addressing
(term_at/replace_at/all_paths), free variables, subterm surgery binding
(_bind_into) and size traversal.

Instantiation lives with the pattern metalanguage in cas/syntax/pattern.py,
because the term layer has no holes.

Dependency note: this module holds only a module reference to term (accessed
as T.xxx inside functions). term.py re-exports these names lazily, so there is
no import cycle.
"""

from cas.syntax import term as T


def subst_raw(t, mapping):
    """Raw structural substitution (no normalization, held form preserved),
    used inside Quote.

    Isomorphic to subst but rebuilds through intern_expr, so Times/Power do
    not merge same-base powers and the held structure of the term is kept.
    """
    if not mapping:
        return t
    order = []
    stack = [t]
    while stack:
        u = stack.pop()
        order.append(u)
        if isinstance(u, T.Expr):
            if u in mapping:
                continue
            stack.extend(u.args)
        elif isinstance(u, T.Bound):
            stack.append(u.body)
    val = {}
    for u in reversed(order):
        hit = mapping.get(u)
        if hit is not None:
            val[u] = hit
        elif isinstance(u, T.Expr):
            val[u] = T.intern_expr(u.head, tuple(val[a] for a in u.args))
        elif isinstance(u, T.Bound):
            val[u] = T.mk_bound_canon(u.hint, val[u.body])
        else:
            val[u] = u
    return val[t]


def subst(t, mapping):
    """Substitution, rebuilt bottom-up on an explicit work stack so that deep
    expressions never hit the Python recursion limit.

    Inside Quote the raw channel is used, preserving the held structure
    instead of merging same-base powers and like terms.
    """
    if not mapping:
        return t
    # Explicit-stack postorder. A Bound body is always entered: its free
    # variables must be substituted and capture must be prevented.
    order = []
    stack = [t]
    while stack:
        u = stack.pop()
        order.append(u)
        if isinstance(u, T.Expr):
            if u in mapping:
                continue  # a substituted subtree is not traversed further
            if isinstance(u.head, T.Sym) and u.head.name == "Quote":
                continue  # Quote contents do not rebuild through mk
            stack.extend(u.args)
        elif isinstance(u, T.Bound):
            stack.append(u.body)
    val = {}
    for u in reversed(order):
        hit = mapping.get(u)
        if hit is not None:
            val[u] = hit
        elif isinstance(u, T.Expr):
            if isinstance(u.head, T.Sym) and u.head.name == "Quote":
                # Quote preserves held structure: raw rebuild, no normalization.
                val[u] = T.intern_expr(
                    u.head, tuple(subst_raw(a, mapping) for a in u.args))
            else:
                val[u] = T.mk(u.head, tuple(val[a] for a in u.args))
        elif isinstance(u, T.Bound):
            val[u] = T.mk_bound_canon(u.hint, val[u.body])
        else:
            val[u] = u
    return val[t]


def free_vars(t, acc=None):
    if acc is None:
        acc = set()
    if isinstance(t, T.Sym):
        acc.add(t)
    elif isinstance(t, T.Expr):
        for a in t.args:
            free_vars(a, acc)
    elif isinstance(t, T.Bound):
        free_vars(t.body, acc)
    return acc


def term_at(t, path):
    for i in path:
        if isinstance(t, T.Expr):
            t = t.args[i]
        elif isinstance(t, T.Bound):
            # Crossing a binder opens its body: de Bruijn indices become the
            # bound symbol, so the subterm leaves the binding context and can be
            # matched/evaluated as a free-symbol tree. replace_at re-abstracts
            # it through mk_bound when putting it back.
            t = T.lift(t.body, T.S(t.hint), 0)
        else:
            raise IndexError(path)
    return t


def _bind_into(t, var, depth=0):
    """Bind the free variable `var` in an opened body back to a de Bruijn
    index, without touching existing DB references.

    Unlike _abstract, this never shifts DB(i >= depth) already present in the
    body: replace_at crosses an already-bound layer whose body may hold outer
    DB references, and those must stay as they are.
    """
    if isinstance(t, T.Sym):
        return T.DB_(depth) if t is var else t
    if isinstance(t, T.Expr):
        return T.mk(t.head, tuple(_bind_into(a, var, depth) for a in t.args))
    if isinstance(t, T.Bound):
        return T.mk_bound_canon(t.hint, _bind_into(t.body, var, depth + 1))
    return t


def replace_at(t, path, v):
    if not path:
        return v
    i = path[0]
    if isinstance(t, T.Expr):
        args = list(t.args)
        args[i] = replace_at(args[i], path[1:], v)
        return T.mk(t.head, tuple(args))
    if isinstance(t, T.Bound):
        # Open the current layer, substitute recursively, then bind only the
        # current layer's variable back; outer DB references stay untouched.
        var = T.S(t.hint)
        inner = replace_at(T.lift(t.body, var, 0), path[1:], v)
        return T.mk_bound_canon(t.hint, _bind_into(inner, var, 0))
    raise IndexError(path)


def all_paths(t, base=()):
    yield base
    if isinstance(t, T.Expr):
        for i, a in enumerate(t.args):
            yield from all_paths(a, base + (i,))
    elif isinstance(t, T.Bound):
        yield from all_paths(t.body, base + (0,))


def postorder(t):
    """Explicit-stack postorder traversal, safe for deep expressions because it
    never relies on the Python recursion stack.

    This is the single implementation in the system: pprint and the simplifier
    used to hold isomorphic private copies.
    """
    order = []
    stack = [t]
    while stack:
        u = stack.pop()
        order.append(u)
        if isinstance(u, T.Expr):
            stack.extend(u.args)
        elif isinstance(u, T.Bound):
            stack.append(u.body)
    return order
