from cas import term as T
from cas.term import Expr, Int, Rat, Sym, Const, Bound, PatVar, PatSeq, BVal, Special, DB, S

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
    if isinstance(h, Sym):
        # 打印名来自 FunctionSpec；未注册头回退小写
        from cas.spec import get as _spec_get

        sp = _spec_get(h.name)
        if sp is not None and sp.print_name:
            return sp.print_name
        return h.name.lower()
    return repr(h)


def _postorder(t):
    """显式栈后序遍历（与 simplify._postorder 同构，避免跨模块依赖）。"""
    order = []
    stack = [t]
    while stack:
        u = stack.pop()
        order.append(u)
        if isinstance(u, Expr):
            stack.extend(u.args)
        elif isinstance(u, Bound):
            stack.append(u.body)
    return order


def _wrap(child, need):
    """子节点 (身串, 自身优先级) 在 need 优先级上下文中的括号决策。"""
    s, p = child
    return "(" + s + ")" if need > p else s


_ATOM_P = 100   # 非 _PREC 节点自身优先级：永不需要括号（原递归版只有 _PREC 头查 prec）


def to_str(t, prec=0, hint=None):
    """显式栈后序重建：每节点产出不带外层括号的身串与自身优先级，
    父层按上下文优先级加括号（与原递归版 prec 机制逐案例等价）。"""
    val = {}
    for u in reversed(_postorder(t)):
        if not isinstance(u, Expr):
            if isinstance(u, Bound):
                val[u] = val[u.body]
            else:
                val[u] = (_atom_str(u), _ATOM_P)
            continue
        name = u.head.name
        if name == "Quote":
            val[u] = ("'" + _wrap(val[u.args[0]], 0), _ATOM_P)
            continue
        if name in ("Integrate", "Sum", "Product", "Limit") and len(u.args) == 1 and isinstance(u.args[0], Bound):
            b = u.args[0]
            sym = {"Integrate": "∫", "Sum": "Σ", "Product": "Π", "Limit": "lim"}[name]
            val[u] = (f"{sym}[{_wrap(val[b.body], 0)}] d{b.hint}", _ATOM_P)
            continue
        if name == "Piecewise" and len(u.args) % 2 == 0:
            parts = [
                f"{_wrap(val[u.args[i]], 0)} if {_wrap(val[u.args[i + 1]], 0)}"
                for i in range(0, len(u.args), 2)
            ]
            val[u] = ("piecewise(" + ", ".join(parts) + ")", _ATOM_P)
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
                    # 负整数幂因子 -> 分母（b^-k -> /b^k），支持多个；
                    # 只存 (底, 指数) 不新造项（新项不在后序遍历里，查 val 会 KeyError）
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
                    facs.append(_wrap(val[a], p))   # prec 机制已负责子表达式括号
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
                        sb = _wrap(val[base], 6)   # 分母幂底按 Power 内优先级渲染
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
    # 顶层 prec 只对 _PREC 头生效（与原递归版逐案例等价；原子/函数头不加括号）
    if prec > p and isinstance(t, Expr) and t.head.name in _PREC:
        return "(" + s + ")"
    return s
