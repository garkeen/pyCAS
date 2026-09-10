from cas.runtime import dispatch as rt

from cas.syntax import term as T
from cas.syntax import pattern as P
from cas.syntax.term import Expr, Int, Rat, Sym, Const, Bound, BVal, Special, DB, S
from cas.syntax.termpath import postorder

_PREC = {"Eq": 2, "Ne": 2, "Lt": 2, "Le": 2, "Gt": 2, "Ge": 2, "Plus": 3, "Times": 4, "Power": 6}


def _atom_str(a, src=False):
    """原子渲染。

    Sym 是用户符号，不做任何重映射——重映射会让名为 pi 的自定义符号被
    印成 π。只有图书馆声明的常数才吃 print_name。

    src=True（可解析源码形）一律输出内部名：展示名 π/γ 不在词法里，
    输出即不可重解析——展示与源码是两种用途，各走各的。
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
    """子节点 (身串, 自身优先级) 在 need 优先级上下文中的括号决策。"""
    s, p = child
    return "(" + s + ")" if need > p else s


_ATOM_P = 100   # 非 _PREC 节点自身优先级：永不需要括号（原递归版只有 _PREC 头查 prec）


def to_str(t, prec=0, hint=None, src=False):
    """显式栈后序重建：每节点产出不带外层括号的身串与自身优先级，
    父层按上下文优先级加括号（与原递归版 prec 机制逐案例等价）。

    src=True 时输出可解析源码形式（绑定词输出函数形态 integrate(f,x)/sum(f,x)/
    product(f,x)/limit(f,x,pt)），供 % 历史展开后重新解析。
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
            _v, ob = T.open_bound(b)   # DB 索引还原为绑定变量名再渲染
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
            # 原样大写输出：parser 对小写头自动首字母大写（rootof -> Rootof
            # != RootOf），round-trip 要求精确形态
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
                if isinstance(e, Rat):
                    se = "(" + se + ")"   # 3^1/2 有歧义（^优先于/），分数指数必加括号
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


# ---------------------------------------------------------------------------
# 模式渲染（v4 §5.2 模式元语言）：规则清单展示，输出可重解析的 DSL 形
# ---------------------------------------------------------------------------

def _pat_prec(a):
    if isinstance(a, P.PatternCall) and isinstance(a.head, Sym) and a.head.name in _PREC:
        return _PREC[a.head.name]
    return _ATOM_P


def pat_to_str(p, src=False):
    """模式渲染。字面项交 to_str；洞输出 ?name / ??name / ?name::pred；
    PatternCall 按 _PREC/_INFIX 中缀渲染，与项打印同形。"""
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
