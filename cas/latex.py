r"""LaTeX 输出（纯展示层，maxima tex 同款定位）。

显式栈后序重建（与 pprint.to_str 同构）：每节点产出 LaTeX 身串，
父层按结构需要包裹 \left( \right)。不追求完备括号决策，
覆盖教科书常用形态：分式/根式/幂/三角/积分/分段/比较/逻辑。
"""

from fractions import Fraction as Fr

from cas import term as T
from cas.term import Expr, Int, Rat, Sym, Const, Bound, Special, DB, BVal


def _atom(u):
    if isinstance(u, Int):
        return str(u.v)
    if isinstance(u, Rat):
        f = u.f
        sign = "-" if f < 0 else ""
        return f"{sign}\\frac{{{abs(f.numerator)}}}{{{f.denominator}}}"
    if isinstance(u, Const):
        return {"pi": "\\pi", "e": "e", "i": "i", "gamma": "\\gamma"}.get(u.name, u.name)
    if isinstance(u, Special):
        if u is T.EMPTY_SET:
            return "\\varnothing"
        return {"Infinity": "\\infty", "Undefined": "\\text{undefined}"}.get(u.name, u.name)
    if isinstance(u, Sym):
        return u.name.replace("_", "\\_")
    if isinstance(u, BVal):
        return "\\top" if u.val else "\\bot"
    if isinstance(u, DB):
        return f"\\#{u.i}"
    if isinstance(u, T.PatVar):
        return "?" + u.name
    if isinstance(u, T.PatSeq):
        return "??" + u.name
    return str(u)


_CMP = {"Eq": "=", "Ne": "\\ne", "Lt": "<", "Le": "\\le", "Gt": ">", "Ge": "\\ge"}


def _parens(s):
    return "\\left(" + s + "\\right)"


def _name_of(h):
    if isinstance(h, Sym):
        from cas.spec import get as _spec_get

        sp = _spec_get(h.name)
        if sp is not None and sp.print_name:
            return "\\" + sp.print_name
        return "\\" + h.name.lower() if len(h.name) > 1 else h.name.lower()
    return str(h)


def to_latex(t):
    """term -> LaTeX 字符串。"""
    val = {}
    order = []
    stack = [t]
    while stack:
        u = stack.pop()
        order.append(u)
        if isinstance(u, Expr):
            stack.extend(u.args)
        elif isinstance(u, Bound):
            stack.append(u.body)
    for u in reversed(order):
        if not isinstance(u, Expr):
            if isinstance(u, Bound):
                val[u] = val[u.body]
                continue
            val[u] = _atom(u)
            continue
        name = u.head.name
        if name == "Plus":
            parts = [val[a] for a in u.args]
            s = parts[0]
            for p in parts[1:]:
                s += (" - " + p[1:]) if p.startswith("-") else (" + " + p)
            val[u] = s
            continue
        if name == "Times":
            nums = [a for a in u.args if T.is_num(a)]
            rest = [a for a in u.args if not T.is_num(a)]
            dens = []
            keep = []
            for a in rest:
                if (isinstance(a, Expr) and a.head.name == "Power"
                        and isinstance(a.args[1], Int) and a.args[1].v < 0):
                    be = -a.args[1].v
                    dens.append((a.args[0], be))
                else:
                    keep.append(a)
            coef = ""
            for n in nums:
                v = T.num_val(n)
                if v == -1:
                    coef = "-"
                elif v != 1:
                    coef = _atom(n)
            def _fac(a):
                s = val[a]
                return _parens(s) if isinstance(a, Expr) and a.head.name == "Plus" else s
            num_s = coef + " ".join(_fac(a) for a in keep)
            if not num_s:
                num_s = "1"
            if dens:
                den_s = " ".join(
                    _fac(b) if k == 1 else _fac(b) + "^{" + str(k) + "}"
                    for b, k in dens
                )
                val[u] = "\\frac{" + num_s + "}{" + den_s + "}"
            else:
                val[u] = num_s
            continue
        if name == "Power":
            b, e = u.args
            sb = val[b]
            if isinstance(b, Expr) and b.head.name in ("Plus", "Times"):
                sb = _parens(sb)
            if isinstance(e, Int) and e.v < 0:
                # 负整数幂统一分式形态（x^-2 -> 1/x^2，与 Times 分母提取一致）
                be = -e.v
                den = sb if be == 1 else sb + "^{" + str(be) + "}"
                val[u] = "\\frac{1}{" + den + "}"
            elif isinstance(e, Rat) and e.f == Fr(1, 2):
                val[u] = "\\sqrt{" + sb + "}"
            elif isinstance(e, Rat) and e.f.numerator == 1:
                val[u] = "\\sqrt[" + str(e.f.denominator) + "]{" + sb + "}"
            else:
                val[u] = sb + "^{" + val[e] + "}"
            continue
        if name == "Abs":
            val[u] = "\\left|" + val[u.args[0]] + "\\right|"
            continue
        if name in _CMP:
            val[u] = val[u.args[0]] + " " + _CMP[name] + " " + val[u.args[1]]
            continue
        if name == "And":
            val[u] = " \\land ".join(val[a] for a in u.args)
            continue
        if name == "Or":
            val[u] = " \\lor ".join(val[a] for a in u.args)
            continue
        if name == "Not":
            val[u] = "\\lnot " + val[u.args[0]]
            continue
        if name == "Quote":
            val[u] = val[u.args[0]]
            continue
        if name == "Piecewise" and len(u.args) % 2 == 0:
            rows = " \\\\ ".join(
                val[u.args[i]] + " & " + val[u.args[i + 1]]
                for i in range(0, len(u.args), 2)
            )
            val[u] = "\\begin{cases} " + rows + " \\end{cases}"
            continue
        if name == "FiniteSet":
            val[u] = "\\left\\{" + ", ".join(val[a] for a in u.args) + "\\right\\}"
            continue
        if name == "Interval" and len(u.args) == 4:
            lo, hi, lo_o, hi_o = u.args
            lb = "(" if (isinstance(lo_o, T.BVal) and lo_o.val) else "["
            rb = ")" if (isinstance(hi_o, T.BVal) and hi_o.val) else "]"
            val[u] = f"{lb}{val[lo]}, {val[hi]}{rb}"
            continue
        if name == "Union":
            val[u] = " \\cup ".join(val[a] for a in u.args)
            continue
        if name == "O" and len(u.args) == 1:
            val[u] = "O(" + val[u.args[0]] + ")"
            continue
        if name in ("Integrate", "Sum", "Product", "Limit") \
                and len(u.args) == 1 and isinstance(u.args[0], Bound):
            b = u.args[0]
            _v, ob = T.open_bound(b)   # DB 索引还原为绑定变量名再渲染
            sym = {"Integrate": "\\int ", "Sum": "\\sum ", "Product": "\\prod ",
                   "Limit": "\\lim "}[name]
            val[u] = f"{sym}{to_latex(ob)} \\, d{b.hint}"
            continue
        args = ", ".join(val[a] for a in u.args)
        val[u] = f"{_name_of(u.head)}\\left({args}\\right)"
    return val[t]
