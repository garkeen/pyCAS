r"""LaTeX 输出（纯展示层，maxima tex 同款定位）。

显式栈后序重建（与 pprint.to_str 同构）：每节点产出 LaTeX 身串，
父层按结构需要包裹 \left( \right)。不追求完备括号决策，
覆盖教科书常用形态：分式/根式/幂/三角/积分/分段/比较/逻辑。
"""

from fractions import Fraction as Fr
import re

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


def _tag(path, s):
    r"""\htmlClass{tn-<path>}{...}（KaTeX trust:true 渲染）。根节点 path 为空 -> tn-。"""
    p = "-".join(str(i) for i in path)
    return f"\\htmlClass{{tn-{p}}}{{{s}}}"


_NEG_RE = re.compile(r"^(\\htmlClass\{[^}]*\})\{(.*)\}$", re.S)


def _strip_neg(w):
    r"""去掉 \htmlClass{..}{-content} 里 content 的前导 '-'（负号放 class 外）。"""
    m = _NEG_RE.match(w)
    if m and m.group(2).startswith("-"):
        return m.group(1) + "{" + m.group(2)[1:] + "}"
    return w[1:] if w.startswith("-") else w


def annotate_latex(u, path=()):
    r"""to_latex 的可点击版本：每节点片段外包 \htmlClass{tn-<path>}。

    返回 (raw, wrapped)：raw 为完全裸串（与 to_latex(u) 逐字节一致，父分支的
    检测依赖它，如 Plus 的 '-' 前缀判断），wrapped = 每个子节点片段带 class 的
    串（class 嵌入父串内部，前端按 class 定位点击选区）。括号规则与 to_latex 同构。
    """
    memo = {}

    def rec(u, path):
        if (id(u), path) in memo:
            return memo[(id(u), path)]
        if isinstance(u, Bound):
            raw_b, w_b = rec(u.body, path + (0,))
            res = (raw_b, _tag(path, w_b))
            memo[(id(u), path)] = res
            return res
        if not isinstance(u, Expr):
            raw = _atom(u)
            res = (raw, _tag(path, raw))
            memo[(id(u), path)] = res
            return res

        name = u.head.name
        subs = [rec(a, path + (i,)) for i, a in enumerate(u.args)]
        r = [s[0] for s in subs]   # 裸串
        w = [s[1] for s in subs]   # 带 class

        if name == "Plus":
            s, cs = r[0], w[0]
            for i in range(1, len(w)):
                if r[i].startswith("-"):
                    s += " - " + r[i][1:]
                    cs += " - " + _strip_neg(w[i])
                else:
                    s += " + " + r[i]
                    cs += " + " + w[i]
        elif name == "Times":
            nums = [a for a in u.args if T.is_num(a)]
            dens = []
            keep = []
            for i, a in enumerate(u.args):
                if T.is_num(a):
                    continue
                if (isinstance(a, Expr) and a.head.name == "Power"
                        and isinstance(a.args[1], Int) and a.args[1].v < 0):
                    dens.append((i, -a.args[1].v))
                else:
                    keep.append(i)
            coef = ""
            for n in nums:
                v = T.num_val(n)
                if v == -1:
                    coef = "-"
                elif v != 1:
                    coef = _atom(n)

            def _fac_s(i):
                a = u.args[i]
                return _parens(r[i]) if isinstance(a, Expr) and a.head.name == "Plus" else r[i]

            def _fac_w(i):
                a = u.args[i]
                return _parens(w[i]) if isinstance(a, Expr) and a.head.name == "Plus" else w[i]

            num_s = coef + " ".join(_fac_s(i) for i in keep)
            num_c = coef + " ".join(_fac_w(i) for i in keep)
            if not num_s:
                num_s = "1"
                num_c = "1"
            if dens:
                den_s_parts = []
                den_c_parts = []
                for i, k in dens:
                    b = u.args[i].args[0]
                    rb, wb = memo[(id(b), path + (i, 0))]
                    if isinstance(b, Expr) and b.head.name == "Plus":
                        rb, wb = _parens(rb), _parens(wb)
                    den_s_parts.append(rb if k == 1 else rb + "^{" + str(k) + "}")
                    den_c_parts.append(wb if k == 1 else wb + "^{" + str(k) + "}")
                s, cs = "\\frac{" + num_s + "}{" + " ".join(den_s_parts) + "}", \
                        "\\frac{" + num_c + "}{" + " ".join(den_c_parts) + "}"
            else:
                s, cs = num_s, num_c
        elif name == "Exp" and len(u.args) == 1:
            s, cs = "e^{" + r[0] + "}", "e^{" + w[0] + "}"
        elif name == "Power":
            b, e = u.args
            if isinstance(b, Expr) and b.head.name in ("Plus", "Times"):
                sb_s, sb_c = _parens(r[0]), _parens(w[0])
            else:
                sb_s, sb_c = r[0], w[0]
            if isinstance(e, Int) and e.v < 0:
                be = -e.v
                den_s = sb_s if be == 1 else sb_s + "^{" + str(be) + "}"
                den_c = sb_c if be == 1 else sb_c + "^{" + str(be) + "}"
                s, cs = "\\frac{1}{" + den_s + "}", "\\frac{1}{" + den_c + "}"
            elif isinstance(e, Rat) and e.f == Fr(1, 2):
                s, cs = "\\sqrt{" + r[0] + "}", "\\sqrt{" + w[0] + "}"
            elif isinstance(e, Rat) and e.f.numerator == 1:
                s, cs = "\\sqrt[" + str(e.f.denominator) + "]{" + r[0] + "}", \
                        "\\sqrt[" + str(e.f.denominator) + "]{" + w[0] + "}"
            else:
                s, cs = sb_s + "^{" + r[1] + "}", sb_c + "^{" + w[1] + "}"
        elif name == "Abs":
            s, cs = "\\left|" + r[0] + "\\right|", "\\left|" + w[0] + "\\right|"
        elif name in _CMP:
            s, cs = r[0] + " " + _CMP[name] + " " + r[1], \
                    w[0] + " " + _CMP[name] + " " + w[1]
        elif name == "And":
            s, cs = " \\land ".join(r), " \\land ".join(w)
        elif name == "Or":
            s, cs = " \\lor ".join(r), " \\lor ".join(w)
        elif name == "Not":
            s, cs = "\\lnot " + r[0], "\\lnot " + w[0]
        elif name == "Quote":
            s, cs = r[0], w[0]
        elif name == "Piecewise" and len(u.args) % 2 == 0:
            s = "\\begin{cases} " + " \\\\ ".join(
                r[i] + " & " + r[i + 1] for i in range(0, len(r), 2)) + " \\end{cases}"
            cs = "\\begin{cases} " + " \\\\ ".join(
                w[i] + " & " + w[i + 1] for i in range(0, len(w), 2)) + " \\end{cases}"
        elif name == "FiniteSet":
            s, cs = "\\left\\{" + ", ".join(r) + "\\right\\}", \
                    "\\left\\{" + ", ".join(w) + "\\right\\}"
        elif name == "Interval" and len(u.args) == 4:
            lo, hi, lo_o, hi_o = u.args
            lb = "(" if (isinstance(lo_o, T.BVal) and lo_o.val) else "["
            rb = ")" if (isinstance(hi_o, T.BVal) and hi_o.val) else "]"
            s, cs = f"{lb}{r[0]}, {r[1]}{rb}", f"{lb}{w[0]}, {w[1]}{rb}"
        elif name == "Union":
            s, cs = " \\cup ".join(r), " \\cup ".join(w)
        elif name == "O" and len(u.args) == 1:
            s, cs = "O(" + r[0] + ")", "O(" + w[0] + ")"
        elif name in ("Integrate", "Sum", "Product", "Limit") \
                and len(u.args) == 1 and isinstance(u.args[0], Bound):
            b = u.args[0]
            _v, ob = T.open_bound(b)   # DB 索引还原为绑定变量名再渲染
            sym = {"Integrate": "\\int ", "Sum": "\\sum ", "Product": "\\prod ",
                   "Limit": "\\lim "}[name]
            body_plain = to_latex(ob)
            s = f"{sym}{body_plain} \\, d{b.hint}"
            cs = f"{sym}{_tag(path + (0,), body_plain)} \\, d{b.hint}"
        else:
            s = f"{_name_of(u.head)}\\left({', '.join(r)}\\right)"
            cs = f"{_name_of(u.head)}\\left({', '.join(w)}\\right)"
        res = (s, _tag(path, cs))
        memo[(id(u), path)] = res
        return res

    return rec(u, path)


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
        if name == "Exp" and len(u.args) == 1:
            # 教科书惯例：exp(x) -> e^{x}（E^x 与 exp(x) 同一规范形）
            val[u] = "e^{" + val[u.args[0]] + "}"
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
