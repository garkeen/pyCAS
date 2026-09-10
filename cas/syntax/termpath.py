# -*- coding: utf-8 -*-
"""树遍历与重写工具（自 cas/term.py 拆出）：替换（subst）、模式实例化
（instantiate）、路径寻址（term_at/replace_at/all_paths）、自由变量、
子项手术绑定（_bind_into）、规模统计。

依赖纪律：本模块对 term 只持模块引用（函数内经 T.xxx 访问）——
term.py 末尾延迟导入本模块完成名字回接，无导入环。
"""

from cas.syntax import term as T
from cas.errors import BudgetExceeded


def _subst_raw(t, mapping):
    """原始结构替换（不规范化，保 held 形）：用于 Quote 内部。

    与 subst 同构但重建走 _intern_expr——Times/Power 不合并同底幂，
    保持 held 项的原始结构。Quote 内部含 ?x 替换时用此。
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
            val[u] = T._intern_expr(u.head, tuple(val[a] for a in u.args))
        elif isinstance(u, T.Bound):
            val[u] = T._mk_bound_canon(u.hint, val[u.body])
        else:
            val[u] = u
    return val[t]


def subst(t, mapping):
    """替换（显式工作栈后序重建，深表达式不触及 Python 递归上限）。

    Quote 内部走 _subst_raw（保 held 结构，不合并同底幂/同类项）。
    """
    if not mapping:
        return t
    # 显式栈后序遍历；Bound 的 body 必须始终下行（内部自由变量需替换且防捕获）
    order = []
    stack = [t]
    while stack:
        u = stack.pop()
        order.append(u)
        if isinstance(u, T.Expr):
            if u in mapping:
                continue  # 命中替换表的子树不再下行
            if isinstance(u.head, T.Sym) and u.head.name == "Quote":
                continue  # quote 内部不走 mk 重建（保 held 结构，单独 raw subst）
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
                # quote 内部保 held 结构：raw subst（_intern_expr 重建，不规范化）
                val[u] = T._intern_expr(u.head, tuple(T._subst_raw(a, mapping) for a in u.args))
            else:
                val[u] = T.mk(u.head, tuple(val[a] for a in u.args))
        elif isinstance(u, T.Bound):
            val[u] = T._mk_bound_canon(u.hint, val[u.body])
        else:
            val[u] = u
    return val[t]


def _instantiate_raw(t, sub):
    """原始结构实例化（不规范化，保 held 形）：用于 Quote 内部。

    与 instantiate 同构但重建走 _intern_expr——Times/Power 不合并，
    保持 held 项的原始结构。规则 RHS 的 Quote 内含 ?x 实例化时用此。
    """
    if isinstance(t, T.PatVar):
        return sub.get(t.name, t)
    if isinstance(t, T.PatSeq):
        raise BudgetExceeded(message=f"sequence hole ?{t.name} not in arg position")
    if isinstance(t, T.Expr):
        out = []
        for a in t.args:
            if isinstance(a, T.PatSeq):
                seq = sub.get(a.name)
                if seq is None:
                    out.append(a)
                else:
                    out.extend(seq)
            else:
                out.append(_instantiate_raw(a, sub))
        return T._intern_expr(t.head, tuple(out))
    if isinstance(t, T.Bound):
        return T._mk_bound_canon(t.hint, _instantiate_raw(t.body, sub))
    return t


def instantiate(t, sub):
    if isinstance(t, T.PatVar):
        return sub.get(t.name, t)
    if isinstance(t, T.PatSeq):
        raise BudgetExceeded(message=f"sequence hole ?{t.name} not in arg position")
    if isinstance(t, T.Expr):
        if isinstance(t.head, T.Sym) and t.head.name == "Quote":
            # quote 内部保 held 结构：raw instantiate（_intern_expr 重建，不规范化）
            return T._intern_expr(t.head, tuple(_instantiate_raw(a, sub) for a in t.args))
        out = []
        for a in t.args:
            if isinstance(a, T.PatSeq):
                seq = sub.get(a.name)
                if seq is None:
                    out.append(a)
                else:
                    out.extend(seq)
            else:
                out.append(instantiate(a, sub))
        return T.mk(t.head, tuple(out))
    if isinstance(t, T.Bound):
        return T._mk_bound_canon(t.hint, instantiate(t.body, sub))
    return t


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
            # 穿过绑定层时打开体：DB 索引还原为绑定符号，子树脱离绑定上下文
            # 供规则匹配/求值视为自由符号树（replace_at 放回时 mk_bound 重新抽象）
            t = T._lift(t.body, T.S(t.hint), 0)
        else:
            raise IndexError(path)
    return t


def _bind_into(t, var, depth=0):
    """把打开后的体中的自由变量 var 绑回 de Bruijn 索引，不触碰已有 DB 引用。

    与 _abstract 的区别：_abstract 会提升 body 里已有的 DB(i>=depth)（正常 mk_bound
    场景 body 无 DB 引用）；replace_at 穿过已绑定层时 body 里已有外层 DB 引用，必须保持。
    """
    if isinstance(t, T.Sym):
        return T.DB_(depth) if t is var else t
    if isinstance(t, T.Expr):
        return T.mk(t.head, tuple(_bind_into(a, var, depth) for a in t.args))
    if isinstance(t, T.Bound):
        return T._mk_bound_canon(t.hint, _bind_into(t.body, var, depth + 1))
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
        # 打开当前层 -> 递归替换 -> 只把当前层变量绑回，外层 DB 引用保持不动
        var = T.S(t.hint)
        inner = replace_at(T._lift(t.body, var, 0), path[1:], v)
        return T._mk_bound_canon(t.hint, _bind_into(inner, var, 0))
    raise IndexError(path)


def all_paths(t, base=()):
    yield base
    if isinstance(t, T.Expr):
        for i, a in enumerate(t.args):
            yield from all_paths(a, base + (i,))
    elif isinstance(t, T.Bound):
        yield from all_paths(t.body, base + (0,))


def postorder(t):
    """显式栈后序遍历（不依赖 Python 递归栈，深表达式安全）。

    全系统只此一份：此前 pprint 与 simplify 各存一份同构副本（pprint
    那份的注释还写着"避免跨模块依赖"），树遍历工具归本模块。
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
