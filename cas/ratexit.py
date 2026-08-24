"""N8 表达式层除法出口共轭有理化（M78.5）。

参照物：expr.spad root_reduce / algreduc（FriCAS）。算法契约：

  simple_root 限定 —— 只处理平方根类核（nthRoot(a,2) 且 radicand
  无嵌套核）；分母对该核的次数 ≤1 时取共轭闭式

      1/(c0 + c1*l) = (c0 - c1*l)/(c0^2 - c1^2*bv)    l = bv^(1/2)

  （root_reduce 的 n1/d1 在项级局部重写下的等价形式：除法即负幂
  因子，Power(g,-1) -> conj/d1，与上下文无关恒成立——因
  (c0+c1*l)(c0-c1*l) = c0^2 - c1^2*bv。）

本实现逐叶多遍至不动点（每遍单核——FriCAS algreduc 同为每调用
单核，多核靠重复）；系数含其它平方根叶的因子诚实跳过，留待后续
批次的多叶扩张（M78.8 辖区）。无注册表依赖：叶语义自项自身的
数值底+指数读取（mk/N1 保证指数规范形），不触碰 ALG_FIELDS——
零作用域泄漏面（QxStruct 教训）。

诚实边界：
  - 高次根（分母指数 >=3 次单位根类）不动：共轭无二项闭式，
    需结式机械（N2 后置）。
  - 分母对某根次数 >=2 不动（同上）。
  - 多叶线性分母（sqrt(2)+sqrt(3)）单遍跳过；多遍亦不动点。
"""

from fractions import Fraction as Fr

from cas.term import S, N, Expr, Rat, is_num, num_val
import cas.term as T

_MAX_PASSES = 8
_LSYM = S("_re_l")


def _sqrt_leaves(t):
    """全部平方根类叶 {Power(bv, 1/2)}（数值正底、指数恰为 1/2）。"""
    leaves = set()
    stack = [t]
    while stack:
        u = stack.pop()
        if isinstance(u, Expr):
            if u.head.name == "Power":
                b, e = u.args
                if is_num(b) and isinstance(e, Rat) \
                        and e.f.denominator == 2 and e.f.numerator == 1 \
                        and num_val(b) > 0:
                    leaves.add(u)
                    continue
            stack.extend(u.args)
    return leaves


def _split_linear(f, leaf):
    """f 是否 c0 + c1*leaf（c0,c1 均无 leaf 且无其它平方根叶）。

    返回 (c0_term, c1_term)；否则 None。以符号替换 + 多元 Poly 的
    指定位置次数判定（系数可为 x/参数的任意多项式——univariate in r
    的项级对应物）。"""
    others = [l for l in _sqrt_leaves(f) if not (l == leaf)]
    if others:
        return None                  # 系数混其它叶：本遍跳过
    sub = T.subst(f, {leaf: _LSYM})
    try:
        from cas.poly import Poly
        vs = (_LSYM,) + tuple(sorted(T.free_vars(sub) - {_LSYM}, key=str))
        gp = Poly.from_term(sub, vs)
    except Exception:
        return None
    c0m, c1m = {}, {}
    for key, c in gp.monos.items():
        if c == 0:
            continue
        tgt = c0m if key[0] == 0 else c1m if key[0] == 1 else None
        if tgt is None:
            return None              # 对 l 次数 >=2：边界外
        rest = key[1:]
        tgt[rest] = tgt.get(rest, Fr(0)) + c
    p = Poly(vs[1:], c0m)
    q = Poly(vs[1:], c1m)
    return p.to_term(), q.to_term()


def _rationalize_once(t):
    """单遍：自底向上把 Power(c0+c1*l, -1) 重写为 (c0-c1*l)/d1。

    返回 (新 t, 是否有改动)。"""
    val = {}
    changed = False
    order = []
    stack = [t]
    while stack:
        u = stack.pop()
        order.append(u)
        if isinstance(u, Expr):
            stack.extend(u.args)
    for u in reversed(order):
        if not isinstance(u, Expr):
            val[u] = u
            continue
        args = tuple(val[a] for a in u.args)
        hit = None
        if u.head.name == "Power" and len(args) == 2 \
                and isinstance(args[1], T.Int) and args[1].v == -1 \
                and isinstance(args[0], Expr):
            f = args[0]
            for l in sorted(_sqrt_leaves(f), key=repr):
                sp = _split_linear(f, l)
                if sp is None:
                    continue
                c0, c1 = sp
                bv = num_val(l.args[0])
                conj = T.plus(c0, T.neg(T.times(c1, l)))
                d1 = T.plus(T.pw(c0, N(2)),
                            T.neg(T.times(T.pw(c1, N(2)), N(bv))))
                hit = T.times(conj, T.pw(d1, N(-1)))
                break
        if hit is not None:
            val[u] = hit
            changed = True
        else:
            val[u] = T.mk(u.head, args)
    return val[t], changed


def rationalize(t, max_passes=_MAX_PASSES):
    """出口共轭有理化：多遍至不动点（上限守卫）。纯函数、无副作用。"""
    cur = t
    for _ in range(max_passes):
        nxt, ch = _rationalize_once(cur)
        if not ch or nxt is cur:
            break
        cur = nxt
    return cur
