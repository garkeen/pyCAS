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
  - 分母对某根次数 >=q 不动（需结式机械，已由 af_func 域求逆覆盖任意 q）。
  - 多叶线性分母（sqrt(2)+sqrt(3)）单遍跳过；多遍亦不动点（M78.8）。
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


def _higher_leaves(t):
    """一般 q 次根叶（q>=2、分子 1、正数值底，理论无上界）。"""
    out = set()
    stack = [t]
    while stack:
        u = stack.pop()
        if isinstance(u, Expr):
            if u.head.name == "Power":
                b, e = u.args
                if is_num(b) and isinstance(e, Rat) \
                        and e.f.numerator == 1 \
                        and e.f.denominator >= 2 \
                        and num_val(b) > 0:
                    out.add(u)
                    continue
            stack.extend(u.args)
    return out


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
            if hit is None:
                # N8 余项：一般 q 次根（q>=2）经域求逆有理化
                gen = sorted(_higher_leaves(f), key=repr)
                for l in gen:
                    inv = _rationalize_higher(f, l)
                    if inv is not None:
                        hit = inv
                        break
        if hit is not None:
            val[u] = hit
            changed = True
        else:
            val[u] = T.mk(u.head, args)
    return val[t], changed


def _rationalize_higher(f, leaf):
    """N8 余项：一般 q 次根叶的分母逆——映入 ℚ(x)(ℓ) 域元素求逆。

    d(x,ℓ)=Σ c_i(x)·ℓ^i（c_i 无其它根式叶）在 K=ℚ(ℓ)(x) 中可逆
    （m 不可约时）；inv 的 to_term 即有理化形（分母归 ℚ(x)）。
    m 可约/不可逆/混叶 ⟹ None（诚实跳过）。"""
    from cas.term import Expr as _E
    b, e = leaf.args
    if not is_num(b):
        return None
    bv = num_val(b)
    if bv <= 0 or e.f.numerator != 1:
        return None
    q = e.f.denominator
    if q < 2:
        return None
    # 系数提取：对 ℓ 位置次数 <=q-1；系数为 xv 多项式（Fr/SymRat 叶）
    sub = T.subst(f, {leaf: S("_rl")})
    try:
        from cas.poly import Poly, SymRat
        from cas.ratfunc import RatFunc as _RF
        from cas.algfield import af_func
        vs = (S("_rl"),) + tuple(sorted(T.free_vars(sub) - {S("_rl")},
                                        key=str))
        gp = Poly.from_term(sub, vs)
        buckets = {}
        for key, cf in gp.monos.items():
            ea = key[0]
            if ea >= q:
                return None
            rest = key[1:]
            tgt = buckets.setdefault(ea, {})
            tgt[rest] = tgt.get(rest, Fr(0)) + cf
        cs_rf = []
        for i in range(q):
            mm = buckets.get(i, {})
            cs_rf.append(_RF(Poly(vs[1:], mm), Poly.one(vs[1:]))
                         if mm else _RF.zero(vs[1:]))
        # 域：ℚ(x)(ℓ)，m=T^q−bv 首一 RatFunc 系数（升序恰 q+1 项）
        mrf = []
        for j in range(q):
            cj = Fr(-(bv ** e.f.numerator)) if j == 0 else Fr(0)
            mrf.append(_RF.from_const(vs[1:], cj))
        mrf.append(_RF.one(vs[1:]))
        fld = af_func(mrf, vs[1:], origin=leaf)
        d_el = fld.elem(cs_rf)
        inv = d_el.inv()
        parts = []
        for j, c in enumerate(inv.cs):
            ct = c.to_term()
            if j == 0:
                parts.append(ct)
            else:
                parts.append(T.times(ct, T.pw(leaf, N(j))))
        if not parts:
            return None
        return parts[0] if len(parts) == 1 \
            else T.mk(S("Plus"), tuple(parts))
    except Exception:
        return None


def rationalize(t, max_passes=_MAX_PASSES):

    """出口共轭有理化：多遍至不动点（上限守卫）。纯函数、无副作用。"""
    cur = t
    for _ in range(max_passes):
        nxt, ch = _rationalize_once(cur)
        if not ch or nxt is cur:
            break
        cur = nxt
    return cur
