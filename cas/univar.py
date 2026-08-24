"""单变量域多项式 K[t]（M6.4 提取）：系数为域元素的稠密算术。

# 表示与契约

- K[t] 多项式 = 系数 list [c_0..c_n]（**升序**）。
- K 是域（当前实例：基变量上的 RatFunc；任何支持
  ``+ - * /``、``is_zero()``、``one(vars)`` 的对象皆可）。
- 零元协议：算术函数收显式 ``zero`` 实参作原型——``zero.one(p.vars)``
  给单位元，变量集由参与运算的元素自携带。
- gcd 恒 monic 规范化（K 是域，首系数可逆）；空 list = 零多项式。
- 与 Poly 的换算边界：Poly -> K[t] 见 :func:`from_poly`；反向
  K[t] -> 塔上 Poly 对因耦合塔嵌入（_embed/_cancel）留在 risch
  （_from_univar）。本模块仅依赖地基 {poly, term}，不依赖 risch
  （u_inv_mod 的异常懒导入除外）。
- 已知接缝：u_inv_mod 前置违反（gcd(a,m)≠1）抛 RischUnsupported
  （懒导入防环）——语义上是"诚实拒答载体"，改抛 PolyError 会
  变更上层捕获路径，留待 M6.3 异常审计统一裁定。
"""

from fractions import Fraction as Fr

from cas.poly import Poly
from cas.term import S


def from_poly(p, ti):
    """Poly(all_vars) -> K[t_i] 系数 list（升序，K 元素 = RatFunc）。"""
    from cas.ratfunc import RatFunc

    sub = tuple(v for v in p.vars if v is not ti)
    j = p.vars.index(ti)
    out = [RatFunc.zero(sub)]
    for k, c in p.monos.items():
        e = k[j]
        while len(out) <= e:
            out.append(RatFunc.zero(sub))
        nk = tuple(x for i, x in enumerate(k) if i != j)
        out[e] = out[e] + RatFunc.from_poly(Poly(sub, {nk: c}))
    return out


def u_add(a, b, zero):
    n = max(len(a), len(b))
    out = []
    for i in range(n):
        ca = a[i] if i < len(a) else zero
        cb = b[i] if i < len(b) else zero
        out.append(ca + cb)
    return u_trim(out)


def u_trim(cs):
    while cs and cs[-1].is_zero():
        cs.pop()
    return cs


def u_neg(a, neg):
    return [neg(c) for c in a]


def u_mul(a, b, zero):
    if not a or not b:
        return []
    out = [zero for _ in range(len(a) + len(b) - 1)]
    for i, ca in enumerate(a):
        if ca.is_zero():
            continue
        for j, cb in enumerate(b):
            if cb.is_zero():
                continue
            out[i + j] = out[i + j] + ca * cb
    return u_trim(out)


def u_divmod(a, b, zero):
    """K[t] 除法（b 非零，K = RatFunc 域）。返回 (q, r) 系数 list。"""
    r = [c for c in a]
    db = len(b) - 1
    lb = b[db]
    if len(r) - 1 < db:
        return [], u_trim(r)
    q = [zero for _ in range(len(r) - db)]
    while len(r) - 1 >= db and not u_is_zero(r):
        shift = len(r) - 1 - db
        lc = r[-1]
        c = lc / lb
        q[shift] = c
        for i in range(db + 1):
            r[shift + i] = r[shift + i] - c * b[i]
        u_trim(r)
    return u_trim(q), u_trim(r)


def u_is_zero(cs):
    return not cs or all(c.is_zero() for c in cs)


def u_gcd(a, b, zero):
    """K[t] gcd（欧几里得 + monic）。K 是域——首系数总可逆。"""
    A, B = u_trim([c for c in a]), u_trim([c for c in b])
    while not u_is_zero(B):
        _, r = u_divmod(A, B, zero)
        A, B = B, r
    if u_is_zero(A):
        return []
    s = zero.one(zero.p.vars) / A[-1]
    return [c * s for c in A]


def u_inv_mod(a, m, zero):
    """a 的逆 mod m（gcd(a,m)=1）。扩展欧几里得：s*a + t*m = g -> s/g。

    初始化 s0=0（对应 r0=m）、s1=1（对应 r1=a）；结束时 s0*a ≡ g (mod m)。
    """
    r0, r1 = [c for c in m], u_trim([c for c in a])
    s0, s1 = [zero], [zero.one(zero.p.vars)]
    while not u_is_zero(r1):
        q, r = u_divmod(r0, r1, zero)
        qs = u_mul(q, s1, zero)
        s_new = u_add(s0, u_neg(qs, lambda c: c * Fr(-1)), zero)
        s0, s1 = s1, s_new
        r0, r1 = r1, r
    # r0 = gcd；互素时为 K 中单位（非零元素），s0*a ≡ gcd (mod m)
    if u_is_zero(r0):
        from cas.risch import RischUnsupported
        raise RischUnsupported("zero gcd in inverse")
    s = r0[0].one(r0[0].p.vars) / r0[0]
    out = [c * s for c in s0]
    _, rem = u_divmod(out, m, zero)
    return rem


def u_deriv_x(coeffs):
    """K 层求导：逐系数 d/dx。"""
    xv = coeffs[0].p.vars[0] if coeffs and coeffs[0].p.vars else S("x")
    return [c.deriv(xv) for c in coeffs]


def u_pow(cs, n, zero):
    out = [zero.one(zero.p.vars)]
    base = list(cs)
    while n > 0:
        if n & 1:
            out = u_mul(out, base, zero)
        base = u_mul(base, base, zero)
        n >>= 1
    return out


def u_inv_mod_t(a, m, zero):
    """K[t] 上 a^{-1} mod m。"""
    return u_inv_mod(a, m, zero)


def u_sub(a, b):
    """K 多项式减法（zero 自参数推断）。"""
    from cas.ratfunc import RatFunc

    src = a if a else b
    z = RatFunc.zero(src[0].p.vars) if src else RatFunc.zero((S("x"),))
    return u_add(a, u_neg(b, lambda c: c * Fr(-1)), z)


def u_mul0(a, b):
    """K 多项式乘法（zero 自参数推断）。"""
    from cas.ratfunc import RatFunc

    if not a or not b:
        return []
    z = RatFunc.zero(a[0].p.vars)
    return u_mul(a, b, z)


def u_formal_deriv(cs):
    """形式偏导 ∂/∂t（系数不动）。"""
    return u_trim([c * Fr(k) for k, c in enumerate(cs)][1:])


def u_deg(cs):
    return len(u_trim(list(cs))) - 1


def u_xgcd(a, b, zero):
    """扩展欧几里得：返回 (s, t, g) 使 s·a + t·b = g。"""
    one_c = zero.one(zero.p.vars)
    r0, r1 = u_trim([c for c in b]), u_trim([c for c in a])
    s0, s1 = [], [one_c]
    t0, t1 = [one_c], []
    while not u_is_zero(r1):
        q, r = u_divmod(r0, r1, zero)
        s_new = u_sub(s0, u_mul(q, s1, zero))
        t_new = u_sub(t0, u_mul(q, t1, zero))
        r0, r1 = r1, r
        s0, s1 = s1, s_new
        t0, t1 = t1, t_new
    if u_is_zero(r0):
        return s0, t0, []
    inv = one_c / r0[0]
    return [c * inv for c in s0], [c * inv for c in t0], \
        [c * inv for c in r0]


def u_diophantine(b, a, c, zero):
    """解 r·b + z·a = c（sympy gcdex_diophantine(b, a, c) 语义）。"""
    s, t, g = u_xgcd(b, a, zero)
    if u_is_zero(g):
        return None
    qq, rr = u_divmod(c, g, zero)
    if not u_is_zero(rr):
        return None
    return u_mul(s, qq, zero), u_mul(t, qq, zero)


def u_gauss_solve_k(M, b):
    """K 域（RatFunc）线性方程组高斯消元。返回解 list | None（无解）。"""
    n = len(M)
    cols = len(M[0]) if n else 0
    if n == 0 or cols == 0:
        return [] if not any(not x.is_zero() for x in b) else None
    one = b[0].one(b[0].p.vars)
    A = [list(M[r]) + [b[r]] for r in range(n)]
    piv_cols = []
    r = 0
    for cidx in range(cols):
        piv = None
        for i in range(r, n):
            if not A[i][cidx].is_zero():
                piv = i
                break
        if piv is None:
            continue
        A[r], A[piv] = A[piv], A[r]
        pv = A[r][cidx]
        inv = one / pv
        A[r] = [x * inv for x in A[r]]
        for i in range(n):
            if i != r and not A[i][cidx].is_zero():
                fac = A[i][cidx]
                A[i] = [vi - fac * vr for vi, vr in zip(A[i], A[r])]
        piv_cols.append(cidx)
        r += 1
        if r == n:
            break
    for i in range(n):
        if all(x.is_zero() for x in A[i][:cols]) and not A[i][cols].is_zero():
            return None
    sol = [one.zero(one.p.vars) for _ in range(cols)]
    for i, cidx in enumerate(piv_cols):
        sol[cidx] = A[i][cols]
    return sol
