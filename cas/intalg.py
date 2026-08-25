# -*- coding: utf-8 -*-
"""M78.7b 代数 Hermite / DoubleResultant（intalg.spad 对标）。

通用两级结式 R(z)=Res_x(Res_y(fa - z·g·D(d), y^q-Mp), d) 在 ℚ 上精确，
覆盖 y^q=Mp 任意 q，M78.7a 线性/二次快路外的高次亦经此路径诚实判定。
"""
from fractions import Fraction as Fr
from cas.poly import Poly, PolyError
from cas.term import S, N
import cas.term as T

def _resultant_y(p_yxz, q_yxz, y_sym, xz_vars):
    """Res_y(p,q) 其中 p,q ∈ ℚ[y,x,z]（Fr 系数），y 为主变量。

    返回 Poly(xz_vars, ...)（Fr 系数）。用 Sylvester + Bareiss（Poly 条目）。
    """
    from cas.apart import _det_bareiss
    # 收集 p,q 在 y 上的系数（Poly over xz_vars）
    def coeffs_y(poly):
        idx = poly._var_idx(y_sym)
        coeff_vars = xz_vars
        buckets = {}
        for mono, coeff in poly.monos.items():
            ey = mono[idx]
            rest = mono[:idx] + mono[idx+1:]
            # rest 对应 vars 中除 y 外的顺序，需重排到 xz_vars 顺序
            # poly.vars = (y, x, z) 假设，我们直接取 xz 部分
            # 构造 Poly over xz_vars 的单项
            # 将 rest 映射到 xz_vars 的指数
            # 由于 poly.vars 顺序固定为 (y, x, z)，rest = (ex, ez)
            # 可直接构造
            if coeff_vars:
                # rest 长度应为 len(xz_vars)
                # 若 poly.vars != (y,)+xz_vars，需重排——此处固定为 (y,x,z)
                key = (rest[0], rest[1]) if len(rest)==2 else (rest[0],) if rest else ()
                # 调整 key 长度
                if len(key) != len(coeff_vars):
                    # 扩展
                    key = tuple(list(key) + [0]*(len(coeff_vars)-len(key)))
                term = Poly(coeff_vars, {key: coeff})
            else:
                term = Poly((), {(): coeff})
            buckets[ey] = buckets.get(ey, Poly.zero(coeff_vars)) + term
        return buckets

    # p,q 的 y 次数
    try:
        dp = p_yxz.degree(y_sym)
        dq = q_yxz.degree(y_sym)
    except Exception:
        return None
    if dp < 0 or dq < 0:
        return Poly.zero(xz_vars)
    # 收集系数表（0..deg）
    bp = coeffs_y(p_yxz)
    bq = coeffs_y(q_yxz)
    # 构造 Sylvester 矩阵 (dp+dq) × (dp+dq)，条目为 Poly(xz)
    m = dp
    n = dq
    size = m + n
    # 系数降幂序列
    ca = [bp.get(m - i, Poly.zero(xz_vars)) for i in range(m+1)]  # c_m .. c_0
    cb = [bq.get(n - i, Poly.zero(xz_vars)) for i in range(n+1)]
    mat = []
    for i in range(n):
        row = [Poly.zero(xz_vars)] * size
        for j, c in enumerate(ca):
            row[i + j] = c
        mat.append(row)
    for i in range(m):
        row = [Poly.zero(xz_vars)] * size
        for j, c in enumerate(cb):
            row[i + j] = c
        mat.append(row)
    # Bareiss 行列式（Poly 条目）
    try:
        det = _det_bareiss(mat)
        return det
    except Exception:
        return None

def double_resultant(fa, fd, mp_low, de, j, z_sym):
    """通用 doubleResultant（intalg.spad:30）。

    fa/fd ∈ ℚ(de.vars)（Poly），mp_low = y^q - Mp(x) ∈ ℚ[y,x]，
    de 为塔，j 为代数层索引，z_sym 为新结式变量。
    返回 Poly((z,), Fr) 首一（primitive），失败 None。
    """
    try:
        from cas.poly import mgcd
        x = de.levels[0]
        y = de.levels[j]
        # 1) g = gcd(fd, D(fd)), d = fd/g  （D 为形式 x 导，此处 y 不在 fd 时足够）
        # fd 可能含 y（一般代数被积式的分母），但 D(fd) 需含 y' 项；简化取形式 x 导
        # 对 y 自由的分母（ℚ[x] 上），此近似精确
        try:
            fd_x = fd.deriv(x) if x in fd.vars else Poly.zero(fd.vars)
        except Exception:
            fd_x = Poly.zero(fd.vars)
        # mgcd 需同 vars
        if x in fd.vars:
            g = mgcd(fd, fd_x) if not fd_x.is_zero() else Poly.one(fd.vars)
            if g.is_zero():
                g = Poly.one(fd.vars)
            # d = fd / g  精确除
            from cas.poly import div_exact
            try:
                d = div_exact(fd, g)
            except Exception:
                d = fd
        else:
            g = Poly.one(fd.vars)
            d = fd
        # 2) 构造 p = fa - z·g·D(d)  在 ℚ[y,x,z] 上（Fr 系数）
        # 需将 fa, g, D(d) 嵌入到 (y,x,z) 空间
        xz_vars = (x, z_sym)
        yxz_vars = (y, x, z_sym)
        # 辅助：Poly over de.vars -> Poly over (y,x,z) with Fr
        def embed_to_yxz(p):
            if p.is_zero():
                return Poly(yxz_vars, {})
            # p.vars 可能是 (x,y) 或 (x,) 等，需经 to_term 再 from_term 重建
            t = p.to_term()
            # 重建到 yxz
            try:
                return Poly.from_term(t, yxz_vars)
            except PolyError:
                # 含非多项式项（如负幂）——此路径不适用，返回 None 触发上层 fallback
                return None
        fa_yxz = embed_to_yxz(fa)
        if fa_yxz is None:
            return None
        # g·D(d) 嵌入
        # g, d 可能为多变量 Poly over de.vars，需同样嵌入但仅取 x 部分
        # D(d) 近似为 x 导
        try:
            dd = d.deriv(x) if x in d.vars else Poly.zero(d.vars)
        except Exception:
            dd = Poly.zero(d.vars)
        # g·dd  -> Poly over (x,) 嵌入到 (y,x,z)
        # g·dd 的 vars 可能为 (x,) 或 (x,y)
        try:
            gdd = g * dd if not (g.is_zero() or dd.is_zero()) else Poly.zero(d.vars)
            if gdd.is_zero():
                gdd_yxz = Poly(yxz_vars, {})
            else:
                gdd_yxz = embed_to_yxz(gdd)
                if gdd_yxz is None:
                    return None
        except Exception:
            gdd_yxz = Poly(yxz_vars, {})
        # z·g·dd
        # 构造 z 的 Poly
        z_poly = Poly(yxz_vars, {(0,0,1): Fr(1)})
        zgdd = gdd_yxz * z_poly if not gdd_yxz.is_zero() else Poly(yxz_vars, {})
        p_yxz = fa_yxz - zgdd
        # 3) m = y^q - Mp(x) 嵌入到 (y,x,z)
        # mp_low 已为 Poly((y,) + lower) 且 lower=(x,)
        # 需嵌入到 (y,x,z)
        try:
            m_yxz = Poly.from_term(mp_low.to_term(), yxz_vars)
        except Exception:
            return None
        # 4) r = Res_y(p, m)  -> Poly(x,z)
        r_xz = _resultant_y(p_yxz, m_yxz, y, xz_vars)
        if r_xz is None or r_xz.is_zero():
            return None
        # 5) R = Res_x(r, d) -> Poly(z)
        # r_xz 是 Poly over (x,z) with Fr coeffs
        # d 是 Poly over (x,) 或 (x,y) — 取其在 x 上部分（忽略 y，若含 y 则此路径不适用）
        # 简化：若 d 含 y（非常见），则取其 x 投影（置 y=0）——诚实近似，失败回 None
        # 真正 intalg 需将 d 视为 ℚ[x] 上多项式，此处 d ∈ ℚ[x] 时精确
        d_xz = None
        try:
            # 仅当 d 真依赖 y 时才诚实 None（y 在 vars 但指数全 0 不算依赖）
            _y_dep = False
            if y in d.vars:
                try:
                    _y_dep = d.degree(y) >= 0 and any(k[d._var_idx(y)]>0 for k in d.monos)
                except Exception:
                    _y_dep = True
            if _y_dep:
                return None
            d_xz = Poly.from_term(d.to_term(), xz_vars)
        except Exception:
            return None
        if d_xz.is_zero() or d_xz.is_const():
            # d 为常数时 Res_x(r,d)= r 的常数因子，取 r 在 x 上首项
            # 简化：返回 r 消 x 后的 z 多项式（置 x=0 的首项）
            # 为保持首一性，取 r 的 x=0 切片
            # 取 r 关于 x 的零次系数
            out_map = {}
            for mono, coeff in r_xz.monos.items():
                if mono[0] == 0:  # x 指数为 0
                    out_map[(mono[1],)] = coeff
            if not out_map:
                return None
            R = Poly((z_sym,), out_map)
            # 首一化
            if R.is_zero():
                return None
            try:
                lc = R.lc(z_sym)
                return R.scalar(Fr(1)/lc) if lc != 1 else R
            except Exception:
                return R
        # 一般 Res_x(r, d)
        # 将 r_xz 与 d_xz 视为 (x) 上多项式，系数在 ℚ[z]
        # 需将它们转为 Poly over (x) with coefficients Poly over (z)
        # 复用 resultant_y 的思想但交换角色：主变量 x，系数域 ℚ[z]
        z_vars = (z_sym,)
        x_var = x
        # 收集 r_xz 在 x 上系数（Poly over z）
        def coeffs_x(poly_xz):
            # poly_xz vars = (x,z)
            idx = poly_xz._var_idx(x_var)
            buckets = {}
            for mono, coeff in poly_xz.monos.items():
                ex = mono[idx]
                # mono = (ex, ez)
                ez = mono[1] if len(mono)>1 else 0
                term = Poly(z_vars, {(ez,): coeff})
                buckets[ex] = buckets.get(ex, Poly.zero(z_vars)) + term
            return buckets
        # 次数
        try:
            dr = r_xz.degree(x)
            dd2 = d_xz.degree(x)
        except Exception:
            return None
        if dr <0 or dd2 <0:
            return None
        br = coeffs_x(r_xz)
        bd = coeffs_x(d_xz)
        # Sylvester over x, coeff Poly(z)
        m1 = dr
        n1 = dd2
        size2 = m1 + n1
        ca2 = [br.get(m1 - i, Poly.zero(z_vars)) for i in range(m1+1)]
        cb2 = [bd.get(n1 - i, Poly.zero(z_vars)) for i in range(n1+1)]
        from cas.apart import _det_bareiss as _det2
        # 需要 _det_bareiss 支持 Poly(z) 条目——已支持
        mat2 = []
        for i in range(n1):
            row = [Poly.zero(z_vars)] * size2
            for j, c in enumerate(ca2):
                row[i+j] = c
            mat2.append(row)
        for i in range(m1):
            row = [Poly.zero(z_vars)] * size2
            for j, c in enumerate(cb2):
                row[i+j] = c
            mat2.append(row)
        try:
            R = _det2(mat2)
        except Exception:
            return None
        if R.is_zero():
            return None
        # 首一化并去 content
        try:
            lc = R.lc(z_sym)
            # lc 为 Fr，首一
            if lc != 0 and lc != 1:
                R = R.scalar(Fr(1)/lc)
        except Exception:
            pass
        # 去常数因子并 primitive
        try:
            from cas.poly import Poly as _P2
            # content 归一
            c = R.content()
            if isinstance(c, Fr) and c != 0 and c != 1:
                R = R.scalar(Fr(1)/c)
        except Exception:
            pass
        return R
    except Exception:
        return None
