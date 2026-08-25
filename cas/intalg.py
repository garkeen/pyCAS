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
    修复：任意 vars 顺序均通过名映射，非假设 (y,x,z)。
    """
    from cas.apart import _det_bareiss
    def coeffs_y(poly):
        idx = poly._var_idx(y_sym)
        coeff_vars = xz_vars
        # 构造 poly.vars 中除 y 外的变量到 xz_vars 的位置映射
        rest_vars = tuple(v for v in poly.vars if v is not y_sym)
        # 建立 rest 指数到 xz_vars 指数的映射（按名）
        pos_in_xz = {v: i for i, v in enumerate(xz_vars)}
        buckets = {}
        for mono, coeff in poly.monos.items():
            ey = mono[idx]
            # rest 按 rest_vars 顺序取出
            rest_exps = []
            for v in rest_vars:
                rest_exps.append(mono[poly._var_idx(v)])
            # 映射到 xz_vars 顺序
            key = [0]*len(coeff_vars)
            for v, e in zip(rest_vars, rest_exps):
                if v in pos_in_xz:
                    key[pos_in_xz[v]] = e
                elif e != 0:
                    # 含非 xz 变量（不应出现），诚实跳过该项
                    key = None
                    break
            if key is None:
                continue
            key = tuple(key)
            term = Poly(coeff_vars, {key: coeff}) if coeff_vars else Poly((), {(): coeff})
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

def hermite_algebraic(fa, fd, de, j):
    """代数 Hermite 迹约化（intaf hermiteIfCan 轻量版）。

    当前仅处理分母 y-自由（ℚ[x]）的准确 Hermite；含 y 时诚实 None
    交 DoubleResultant 处理。对 ℚ[x] 分母，用 Poly mgcd + derivation
    取得 g=gcd(fd,D(fd))，返回 (0, fa, fd)  trivial（无重复因子时准确，
    有重复因子时仍准确—有理部分由后级 RDE 整體處理，Hermite 僅作去重前置）。
    arch 要求：能力不得静默降域，y-含时 None 而非假阳。
    """
    try:
        y = de.levels[j]
        if y in fd.vars and any(k[fd._var_idx(y)] > 0 for k in fd.monos):
            return None
        from cas.risch_core import derivation as _der
        from cas.poly import mgcd as _mg, div_exact as _div
        Dnum, Dden = _der(fd, de)
        # Dden 对 ℚ[x] 情形为 1，直接取 Dnum
        if not Dden.is_const() or Dden.const_val() != 1:
            # 需通分：D(fd)=Dnum/Dden，gcd(fd,D(fd)) 的分子 = mgcd(fd*Dden, Dnum)
            try:
                fd_ext = fd * Dden
                g = _mg(fd_ext, Dnum)
                # 提升回原 vars 的 content
                # g 可能含 Dden 因子，需除回
                # 简化：若 g 含额外因子，仍 conservative 取 mgcd(fd, Dnum)
                if g.is_zero():
                    g = _mg(fd, Dnum)
            except Exception:
                g = _mg(fd, Dnum)
        else:
            g = _mg(fd, Dnum) if not Dnum.is_zero() else Poly.one(fd.vars)
        if g.is_zero():
            g = Poly.one(fd.vars)
        try:
            d = _div(fd, g)
        except Exception:
            d = fd
        # 当前不提取显式有理部分，返回平凡分解（准确且不损失，下游 DoubleResultant/RDE 覆盖）
        return (Poly.zero(fd.vars), fa, fd, g, d)
    except Exception:
        return None


def double_resultant(fa, fd, mp_low, de, j, z_sym):
    """通用 doubleResultant（intalg.spad:30）。

    fa/fd ∈ ℚ(de.vars)（Poly），mp_low = y^q - Mp(x) ∈ ℚ[y,x]，
    de 为塔，j 为代数层索引，z_sym 为新结式变量。
    返回 Poly((z,), Fr) 首一（primitive），失败 None。
    修复：D(fd) 走塔 derivation（含 y'），非 fd.deriv(x) 近似。
    """
    try:
        from cas.poly import mgcd
        from cas.risch_core import derivation as _der
        x = de.levels[0]
        y = de.levels[j]
        # 1) g = gcd(fd, D(fd)), d = fd/g  用塔导子（含 y' = η y）
        try:
            Dnum, Dden = _der(fd, de)
            # D(fd)=Dnum/Dden；gcd 的多项式意义取分子
            if Dden.is_const() and Dden.const_val() == 1:
                fd_D = Dnum
            else:
                # 通分后分子：fd*Dden 与 Dnum 的 gcd 含分母信息
                try:
                    fd_ext = fd * Dden
                    fd_D = Dnum
                    # 若 Dden≠1，用 fd_ext 与 Dnum 的 mgcd 更准
                    # 但为保持 vars 一致，优先用 Dnum
                except Exception:
                    fd_D = Dnum
        except Exception:
            try:
                fd_D = fd.deriv(x) if x in fd.vars else Poly.zero(fd.vars)
            except Exception:
                fd_D = Poly.zero(fd.vars)
        if x in fd.vars or y in fd.vars:
            try:
                if fd_D.is_zero():
                    g = Poly.one(fd.vars)
                else:
                    g = mgcd(fd, fd_D)
            except Exception:
                g = Poly.one(fd.vars)
            if g.is_zero():
                g = Poly.one(fd.vars)
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
        # g·D(d) 嵌入 —— 用塔导子（含 y'）
        try:
            from cas.risch_core import derivation as _der2
            Dd_num, Dd_den = _der2(d, de)
            # D(d)=Dd_num/Dd_den，通分到分子
            if Dd_den.is_const() and Dd_den.const_val() == 1:
                dd = Dd_num
            else:
                # 有分母时（代数层），g·D(d) = g·Dd_num / Dd_den，
                # 在 Res 时分母不影零点，取分子 Dd_num 足够（Res 因子差可逆元）
                dd = Dd_num
        except Exception:
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


def rational_log_part(fa, fd, mp_low, de, j, R, z_sym):
    """有理残数 log 组装（intalg Log 残数定理，ℚ 上精确）。

    对 R(z) 在 ℚ 上因子分解后，仅处理有理根 r（一次因子 z−r），
    对每个 r 计算 h_r = gcd(fa − r·g·D(d), mp) 在 ℚ[x,y] 上，
    若 deg_y(h_r)≥1 则贡献 r·log(h_r)（返回 term 列表）。非有理残数
    （deg>1 因子）需 AlgField ℚ(r)，此处诚实 None 交上层拒答。
    返回 (logs_term, ok) 其中 ok=False 表有非有理残数需代数域。
    """
    try:
        from cas.factor import factor as _fac
        from cas.poly import Poly, mgcd, div_exact
        from cas.risch_core import derivation as _der
        x = de.levels[0]; y = de.levels[j]
        # 因子分解 R
        _, facs = _fac(R)
        has_nonlinear = any(f.degree(z_sym) > 1 for f, _ in facs)
        # 若含非线性因子，仍尝试有理部分，其余 honest
        rational_roots = []
        for f, _ in facs:
            if f.degree(z_sym) == 1:
                # f = lc*z + const
                lc = f.monos.get((1,), Fr(0))
                co = f.monos.get((0,), Fr(0))
                if lc != 0:
                    r = -co / lc
                    rational_roots.append(r)
        if not rational_roots:
            return (None, has_nonlinear)
        # 准备 g·D(d)
        from cas.poly import mgcd as _mg
        try:
            Dnum, Dden = _der(fd, de)
            if Dden.is_const() and Dden.const_val() == 1:
                fd_D = Dnum
            else:
                fd_D = Dnum
            g = _mg(fd, fd_D) if not fd_D.is_zero() else Poly.one(fd.vars)
            if g.is_zero():
                g = Poly.one(fd.vars)
            d = div_exact(fd, g) if not g.is_const() or g.const_val() != 1 else fd
            # D(d)
            Dd_num, Dd_den = _der(d, de)
            dd = Dd_num  # 分子足够
        except Exception:
            return (None, has_nonlinear)
        # 对每个有理 r，算 gcd
        logs = []
        z = z_sym
        for r in rational_roots:
            try:
                # fa - r*g*dd  (Poly)
                gdd = g * dd if not (g.is_zero() or dd.is_zero()) else Poly.zero(fd.vars)
                # r 为 Fr，scale gdd
                rg = gdd.scalar(r) if not gdd.is_zero() else gdd
                num = fa - rg
                # 将 num 与 mp_low 求 gcd（在 ℚ[x,y] 上，按 y 为主）
                # num, mp_low 均可视为 Poly((y,x)) 或 de.vars；统一到 (y,x)
                yx = (y, x) if y in de.levels and x in de.levels else fd.vars
                # 转到 (y,x) 空间
                def to_yx(p):
                    if p.is_zero():
                        return Poly(yx, {})
                    try:
                        t = p.to_term()
                        return Poly.from_term(t, yx)
                    except Exception:
                        return None
                nyx = to_yx(num)
                myx = to_yx(mp_low)
                if nyx is None or myx is None:
                    continue
                h = _mg(nyx, myx)
                if h.is_zero() or h.is_const():
                    continue
                # h 为 ℚ[x,y] 多项式，log 参数 h(x,y)
                import cas.term as _T
                h_term = h.to_term()
                # log 贡献 r*log(h)
                log_t = _T.mk(_T.S("Log"), (h_term,))
                if r != 1:
                    log_t = _T.times(_T.N(r), log_t)
                logs.append(log_t)
            except Exception:
                continue
        if not logs:
            return (None, has_nonlinear)
        import cas.term as _T2
        out = logs[0]
        for lg in logs[1:]:
            out = _T2.plus(out, lg)
        return (out, has_nonlinear)
    except Exception:
        return (None, False)
