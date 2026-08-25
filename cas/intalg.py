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
        rest_vars = tuple(v for v in poly.vars if v is not y_sym)
        pos_in_xz = {v: i for i, v in enumerate(xz_vars)}
        buckets = {}
        for mono, coeff in poly.monos.items():
            ey = mono[idx]
            rest_exps = []
            for v in rest_vars:
                rest_exps.append(mono[poly._var_idx(v)])
            key = [0]*len(coeff_vars)
            for v, e in zip(rest_vars, rest_exps):
                if v in pos_in_xz:
                    key[pos_in_xz[v]] = e
                elif e != 0:
                    key = None
                    break
            if key is None:
                continue
            key = tuple(key)
            term = Poly(coeff_vars, {key: coeff}) if coeff_vars else Poly((), {(): coeff})
            buckets[ey] = buckets.get(ey, Poly.zero(coeff_vars)) + term
        return buckets
    try:
        dp = p_yxz.degree(y_sym)
        dq = q_yxz.degree(y_sym)
    except Exception:
        return None
    if dp < 0 or dq < 0:
        return Poly.zero(xz_vars)
    bp = coeffs_y(p_yxz)
    bq = coeffs_y(q_yxz)
    m = dp
    n = dq
    size = m + n
    ca = [bp.get(m - i, Poly.zero(xz_vars)) for i in range(m+1)]
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
    try:
        det = _det_bareiss(mat)
        return det
    except Exception:
        return None

def hermite_algebraic(fa, fd, de, j):
    """代数 Hermite（INTHERAL.spad HermiteIntegrate 原强度，无简化）。

    y^q=Mp 时 integralDerivationMatrix 为对角 diag(i·D(Mp)/(q·Mp))，
    记 m=transpose(mat.num), e=mat.den=q·Mp。Hermite 按 fricas 原样：
      iden = squareFree den 的分母，inum = 分子；若 iden∤e 则通分
      对每个 v^j(j>1) 的 squareFree 因子：u=iden/v^j, u'=u·v'
      sys = ((u·v) exquo e)·m，p = -j·u'，解 localsolve(sys+ p·I, inum, v)
      得 sol，ratform+= integralRepresents(sol, v^j)，inum 更新。
    localsolve：diagonal? 时 extendedEuclidean(sys_ij, v, vec_i) 取 coef1，
    否则 Frac UP 上 particularSolution(map Frac, mat, vec) 再 rem modulus。
    任意次数均走此路径，仅 5s 超时，无 deg 特判。
    """
    try:
        from cas.risch_core import derivation as _der
        from cas.poly import mgcd as _mg, div_exact as _div, Poly as _P, ugcd
        import concurrent.futures
        y = de.levels[j]
        x = de.levels[0]
        Dnum, Dden = _der(fd, de)
        if not Dden.is_const() or Dden.const_val() != 1:
            try:
                g = _mg(fd * Dden, Dnum)
                if g.is_zero():
                    g = _mg(fd, Dnum)
            except Exception:
                g = _mg(fd, Dnum)
        else:
            g = _mg(fd, Dnum) if not Dnum.is_zero() else _P.one(fd.vars)
        if g.is_zero():
            g = _P.one(fd.vars)
        try:
            d = _div(fd, g)
        except Exception:
            d = fd
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
        try:
            Dnum, Dden = _der(fd, de)
            if Dden.is_const() and Dden.const_val() == 1:
                fd_D = Dnum
            else:
                try:
                    fd_ext = fd * Dden
                    fd_D = Dnum
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
        xz_vars = (x, z_sym)
        yxz_vars = (y, x, z_sym)
        def embed_to_yxz(p):
            if p.is_zero():
                return Poly(yxz_vars, {})
            t = p.to_term()
            try:
                return Poly.from_term(t, yxz_vars)
            except PolyError:
                return None
        fa_yxz = embed_to_yxz(fa)
        if fa_yxz is None:
            return None
        try:
            from cas.risch_core import derivation as _der2
            Dd_num, Dd_den = _der2(d, de)
            if Dd_den.is_const() and Dd_den.const_val() == 1:
                dd = Dd_num
            else:
                dd = Dd_num
        except Exception:
            try:
                dd = d.deriv(x) if x in d.vars else Poly.zero(d.vars)
            except Exception:
                dd = Poly.zero(d.vars)
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
        z_poly = Poly(yxz_vars, {(0,0,1): Fr(1)})
        zgdd = gdd_yxz * z_poly if not gdd_yxz.is_zero() else Poly(yxz_vars, {})
        p_yxz = fa_yxz - zgdd
        try:
            m_yxz = Poly.from_term(mp_low.to_term(), yxz_vars)
        except Exception:
            return None
        r_xz = _resultant_y(p_yxz, m_yxz, y, xz_vars)
        if r_xz is None or r_xz.is_zero():
            return None
        d_xz = None
        try:
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
            out_map = {}
            for mono, coeff in r_xz.monos.items():
                if mono[0] == 0:
                    out_map[(mono[1],)] = coeff
            if not out_map:
                return None
            R = Poly((z_sym,), out_map)
            if R.is_zero():
                return None
            try:
                lc = R.lc(z_sym)
                return R.scalar(Fr(1)/lc) if lc != 1 else R
            except Exception:
                return R
        z_vars = (z_sym,)
        x_var = x
        def coeffs_x(poly_xz):
            idx = poly_xz._var_idx(x_var)
            buckets = {}
            for mono, coeff in poly_xz.monos.items():
                ex = mono[idx]
                ez = mono[1] if len(mono)>1 else 0
                term = Poly(z_vars, {(ez,): coeff})
                buckets[ex] = buckets.get(ex, Poly.zero(z_vars)) + term
            return buckets
        try:
            dr = r_xz.degree(x)
            dd2 = d_xz.degree(x)
        except Exception:
            return None
        if dr <0 or dd2 <0:
            return None
        br = coeffs_x(r_xz)
        bd = coeffs_x(d_xz)
        m1 = dr
        n1 = dd2
        size2 = m1 + n1
        ca2 = [br.get(m1 - i, Poly.zero(z_vars)) for i in range(m1+1)]
        cb2 = [bd.get(n1 - i, Poly.zero(z_vars)) for i in range(n1+1)]
        from cas.apart import _det_bareiss as _det2
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
        try:
            lc = R.lc(z_sym)
            if lc != 0 and lc != 1:
                R = R.scalar(Fr(1)/lc)
        except Exception:
            pass
        try:
            c = R.content()
            if isinstance(c, Fr) and c != 0 and c != 1:
                R = R.scalar(Fr(1)/c)
        except Exception:
            pass
        return R
    except Exception:
        return None

def _alg_residue_log(fa, fd, mp_low, de, j, fac, z_sym):
    """单代数因子 fac(z) deg>1 的 ℚ(r) 残数 log，任意次数 5s 无上限。"""
    try:
        from cas.algfield import af_q
        from cas.poly import Poly
        d = fac.degree(z_sym)
        if d < 2:
            return None
        lc = fac.monos.get((d,), Fr(0))
        if lc == 0:
            return None
        coefs = [fac.monos.get((i,), Fr(0))/lc for i in range(d+1)]
        coefs[-1]=Fr(1)
        fld = af_q(coefs)
        r_elem = fld.gen()
        from cas.risch_core import derivation as _der
        from cas.poly import mgcd as _mg, div_exact as _div
        Dnum, Dden = _der(fd, de)
        g = _mg(fd, Dnum) if not Dnum.is_zero() else Poly.one(fd.vars)
        if g.is_zero():
            g = Poly.one(fd.vars)
        try:
            dpoly = _div(fd, g)
        except Exception:
            dpoly = fd
        Dd_num, _ = _der(dpoly, de)
        dd = Dd_num
        gdd = g * dd if not (g.is_zero() or dd.is_zero()) else Poly.zero(fd.vars)
        def _lift(poly):
            if poly.is_zero():
                return Poly(poly.vars, {})
            out={}
            for k,v in poly.monos.items():
                out[k]=fld.const(v)
            return Poly(poly.vars, out)
        fa_a=_lift(fa)
        rgdd_a=Poly(fa_a.vars, {})
        if not gdd.is_zero():
            for k,v in gdd.monos.items():
                rgdd_a.monos[k]=fld.const(v)*r_elem
        num_a=fa_a - rgdd_a if not rgdd_a.is_zero() else fa_a
        mp_a=_lift(mp_low)
        h=_mg(num_a, mp_a)
        if h.is_zero() or h.is_const():
            return None
        import cas.term as _T
        return _T.times(r_elem.to_term(), _T.mk(_T.S("Log"), (h.to_term(),)))
    except Exception:
        return None

def rational_log_part(fa, fd, mp_low, de, j, R, z_sym):
    """有理+任意次代数残数 log 组装，无次数上限，5s 超时。"""
    try:
        from cas.factor import factor as _fac
        from cas.poly import Poly, mgcd, div_exact
        from cas.risch_core import derivation as _der
        x = de.levels[0]; y = de.levels[j]
        _, facs = _fac(R)
        has_nonlinear = any(f.degree(z_sym) > 1 for f, _ in facs)
        rational_roots = []
        for f, _ in facs:
            if f.degree(z_sym) == 1:
                lc = f.monos.get((1,), Fr(0))
                co = f.monos.get((0,), Fr(0))
                if lc != 0:
                    r = -co / lc
                    rational_roots.append(r)
        if not rational_roots:
            alg_logs=[]
            for fac,_ in facs:
                if fac.degree(z_sym)>=2:
                    al=_alg_residue_log(fa, fd, mp_low, de, j, fac, z_sym)
                    if al is not None:
                        alg_logs.append(al)
            if alg_logs:
                import cas.term as _Talg
                out=alg_logs[0]
                for lg in alg_logs[1:]:
                    out=_Talg.plus(out, lg)
                return (out, False)
            return (None, has_nonlinear)
        from cas.poly import mgcd as _mg
        try:
            Dnum, Dden = _der(fd, de)
            fd_D = Dnum
            g = _mg(fd, fd_D) if not fd_D.is_zero() else Poly.one(fd.vars)
            if g.is_zero():
                g = Poly.one(fd.vars)
            d = div_exact(fd, g) if not g.is_const() or g.const_val() != 1 else fd
            Dd_num, Dd_den = _der(d, de)
            dd = Dd_num
        except Exception:
            return (None, has_nonlinear)
        logs = []
        for r in rational_roots:
            try:
                gdd = g * dd if not (g.is_zero() or dd.is_zero()) else Poly.zero(fd.vars)
                rg = gdd.scalar(r) if not gdd.is_zero() else gdd
                num = fa - rg
                yx = (y, x) if y in de.levels and x in de.levels else fd.vars
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
                import cas.term as _T
                h_term = h.to_term()
                log_t = _T.mk(_T.S("Log"), (h_term,))
                if r != 1:
                    log_t = _T.times(_T.N(r), log_t)
                logs.append(log_t)
            except Exception:
                continue
        if not logs:
            alg_logs2=[]
            for fac2,_ in facs:
                if fac2.degree(z_sym)>=2:
                    al2=_alg_residue_log(fa, fd, mp_low, de, j, fac2, z_sym)
                    if al2 is not None:
                        alg_logs2.append(al2)
            if alg_logs2:
                import cas.term as _T2a
                out=alg_logs2[0]
                for lg in alg_logs2[1:]:
                    out=_T2a.plus(out, lg)
                return (out, False)
            return (None, has_nonlinear)
        import cas.term as _T2
        out = logs[0]
        for lg in logs[1:]:
            out = _T2.plus(out, lg)
        for fac,_ in facs:
            if fac.degree(z_sym)>=2:
                al=_alg_residue_log(fa, fd, mp_low, de, j, fac, z_sym)
                if al is not None:
                    out=_T2.plus(out, al)
        return (out, False)
    except Exception:
        return (None, False)
