"""N6-P1 核关系统一注册表（M78.5）。

架构裁定（notes.md #10）：所有分发器查同一份核关系。本模块是
唯一入口视图；存储分两区：

  代数区    —— 即 cas.algfield.ALG_FIELDS（原样保留语义，现有
              消费者零改动）；本模块提供统一查询/遍历 API，
              P3 批四孤岛（QxStruct _rcN / 塔 'algebraic' 层 /
              solve Phase α① / _collect_radical _aN）迁移后
              全部经此处访问。
  超越常数关系区 —— 命名原子与核字面的同一性（E ≡ exp(1)）。
              `const_face_key` 给出常数项的规范面孔键：不同面孔
              （命名形 vs 核形）同值 ⟹ 同键。消费方（P2）：z-参
              数化层据其把两面孔映到同一 z-符号（叶键级同一性，
              非 mk 折叠——保住验证链的塔核角色）。

诚实边界：关系表只收无条件下成立的恒等式（E=exp(1) 定义级；
log(e)=1 已由 spec.special 承担）；分支敏感者不收。
"""

from fractions import Fraction as Fr

from cas.term import S, N, Expr, Rat, Const, is_num, num_val
import cas.term as T

from cas.algfield import ALG_FIELDS, AlgField


# ---------------------------------------------------------------------------
# 代数区：统一视图 API（存储仍为 ALG_FIELDS 本尊）
# ---------------------------------------------------------------------------

def alg_field(sym):
    """按符号查已注册代数域；无则 None。"""
    return ALG_FIELDS.get(sym)


def alg_fields():
    """全部已注册代数域 {sym: AlgField}（快照副本）。"""
    return dict(ALG_FIELDS)


def register(sym, fld):
    from cas.algfield import register_alg_field
    register_alg_field(sym, fld)


def unregister(syms):
    from cas.algfield import unregister_alg_fields
    unregister_alg_fields(syms)


# ---------------------------------------------------------------------------
# 超越常数关系区：规范面孔键
# ---------------------------------------------------------------------------

def const_face_key(t):
    """常数子项的规范面孔键（可哈希 tuple）；未知形态返回 None。

    统一律：
      Const E            -> ('exp', Fr(1))
      Exp(有理字面 v)     -> ('exp', v)
      其余命名常数        -> ('named', 名称)
    两面孔同值 ⟹ 同键（P2 的 z-符号合一依据）。
    """
    if isinstance(t, Const):
        if t is T.E:
            return ('exp', Fr(1))
        return ('named', t.name)
    if isinstance(t, Expr) and t.head.name == "Exp":
        a = t.args[0]
        if is_num(a):
            v = num_val(a)
            if isinstance(v, Fr):
                return ('exp', v)
        return None
    if is_num(t):
        v = num_val(t)
        if isinstance(v, Fr):
            return ('rat', v)
    return None


def same_constant(a, b):
    """两常数子项是否同面孔键（三态：True/False/None=不可判定）。"""
    ka, kb = const_face_key(a), const_face_key(b)
    if ka is None or kb is None:
        return None
    return ka == kb


def iter_exp_literals():
    """当前已知的 (有理指数,) 字面枚举（诊断/测试用）。"""
    return [('exp', Fr(1))]


# ---------------------------------------------------------------------------
# 代数区：根式常数唯一建域点（B2 收敛，P3）
# ---------------------------------------------------------------------------
# 四孤岛（QxStruct/_collect_radical/塔层/solve α①）此前各自构造
# T^q − b^p 极小多项式并各用键方案去重；本节收敛为单一原语，
# 岛侧全部降级为消费者。

_RADICAL_COUNTER = [0]


def register_numeric_radical(bv, p_, q_, sym=None, bracket=None,
                             origin=None):
    """数值底 b^(p/q)：T^q − b^p 建域入册，返回符号；已注册按规范键
    复用现有域（不新建）。bv<=0 不登记返回 None。

    bracket（实嵌入区间）进规范键：同一极小多项式在不同嵌入下是
    不同域身份——混同曾致主支选择失效（负底分数幂泄漏）。"""
    if bv <= 0:
        return None
    key = ("num", bv, p_, q_,
           None if bracket is None else (bracket[0], bracket[1]))
    for s0, f0 in ALG_FIELDS.items():
        if f0.key == key:
            return s0
    if sym is None:
        _RADICAL_COUNTER[0] += 1
        sym = S(f"_a{_RADICAL_COUNTER[0]}")
    fld = AlgField([Fr(-(bv ** p_))] + [Fr(0)] * (q_ - 1) + [Fr(1)],
                   Fr(1), zero_c=Fr(0),
                   origin=origin, key=key, bracket=bracket)
    register(sym, fld)
    return sym


def register_symbolic_radical(num, den, p_, q_, sym=None, origin=None):
    """符号底（ℚ(params) 元素 num/den，指数 p_/q_）：Capelli 完整判定
    不可约后以 SymRat 系数建 m(T)=T^q−(num/den)^p 入册；可约抛
    RischUnsupported（诚实拒答——退化根式归一化前置缺失，绝不静默
    错域）。"""
    from cas.poly import Poly, SymRat
    from cas.algfield import binomial_irreducible
    from cas.risch_core import RischUnsupported
    if not binomial_irreducible(num, den, q_):
        raise RischUnsupported(
            "radical constant has reducible binomial min polynomial "
            "(degenerate radical pending normalization)")
    key = ("sym", q_, str(sorted(num.monos.items())),
           str(sorted(den.monos.items())))
    for s0, f0 in ALG_FIELDS.items():
        if f0.key == key:
            return s0
    if sym is None:
        _RADICAL_COUNTER[0] += 1
        sym = S(f"_a{_RADICAL_COUNTER[0]}")
    one_c = SymRat(Poly.one(()), Poly.one(()))
    zero_c = SymRat(Poly.zero(()), Poly.one(()))
    # m(T) = T^q − b^p：b 以域元素 num/den 表示，m 升序 = [−(n/d)^p, 0.., 1]
    negG = -SymRat(num ** p_, den ** p_)
    coefs = [negG] + [zero_c] * (q_ - 1) + [one_c]
    fld = AlgField(coefs, one_c, zero_c=zero_c,
                   origin=origin, key=key)
    register(sym, fld)
    return sym


def _try_cross_quad(a0_elem, fld, r_leaf):
    """ℚ(√r) 中 a0+a1√r 的平方根跨域公式：√(a0+a1√r)=√p+√q（p=(a0+c)/2）。

    c=√(a0²−a1²r) 须为 ℚ 中平方，p,q≥0。返回 y term（√p+√q）或 None。
    """
    from math import isqrt
    if len(fld.m) != 3 or fld.m[2] != 1 or fld.m[1] != 0:
        return None
    r = -fld.m[0]
    if not isinstance(r, Fr) or r <= 0:
        return None
    cs = list(a0_elem.cs) + [Fr(0)] * (2 - len(a0_elem.cs))
    a0, a1 = cs[0], cs[1]
    D = a0 * a0 - a1 * a1 * r
    if D < 0:
        return None
    # D 须为有理平方
    n, d = D.numerator, D.denominator
    rn, rd = isqrt(n), isqrt(d)
    if rn * rn != n or rd * rd != d:
        return None
    c = Fr(rn, rd)
    p = (a0 + c) / Fr(2)
    q = (a0 - c) / Fr(2)
    if p < 0 or q < 0:
        return None
    # 验证 pq = a1²r/4（数值闭合）
    if p * q != a1 * a1 * r / Fr(4):
        return None
    # 构造 √p + √q（p,q 为有理数，直接 Power）
    # p 或 q 可能为完全平方有理数，mk 会进一步 via radnorm 归一
    import cas.term as _T
    from cas.term import S as _S, N as _N
    parts = []
    for val in (p, q):
        if val == 0:
            continue
        # 有理平方化简：4 →2, 9/4→3/2 等由 radnorm 承担，此处直构造 Power
        if val == 1:
            # √1 =1，已在 p/q 构造中消去零项，此分支不触发
            parts.append(_N(1))
        else:
            # 用 mk 保证 Power(1,1/2) 归一
            parts.append(_T.mk(_S("Power"), (_N(val), _N(Fr(1, 2)))))
    if not parts:
        return None
    y = parts[0] if len(parts) == 1 else _T.mk(_S("Plus"), tuple(parts))
    # 符号：a1<0 时 √p−√q（主支正根，a0+a1√r>0 已保证）
    if a1 < 0 and len(parts) == 2:
        # y = √p − √q 的主支仍正（因 a0>0 且 |a1|√r < a0 当 D>0）
        y = _T.mk(_S("Plus"), (parts[0], _T.neg(parts[1])))
    # 主支数值校正：与 perfect_power 同款 cmath 对拍
    return y


def try_collapse(b, ef):
    """N3 项级闸门（通用形态，叶数无关）：

    收集常数语境 b 的全部数值根式叶 -> primelt 链式本原元压缩进
    单一 ℚ(β)（不可约门+生成元精确回验）-> b 映入域元素 ->
    denest.perfect_power 三态判定（同域）或跨域二次公式（rsimp p₂c）
    -> 命中则经 β 项级 origin 回代并做主支数值校正。任一步不可判定/
    超界 ⟹ None（照常建核，不阻塞主流程；失败零痕迹）."""
    from fractions import Fraction as _Fr
    if ef.denominator < 2:
        return None
    q_ = ef.denominator
    p_ = ef.numerator
    leaves = []
    stack = [b]
    while stack:
        u = stack.pop()
        if isinstance(u, Expr) and u.head.name == "Power":
            a0, a1 = u.args
            if is_num(a0) and isinstance(a1, Rat) \
                    and a1.f.denominator > 1 and num_val(a0) > 0:
                if not any(u == l for l in leaves):
                    leaves.append(u)
                continue
            stack.extend(u.args)
            continue
        if isinstance(u, Expr):
            stack.extend(u.args)
    if not leaves:
        return None
    ms = []
    for l in leaves:
        lb, le = l.args
        lf = le.f
        bv = num_val(lb)
        if bv <= 0 or lf.denominator < 2:
            return None
        ms.append([_Fr(-(bv ** lf.numerator))]
                  + [_Fr(0)] * (lf.denominator - 1) + [_Fr(1)])
    from cas.primelt import compress_chain
    cres = compress_chain(ms, leaves)
    if cres is None:
        return None
    Scoefs, maps, beta_term = cres
    d = len(Scoefs) - 1
    from cas.denest import perfect_power, _DEG_CAP
    if d > _DEG_CAP:
        return None
    from cas.algfield import af_q
    fld = af_q([_Fr(x) for x in Scoefs], origin=beta_term)
    gen = fld.gen()

    def mk_elem(mp):
        e = fld.zero
        for cc in reversed(mp):
            e = e * gen + fld.const(cc)
        return e

    elems = [mk_elem(mp) for mp in maps]
    syms = [S(f"_tc{i}") for i in range(len(leaves))]
    sub = {leaves[i]: syms[i] for i in range(len(leaves))}
    try:
        from cas.poly import Poly
        gp = Poly.from_term(T.subst(b, sub), tuple(syms))
    except Exception:
        return None
    elem = fld.zero
    for mono, cf in gp.monos.items():
        te = fld.const(cf)
        for si, ex in enumerate(mono):
            for _ in range(ex):
                te = te * elems[si]
        elem = elem + te
    # 通用落域判定：ℚ(β) 内完全幂判定走 denest 唯一基础设施（Groebner 坐标法三态）
    # 无小盒枚举特判，任意 y∈ℚ(β) 的 y^q=x 判定由 perfect_power 覆盖
    verdict, y = perfect_power(elem, q_)
    if verdict == 'yes' and y is not None:
        yterm = y.to_term()
    else:
        yterm = None
    if not (verdict == 'yes' and y is not None and yterm is not None):
        # 跨域二次坍缩（rsimp p₂c）：ℚ(√r) 内 a0+a1√r 的平方根落在 ℚ(√p,√q)
        if q_ == 2 and len(leaves) == 1 and d == 2:
            yterm = _try_cross_quad(a0_elem=elem, fld=fld, r_leaf=leaves[0])
            if yterm is None:
                return None
        else:
            return None
    # 主支校正：perfect_power 只保证 y^q=x；数值对拍 cmath 主值，
    # 反向根翻号（±y 是仅有的实根候选）
    import cmath
    from cas.evalnum import eval_approx
    try:
        xv = eval_approx(b, {})
        cand = eval_approx(yterm, {})
    except Exception:
        return None
    target = complex(xv) ** (1.0 / q_)
    if abs(complex(cand) - target) > 1e-8 * max(1.0, abs(target)):
        yterm = T.neg(yterm)
    return T.mk(S("Power"), (yterm, N(p_)))


