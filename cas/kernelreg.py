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


def try_collapse(b, ef):
    """N3 项级闸门：常数语境 b^(p/q) 是否已落已知根式域的完全幂。

    单叶情形（b 为 ℚ[leaf] 多项式、leaf=正数值底有理指数幂）：
    建临时 ℚ-单扩张（不注册——闸门先于注册，失败零痕迹），交
    denest.perfect_power 三态判定；'yes' 时以 y^p 替换原幂。
    其余形态（多叶/嵌套超越/非 Fr 叶）诚实返回 None——照常建核，
    不阻塞主流程。"""
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
                if any(u == l for l in leaves):
                    continue
                leaves.append(u)
                continue
            stack.extend(u.args)
            continue
        if isinstance(u, Expr):
            stack.extend(u.args)
    if len(leaves) != 1:
        return None
    leaf = leaves[0]
    lb, le = leaf.args
    lf = le.f
    m = [_Fr(-(num_val(lb) ** lf.numerator))] + [_Fr(0)] * (lf.denominator - 1) + [_Fr(1)]
    from cas.algfield import AlgField, AlgElem
    fld = AlgField(m, _Fr(1), zero_c=_Fr(0), origin=leaf)
    try:
        from cas.poly import Poly
        sub = T.subst(b, {leaf: S("_tc_a")})
        gp = Poly.from_term(sub, (S("_tc_a"),))
    except Exception:
        return None
    d = lf.denominator
    cs = [_Fr(0)] * d
    ok = False
    for mono, c in gp.monos.items():
        if len(mono) == 1 and isinstance(c, _Fr) and mono[0] < d:
            cs[mono[0]] += c
            ok = True
    if not ok:
        return None
    from cas.denest import perfect_power
    verdict, y = perfect_power(fld.elem(cs), q_)
    if verdict != 'yes' or y is None:
        return None
    # 主支校正：perfect_power 只保证 y^q=x；数值对拍 cmath 主值，
    # 反向根翻号（±y 是仅有的实根候选）。
    import cmath
    lv = float(num_val(lb)) ** (float(lf.numerator) / lf.denominator)
    cand = complex(sum(float(c) * lv ** i for i, c in enumerate(y.cs)))
    target = complex(sum(float(c) * lv ** i
                         for i, c in enumerate(cs))) ** (1.0 / q_)
    if abs(cand - target) > 1e-8 * max(1.0, abs(target)):
        y = fld.elem([-c for c in y.cs])
    yterm = y.to_term()
    return T.mk(S("Power"), (yterm, N(p_)))
