"""N4 构造期收缩规则集（M78.4）。

纪律：只收"在本系统域声明语义下无条件成立"的恒等式，
分支破裂者一律不收（对标 FriCAS elemntry.spad iiilog/ilog 的
构造期收缩思想，规则本体为本项目域声明下的独立推导）：

  · Exp(Log u) -> u         Log 的 dom 声明即 u>0（主支）；Exp∘Log=id
  · Exp(r·Log u) -> u^r     同上，r ∈ ℚ
  · Exp(Σ) 选择性拆分       把"纯有理系数·Log u"求和项提出为幂积，
                            余项保持单一 Exp（非盲展开，和严格缩短）
  · Log(Exp u) -> u         仅当 u 可证明实局部（此时 e^u>0 恒落
                            Log 定义域；复 u 有分支破裂，不收）
  · Log(u^n) -> n·Log u     n 奇：输入定义域上无条件的（u^n>0 ⟹
                            u>0 ⟹ 右侧良定义且相等）；n 偶：u=−2,
                            n=2 反例（左定义右未定义）⟹ 需 u>0 可证
  · Log(E·rest) -> 1+Log(rest)  正实常数因子剥离：乘正实数不变辐角，
                            主分支安全；一般 Log(ab) 不拆
  · sin/cos/tan 的 π 有理倍数精确值：分母 q∈{1,2,3,4,6} 全类由
    ℚ(√d) 序对旋转递推生成（非手抄表），任意整数倍经周期归约；
    tan 极角诚实拒绝折叠。

全部规则严格缩减度量（核数/参数规模），构造期不动点有限保证。
"""

import math
from fractions import Fraction as Fr

from cas import term as T
from cas.term import S, N, PI, E, IU, ZERO, ONE


# ---------------------------------------------------------------------------
# 保守 oracle：False 仅表示"不可证明"，绝不作否定断言（三态诚实协议）
# ---------------------------------------------------------------------------

_REAL_FUNCS = frozenset((
    "Exp", "Sin", "Cos", "Tan", "Cot", "Sec", "Csc",
    "Sinh", "Cosh", "Tanh", "Atan", "Arcsin", "Arccos", "Abs",
))


def provably_real(t):
    if isinstance(t, (T.Int, T.Rat)):
        return True
    if isinstance(t, T.Const):
        return t is not IU
    if isinstance(t, T.Sym):
        return True                      # 变元实数约定
    if isinstance(t, T.Expr):
        n = t.head.name
        if n in ("Plus", "Times"):
            return all(provably_real(a) for a in t.args)
        if n == "Power":
            b, e = t.args
            if isinstance(e, T.Int):
                return provably_real(b)
            return provably_positive(b)  # 非整幂：底正才保实
        if n == "Log":
            return provably_positive(t.args[0])
        if n in _REAL_FUNCS:
            return provably_real(t.args[0])
    return False


def provably_positive(t):
    if isinstance(t, (T.Int, T.Rat)):
        return T.num_val(t) > 0
    if isinstance(t, T.Const):
        return t is E or t is PI
    if isinstance(t, T.Sym):
        return False
    if isinstance(t, T.Expr):
        n = t.head.name
        if n in ("Plus", "Times"):
            return all(provably_positive(a) for a in t.args)
        if n == "Power":
            b, e = t.args
            if isinstance(e, T.Int):
                if e.v % 2 == 0:
                    return True          # 定义域上恒正（u=0 时未定义）
                return provably_positive(b)
            return provably_positive(b)
        if n == "Exp":
            return provably_real(t.args[0])
    return False


# ---------------------------------------------------------------------------
# Exp / Log 收缩
# ---------------------------------------------------------------------------

def _rat_log_factor(s):
    """s = r·Log(u)（r∈ℚ 非零）或 Log(u) -> (r, u)；否则 None。"""
    if not isinstance(s, T.Expr):
        return None
    if s.head.name == "Log":
        return Fr(1), s.args[0]
    if s.head.name == "Times":
        logs = []
        coef = Fr(1)
        for a in s.args:
            if isinstance(a, T.Expr) and a.head.name == "Log":
                logs.append(a)
            elif T.is_num(a):
                coef *= T.num_val(a)
            else:
                return None
        if len(logs) == 1 and coef != 0:
            return coef, logs[0].args[0]
    return None


def exp_contract(a):
    # 数值字面参数不收缩：exp(1) 在验证链中是塔核（与命名原子 E 构成
    # 双面孔同一性，E^n≡exp(n) 的规范律使两面孔不可混用——ei 族回归
    # 钉实证）。面孔统一属 N6 超越常数关系表管辖。
    if T.is_num(a):
        return None
    pair = _rat_log_factor(a)
    if pair is not None:
        r, u = pair
        return T.pw(u, N(r))
    if isinstance(a, T.Expr) and a.head.name == "Plus":
        peeled, rest = [], []
        for s in a.args:
            p = _rat_log_factor(s)
            if p is not None:
                peeled.append(p)
            else:
                rest.append(s)
        if not peeled:
            return None
        prods = [T.pw(u, N(r)) for r, u in peeled]
        if rest:
            rs = plus_all(rest)
            # rest 折叠为字面 1 时用命名常数 E 出口。注意：全局
            # Exp(1)->E 特殊点折叠不安全——exp(1) 在验证链中是塔核
            # （参与 exp(x-1) 类线性拆分消去），E 是不透明超越原子，
            # 二者代数角色不同（ei 族回归钉实证）。仅在收缩出口局部
            # 采用命名形。
            prods.append(T.E if rs is ONE else T.exp(rs))
        return T.times(*prods) if len(prods) > 1 else prods[0]
    return None


def log_contract(a):
    if not isinstance(a, T.Expr):
        return None
    n = a.head.name
    if n == "Exp":
        u = a.args[0]
        return u if provably_real(u) else None
    if n == "Power":
        u, e = a.args
        if isinstance(e, T.Int) and e.v != 0:
            if e.v % 2 == 1 or provably_positive(u):
                return T.times(N(e.v), T.log(u))
        return None
    if n == "Times":
        rest, has_e = [], False
        for f in a.args:
            if f is E:
                has_e = True
            else:
                rest.append(f)
        if not has_e:
            return None
        if not rest:
            return ONE
        core = T.times(*rest) if len(rest) > 1 else rest[0]
        return T.plus(ONE, T.log(core))
    return None


def plus_all(args):
    return T.plus(*args)


# ---------------------------------------------------------------------------
# π 有理倍数精确值：ℚ(√d) 序对旋转全类生成
# 值 = a + b·√d（Fr 序对）；乘法 (a,b)(c,e) = (ac+d·be, ae+bc)
# ---------------------------------------------------------------------------

_BASE = {
    1: ((Fr(0), Fr(0)), (Fr(-1), Fr(0)), 2),
    2: ((Fr(1), Fr(0)), (Fr(0), Fr(0)), 2),
    3: ((Fr(0), Fr(1, 2)), (Fr(1, 2), Fr(0)), 3),
    4: ((Fr(0), Fr(1, 2)), (Fr(0), Fr(1, 2)), 2),
    6: ((Fr(1, 2), Fr(0)), (Fr(0), Fr(1, 2)), 3),
}

_TABLE_CACHE = {}


def _pmul(p, q_, d):
    a, b = p
    c, e = q_
    return (a * c + d * b * e, a * e + b * c)


def _psub(p, q_):
    return (p[0] - q_[0], p[1] - q_[1])


def _pi_table(q_):
    """θ=k·π/q，k=0..2q−1 的 (sin, cos) 序对表。"""
    tbl = _TABLE_CACHE.get(q_)
    if tbl is not None:
        return tbl
    s1, c1, d = _BASE[q_]
    out = [((Fr(0), Fr(0)), (Fr(1), Fr(0)))]
    sk, ck = (Fr(0), Fr(0)), (Fr(1), Fr(0))
    for _ in range(2 * q_ - 1):
        sk2 = _padd(_pmul(sk, c1, d), _pmul(ck, s1, d))
        ck2 = _psub(_pmul(ck, c1, d), _pmul(sk, s1, d))
        sk, ck = sk2, ck2
        out.append((sk, ck))
    _TABLE_CACHE[q_] = out
    return out


def _padd(p, q_):
    return (p[0] + q_[0], p[1] + q_[1])


def _pair_term(p, d):
    a, b = p
    if b == 0:
        return N(a)
    if a == 0:
        if b == 1:
            return T.sqrt(N(d))
        if b == -1:
            return T.neg(T.sqrt(N(d)))
        return T.times(N(b), T.sqrt(N(d)))
    return T.plus(N(a), T.times(N(b), T.sqrt(N(d))))


def _pi_exact(name, k):
    """name ∈ {Sin, Cos, Tan} 在 k·π 处的精确值项；不可表/极角 -> None。"""
    den = k.denominator
    q_ = den if den in _BASE else None
    if q_ is None:
        return None
    p = k.numerator % (2 * q_)
    s, c = _pi_table(q_)[p]
    d = _BASE[q_][2]
    if name == "Sin":
        return _pair_term(s, d)
    if name == "Cos":
        return _pair_term(c, d)
    # Tan：余弦为零 = 极角，诚实拒绝
    if c == (Fr(0), Fr(0)):
        return None
    return T.div(_pair_term(s, d), _pair_term(c, d))


def _trig_contract(name):
    def go(a):
        if a is PI:
            return _pi_exact(name, Fr(1))
        if isinstance(a, T.Expr) and a.head.name == "Times":
            nums = [T.num_val(x) for x in a.args if T.is_num(x)]
            rest = [x for x in a.args if not T.is_num(x)]
            if len(nums) == 1 and len(rest) == 1 and rest[0] is PI:
                return _pi_exact(name, nums[0])
        return None
    return go


# ---------------------------------------------------------------------------
# 注册：替换 SPECS 条目的 contract 字段（frozen dataclass -> replace）
# ---------------------------------------------------------------------------

def install():
    from dataclasses import replace
    from cas.spec import SPECS, FunctionSpec

    assert "contract" in FunctionSpec.__dataclass_fields__
    plans = {
        "Exp": exp_contract,
        "Log": log_contract,
        "Sin": _trig_contract("Sin"),
        "Cos": _trig_contract("Cos"),
        "Tan": _trig_contract("Tan"),
    }
    for name, fn_ in plans.items():
        sp = SPECS[name]
        SPECS[name] = replace(sp, contract=fn_)
