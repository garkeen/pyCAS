"""ℚ 字面算术层（数域系统第一块地基，cas_v3_arch.md 三）。

职责边界：只对**全字面有理数子树**做精确算术，不合并同类项、不碰
符号幂、不做任何分支破裂的改写。x+x 与 x*x 的收集属于多项式机器
（第四层公共算法机器），本层永远不碰。

这是显式调用层，不是构造期魔法：L0 驻留保持纯句法（手术裁定），
消费方（判定管线、验证回代、战术步）在需要算术语义时主动调 fold。

- fold：自底向上折叠字面子树。Plus/Times 提取数字因子并吸收中性元
  （+0、×1、×0），整数幂精确计算；除零与 0^0/0^负 保持驻留——
  未定义性由域闸门裁决，本层不猜。
- eval_exact：环层精确求值（env 绑定），回代验证与压力测试判官的
  唯一算术通道。
"""

from fractions import Fraction as Fr

from cas.term import Expr, Int, Sym, S, N
from cas import term as T


class EvalNumError(Exception):
    pass


_MAX_EXP = 4096          # 字面幂安全上限：防 2^(10^9) 级爆炸


def _flat(head, args):
    """同头递归拉平（先于数字收集）：子项折叠中的单因子解包会让
    嵌套字面量经 mk 句法拉平浮到本层，收集必须发生在拉平之后。"""
    out = []
    for a in args:
        if isinstance(a, Expr) and a.head.name == head:
            out.extend(_flat(head, a.args))
        else:
            out.append(a)
    return out


def fold(t):
    """ℚ 字面折叠。返回树中每个全数字子树被其精确值替换后的驻留形式。

    规则（全部是 ℚ 半环恒等式，无分支破裂）：
      · Plus：数字项求和归一；和为 0 且存在非数字项时整体吸收；
      · Times：任一数字因子为 0 -> 全体归 0；数字因子连乘，
        积为 1 且存在非数字因子时吸收；
      · Power：底为字面数且指数为整数字面量 -> 精确幂
        （底 0 仅正偶……仅正指数可行；负指数要求底非零）。
    除法不存在于句法层（a/b 即 Power(a,-1) 或 Rat），无需特判。
    """
    if not isinstance(t, Expr):
        return t
    head = t.head.name

    if head == "Plus":
        args = _flat("Plus", [fold(a) for a in t.args])
        c = Fr(0)
        rest = []
        for a in args:
            if T.is_num(a):
                c += T.num_val(a)
            else:
                rest.append(a)
        if not rest:
            return N(c)
        if c != 0:
            rest.append(N(c))
        return rest[0] if len(rest) == 1 else T.mk(S("Plus"), tuple(rest))

    if head == "Times":
        args = _flat("Times", [fold(a) for a in t.args])
        c = Fr(1)
        rest = []
        for a in args:
            if T.is_num(a):
                c *= T.num_val(a)
                if c == 0:
                    return N(0)
            else:
                rest.append(a)
        if not rest:
            return N(c)
        if c != 1:
            rest.append(N(c))
        return rest[0] if len(rest) == 1 else T.mk(S("Times"), tuple(rest))

    args = [fold(a) for a in t.args]
    if head == "Power":
        b, e = args
        if isinstance(e, Int) and abs(e.v) <= _MAX_EXP:
            if e.v == 1:
                return b                      # b^1 = b：幺半群恒等，普适
            if e.v == 0:
                return T.mk(t.head, (b, e))   # u^0：0^0 争议，驻留给域层（子项仍折叠）
            if T.is_num(b):
                bv = T.num_val(b)
                if bv != 0:
                    return N(bv ** e.v if e.v > 0 else Fr(1) / (bv ** -e.v))
                if e.v > 0:
                    return N(0)
                return T.mk(t.head, (b, e))   # 0^负：未定义，驻留（子项仍折叠）
        return T.mk(t.head, (b, e))

    return T.mk(t.head, tuple(args))


def eval_exact(t, env):
    """环层精确有理求值（v2 evalnum 捞回，剥离采样通道）。

    env: {Sym: Fraction}。超出环层（超越头、常数、非整数幂）抛
    EvalNumError——调用方据此判定片段不覆盖，绝不静默近似。
    """
    if T.is_num(t):
        return T.num_val(t)
    if isinstance(t, Sym):
        if t in env:
            return env[t]
        raise EvalNumError(f"unbound symbol {t.name}")
    if isinstance(t, Expr):
        n = t.head.name
        if n == "Plus":
            acc = Fr(0)
            for a in t.args:
                acc += eval_exact(a, env)
            return acc
        if n == "Times":
            acc = Fr(1)
            for a in t.args:
                acc *= eval_exact(a, env)
            return acc
        if n == "Power":
            b, e = t.args
            bv = eval_exact(b, env)
            if isinstance(e, Int):
                if e.v >= 0:
                    return bv ** e.v
                if bv == 0:
                    raise EvalNumError("zero to negative power")
                return Fr(1) / (bv ** (-e.v))
            ev = eval_exact(e, env)
            if ev.denominator == 1:
                v = ev.numerator
                if abs(v) <= _MAX_EXP:
                    if v >= 0:
                        return bv ** v
                    if bv != 0:
                        return Fr(1) / (bv ** (-v))
            raise EvalNumError("non-integer power not exact")
    raise EvalNumError(f"not exactly evaluable: {t!r}")
