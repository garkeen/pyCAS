"""数值求值层（验证/抽查工具，非计算通道）。

定位：只做裁决，不进主通道——equivalent 的 PROBABLE 采样、差分测试、
check_solution 数值侧。与"纯符号、无浮点"哲学不冲突：计算路径永远纯符号。

- eval_exact：环层精确有理求值（Plus/Times/整数幂），失败抛 EvalNumError；
- eval_approx：含超越函数的浮点近似（函数实现来自 FunctionSpec.numeric）；
- sample_agrees：结构化采样点一致性检查（带极点保护），只产出"一致/未知"，
  绝不产出否证（否证必须走符号通道——永不静默错）。
"""

import itertools
import math
from fractions import Fraction as Fr

from cas import term as T
from cas.term import Expr, Int, Rat, Sym, Const
from cas import spec as _spec


class EvalNumError(Exception):
    pass


def eval_exact(t, env):
    """精确有理求值：仅环层（Plus/Times/整数幂）。

    env: {Sym: Fraction}。超出环层（超越函数、常数、非整数幂）抛 EvalNumError。
    """
    if T.is_num(t):
        return T.num_val(t)
    if isinstance(t, Sym):
        if t in env:
            return env[t]
        raise EvalNumError(f"unbound symbol {t.name}")
    if isinstance(t, Const):
        raise EvalNumError(f"constant {t.name} not exactly evaluable")
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
            raise EvalNumError("non-integer power not exact")
    raise EvalNumError(f"not exactly evaluable: {t!r}")


def eval_approx(t, env):
    """浮点近似求值（验证工具）。超越函数走 FunctionSpec.numeric。"""
    if T.is_num(t):
        return float(T.num_val(t))
    if isinstance(t, Sym):
        if t in env:
            return float(env[t])
        raise EvalNumError(f"unbound symbol {t.name}")
    if isinstance(t, Const):
        if t is T.PI:
            return math.pi
        if t is T.E:
            return math.e
        raise EvalNumError(f"constant {t.name} not numerically evaluable")
    if isinstance(t, Expr):
        n = t.head.name
        if n == "Plus":
            acc = 0.0
            for a in t.args:
                acc += eval_approx(a, env)
            return acc
        if n == "Times":
            acc = 1.0
            for a in t.args:
                acc *= eval_approx(a, env)
            return acc
        if n == "Power":
            bv = eval_approx(t.args[0], env)
            ev = eval_approx(t.args[1], env)
            if bv < 0 and ev != int(ev):
                raise EvalNumError("negative base with fractional power")
            try:
                return bv ** ev
            except (OverflowError, ZeroDivisionError, ValueError):
                raise EvalNumError("power undefined at sample point")
        sp = _spec.get(n)
        if sp is not None and sp.numeric is not None:
            args = [eval_approx(a, env) for a in t.args]
            try:
                return float(sp.numeric(*args))
            except (ValueError, ZeroDivisionError, OverflowError):
                raise EvalNumError(f"{n} undefined at sample point")
    raise EvalNumError(f"not numerically evaluable: {t!r}")


# 结构化采样点（有理，覆盖正负与分数）
_POINTS = (
    Fr(1, 3), Fr(2, 5), Fr(3, 2), Fr(-1, 2),
    Fr(4, 3), Fr(7, 5), Fr(-2, 3), Fr(5, 7),
)


def sample_agrees(a, b, vars_, tol=1e-8, min_points=4, max_checks=16):
    """采样一致性：a、b 在足够多采样点数值一致 -> True；否则 None（未知）。

    极点保护：任一侧求值失败或绝对值过大（疑似极点）的点跳过。
    只产出 True/None——采样是探测器不是证明，否证必须走符号通道。
    """
    agree = 0
    checked = 0
    combos = itertools.product(_POINTS, repeat=len(vars_)) if vars_ else [()]
    for combo in combos:
        env = dict(zip(vars_, combo))
        try:
            va = eval_approx(a, env)
            vb = eval_approx(b, env)
        except (EvalNumError, OverflowError):
            continue
        if abs(va) > 1e6 or abs(vb) > 1e6:
            continue
        checked += 1
        scale = max(1.0, abs(va), abs(vb))
        if abs(va - vb) <= tol * scale:
            agree += 1
        if checked >= max_checks:
            break
    if checked >= min_points and agree == checked:
        return True
    return None
