# -*- coding: utf-8 -*-
"""约束求解与三值原函数验证（v4 §8.6 / §9.6）。

两条纪律在这里交汇：
· 求解器在**不可信侧**——产出候选，复核归 checker（§7.3）；
· 判定通道覆盖不到时必须**诚实未决**，绝不把「判不了」报成「不是原函数」。
"""

from cas.frontend.parser import parse
from cas.syntax.term import S, N
from cas.syntax import term as T
from cas.math.constraints import solve_linear_constraints, is_linear
from cas.math.integrate import verify_antideriv
from cas.runtime import new_workflow
from cas.workflow.command import Claim, Integrate


# --- 线性形式分析（句法，不靠化简器）---

def test_linear_form_decomposition_holds_for_transcendental_coeffs():
    u = S("_u")
    e = T.plus(T.plus(parse("exp(x)*sin(x)"), T.neg(u)), T.times(N(3), u))
    assert is_linear(e, (u,))
    assert not is_linear(T.times(u, u), (u,))
    assert not is_linear(T.pw(u, N(-1)), (u,))
    assert not is_linear(parse("sin(_u)"), (u,))


def test_coefficient_sign_kept_with_constant_factor():
    """`-1·v` 的系数必须是 −1（这条曾因 Times 分解漏乘常数部分而出错）。"""
    u, v = S("_u"), S("_v")
    res = solve_linear_constraints([T.eq(u, T.neg(v)), T.eq(u, N(2))], (u, v))
    assert res is not None
    val, complete = res
    assert complete
    assert val[u] is N(2)
    assert val[v] is N(-2)


def test_solver_honestly_refuses_nonlinear_and_inconsistent():
    u, X = S("_u"), S("x")
    assert solve_linear_constraints([T.eq(T.times(u, u), X)], (u,)) is None
    assert solve_linear_constraints([T.eq(u, N(1)), T.eq(u, N(2))], (u,)) is None


# --- 原函数判零：三值 ---

def test_antiderivative_verification_three_valued():
    X = S("x")
    # 证零：多项式
    assert verify_antideriv(parse("1/3*x^3"), parse("x^2"), X) is True
    # 证非零：真反驳
    assert verify_antideriv(parse("x^2"), parse("x^2"), X) is False
    # 未决：正确但判零通道（三角基归零）尚未重建 —— 必须是 None，不是 False
    assert verify_antideriv(parse("(exp(x)*(sin(x) - cos(x)))/2"),
                            parse("exp(x)*sin(x)"), X) is None


# --- §9.6 循环积分端到端 ---

def test_loop_integral_end_to_end_solved_but_verification_undecided():
    wf = new_workflow()
    u, v, X = S("_u"), S("_v"), S("x")
    a, b = parse("exp(x)*sin(x)"), parse("exp(x)*cos(x)")
    wf.add_constraint(T.eq(u, T.plus(a, T.neg(v))))          # u = a − v
    wf.add_constraint(T.eq(v, T.plus(T.plus(b, N(-1)), u)))  # v = b − 1 + u

    val, steps, complete = wf.solve_constraints((u, v))
    assert val is not None and complete, "循环方程应有唯一解"
    # 解就是 §9.5 的形式（D_x u = a），但判零通道覆盖不到 → 未决
    assert verify_antideriv(val[u], a, X) is None

    # 工作流里因此是 unverified，**绝不是 dead**（dead 等于伪造否证）
    s0 = wf.add(a, Claim())
    content = T.eq(T.mk(S("Integrate"), (T.mk_bound(X, a),)), val[u])
    s1 = wf.add(content, Integrate(pred=s0.id, var=X, antideriv=val[u]))
    assert s1.status == "undecided", (s1.status, s1.note)
    assert s1.judgment is None
