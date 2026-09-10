# -*- coding: utf-8 -*-
"""v4 §十二 不变量门禁（AGENTS.md「不变量落地要求」）。

可机械化者在此断言。尚未迁移到位的按 AGENTS.md「红灯先挂，等迁移到位
再翻绿」标记 xfail，并把差距写进 reason——CI 上看得见的光谱，而不是散在
文档里的主张。

本文件按迁移阶段分批点亮：

· 1  Term 无 guard/context/proof 字段      —— 绿（阶段1b）
· 2  Pattern 不是 Term                      —— 绿（阶段1b，模式元语言）
· 14 checker 不导入自身搜索算法            —— 绿（阶段3，规则实例验证）
· 16 未验证候选不参与可信推导              —— 绿（阶段2b，接入 commit）
· 18 自动化简不应用未证明的条件规则        —— 绿
"""

import inspect

import pytest

from cas.syntax import term as T
from cas.syntax import pattern as P


def _term_variants():
    out = []
    for obj in vars(T).values():
        if inspect.isclass(obj) and issubclass(obj, T.Term) and obj is not T.Term:
            out.append(obj)
    return out


def test_不变量1_项不带守卫与证明字段():
    """Term 只回答「长什么样」：不得携带 guard/context/proof/history 等字段。"""
    forbidden = {"guard", "guards", "context", "proof", "history", "domain",
                 "integration_constant", "substitution_variable", "ode_solution"}
    variants = _term_variants()
    assert variants, "未找到任何 Term 变体——变体收集逻辑失效"
    for cls in variants:
        slots = set(getattr(cls, "__slots__", ()))
        bad = slots & forbidden
        assert not bad, f"{cls.__name__} 携带了非法字段: {sorted(bad)}"


def test_不变量2_模式不是项():
    """PatternVar/PatternSeq/PatternCall 不在 Term 层次内（v4 §5.2）。"""
    for cls in (P.PatternVar, P.PatternSeq, P.PatternCall):
        assert not issubclass(cls, T.Term), f"{cls.__name__} 仍是 Term 子类"
    # 项层不得再暴露模式变量构造器
    assert not hasattr(T, "PatVar"), "term 层仍暴露 PatVar"
    assert not hasattr(T, "PatSeq"), "term 层仍暴露 PatSeq"
    assert not hasattr(T, "PV") and not hasattr(T, "PS"), "term 层仍暴露 PV/PS"
    # 变体清单里不得混入模式变量
    names = {c.__name__ for c in _term_variants()}
    assert not (names & {"PatVar", "PatSeq"}), f"项变体混入模式变量: {names}"


def test_不变量2_项内不可能出现模式变量():
    """模式通道产出 Pattern；普通通道拒绝 ?x，故洞进不了 Term。"""
    from cas.frontend.parser import parse
    from cas.errors import ParseError

    pat = parse("exp(?a)*exp(?b)", pattern=True)
    assert isinstance(pat, P.PatternCall)
    assert not isinstance(pat, T.Term)
    # 普通通道：?x 是模式记号，不是表达式
    with pytest.raises(ParseError):
        parse("exp(?a)")
    with pytest.raises(ParseError):
        parse("f(??xs)")


def test_不变量2_实例化产出项而非模式():
    """模板实例化必须落在 Term 层，且未绑定的洞显式报错（不泄漏）。"""
    from cas.frontend.parser import parse
    from cas.syntax.match import matches
    from cas.errors import ParseError

    tpl = parse("exp(?a + ?b)", pattern=True)
    tgt = parse("exp(x)*exp(y)")
    subs = list(matches(parse("exp(?a)*exp(?b)", pattern=True), tgt))
    assert subs, "规则模式未匹配到目标"
    inst = P.instantiate(tpl, subs[0])
    assert isinstance(inst, T.Term) and not isinstance(inst, P.Pattern)
    with pytest.raises(ParseError):
        P.instantiate(tpl, {"a": T.S("x")})   # ?b 未绑定：规则缺陷，显式报错


def test_不变量18_自动化简不应用未证明的条件规则():
    """auto 规则只许无条件；带守卫者一律非 auto（分支破裂改写不得静默落地）。"""
    from cas.math.rules import library_ruleset
    rs = library_ruleset()
    bad = [r.id for r in rs.rules.values() if r.auto and r.guard is not None]
    assert not bad, f"auto 规则携带守卫: {bad}"


def test_不变量14_checker不导入自身搜索算法():
    """checker 只验证给定实例，不得导入搜索器、不得遍历路径（v4 §7.3）。

    规则重写的主张由提出方给出实例（rule + path + substitution），checker
    复核该实例；「找在哪里应用哪条规则」是提出方的搜索，不进 checker。
    """
    from cas.workflow import checkers as C
    bad = []
    for name in dir(C):
        obj = getattr(C, name)
        if inspect.isclass(obj) and name.endswith("Checker"):
            names = obj.check.__code__.co_names
            for forbidden in ("apply_rule", "all_paths"):
                if forbidden in names:
                    bad.append(f"{name}.{forbidden}")
    assert not bad, f"checker 依赖了搜索算法: {bad}"


def test_规则实例checker只认给定实例():
    """替换/路径与实例不符 → 否决；相符 → 通过（不搜索其他路径或匹配）。"""
    from cas.frontend.parser import parse
    from cas.workflow.workflow import Workflow, Claim, Rewrite

    wf = Workflow()
    wf.add(parse("exp(x)*exp(y)"), Claim())
    X, Y = parse("x"), parse("y")
    good = wf.add(parse("exp(x + y)"),
                  Rewrite(pred=0, rule="exp_add", path=(),
                          substitution={"a": X, "b": Y}))
    assert good.status == "open", good.note
    assert good.judgment is not None
    # 替换不是该位置的有效匹配（?a、?b 都被绑到 x）→ 否决
    wrong = wf.add(parse("exp(x + y)"),
                   Rewrite(pred=0, rule="exp_add", path=(),
                           substitution={"a": X, "b": X}))
    assert wrong.status == "dead", wrong.note
    assert wrong.judgment is None
    # 路径越界 → 否决
    oob = wf.add(parse("exp(x + y)"),
                 Rewrite(pred=0, rule="exp_add", path=(5,),
                         substitution={"a": X, "b": Y}))
    assert oob.status == "dead", oob.note


def test_不变量16_未验证候选不参与可信推导():
    """checker 未决的候选不得以「可依赖」状态入账——unverified ≠ open。"""
    from cas.frontend.parser import parse
    from cas.syntax.term import S, N
    from cas.workflow.workflow import Workflow, Claim, Solve

    wf = Workflow()
    wf.add(parse("sin(x) == 1/2"), Claim())
    before = dict(wf.store.stats())
    # 回代判官在投影外诚实未决（超越函数），checker 返回 UnknownResult
    step = wf.add(parse("x == 1"), Solve(pred=0, var=S("x"), solution=N(1)))
    assert step.status == "unverified", \
        f"未决候选状态应为 unverified，实际 {step.status}"
    assert step.judgment is None, "未决候选不得持有可依赖结论"
    assert dict(wf.store.stats()) == before, "未决候选不得对账本产生任何写入"
