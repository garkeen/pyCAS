# -*- coding: utf-8 -*-
"""v4 §十二 不变量门禁（AGENTS.md「不变量落地要求」）。

可机械化者在此断言。尚未迁移到位的按 AGENTS.md「红灯先挂，等迁移到位
再翻绿」标记 xfail，并把差距写进 reason——CI 上看得见的光谱，而不是散在
文档里的主张。

本文件按迁移阶段分批点亮：

· 1  Term 无 guard/context/proof 字段      —— 绿（阶段1b）
· 2  Pattern 不是 Term                      —— 绿（阶段1b，模式元语言）
· 14 checker 不导入自身搜索算法            —— 绿（阶段3/6，checker 住 math/*）
· 16 未验证候选不参与可信推导              —— 绿（阶段2b，接入 commit）
· 18 自动化简不应用未证明的条件规则        —— 绿
"""

import inspect
from pathlib import Path

import pytest

from cas.runtime import new_workflow
from cas.syntax import term as T
from cas.syntax import pattern as P

_ROOT = Path(__file__).resolve().parents[1]


# ---------------------------------------------------------------------------
# v4 §四：依赖方向。指针与 import 都只许指向下方层。
# ---------------------------------------------------------------------------

def _cas_imports(path):
    """静态收集文件里出现的 cas.* / library 模块名（含函数内导入）。"""
    import ast
    tree = ast.parse(path.read_text(encoding="utf-8"))
    found = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.ImportFrom) and node.module:
            if node.module.startswith(("cas.", "library")):
                found.add(node.module)
        elif isinstance(node, ast.Import):
            for a in node.names:
                if a.name.startswith(("cas.", "library")):
                    found.add(a.name)
    return found


def _pkg_modules(*parts):
    return sorted((_ROOT / "cas").joinpath(*parts).glob("*.py"))


def test_依赖方向_syntax不依赖上层():
    """syntax 只许依赖标准库与 cas.errors（基础设施）。"""
    bad = []
    for p in _pkg_modules("syntax"):
        for m in _cas_imports(p):
            if not m.startswith("cas.syntax") and m != "cas.errors":
                bad.append(f"cas/syntax/{p.name} → {m}")
    assert not bad, "syntax 依赖了上层:\n" + "\n".join(bad)


def test_依赖方向_kernel不依赖数学与工作流():
    """kernel 只许依赖 syntax；不得依赖 math / workflow / frontend / library。"""
    bad = []
    for p in _pkg_modules("kernel"):
        for m in _cas_imports(p):
            if m.startswith(("cas.math", "cas.workflow", "cas.frontend", "library")):
                bad.append(f"cas/kernel/{p.name} → {m}")
    assert not bad, "kernel 依赖了上层:\n" + "\n".join(bad)


def test_依赖方向_math不依赖runtime():
    """§四：依赖方向是 runtime → math（bootstrap 拉全部数学模块），反向禁止。

    所以 math 模块读声明必须由装配期**注入**（bind_runtime），不能自己 import
    runtime——否则又会绕回 import 链条。
    """
    bad = []
    for p in sorted((_ROOT / "cas" / "math").rglob("*.py")):
        for m in _cas_imports(p):
            if m.startswith("cas.runtime"):
                bad.append(f"{p.relative_to(_ROOT)} → {m}")
    assert not bad, "math 依赖了 runtime: " + ", ".join(bad)


def test_依赖方向_workflow不依赖具体数学模块():
    """§四：workflow 只依赖 syntax + kernel。

    阶段6 起 checker 住在 `math/*/checkers.py`，workflow 不再持有验证逻辑——
    本门禁因此转绿（原为 v3 遗留债务）。
    """
    bad = [f"cas/workflow/{p.name} → {m}"
           for p in _pkg_modules("workflow")
           for m in _cas_imports(p) if m.startswith("cas.math")]
    assert not bad, "workflow 依赖具体数学模块:\n" + "\n".join(bad)


def test_引用方向_内核不认识工作流概念():
    """§四：内核侧不得出现 Artifact/Task/Event 这类工作流概念的名字。

    用 AST 收名字（不是字符串匹配），所以注释与文档里说明方向不受影响；
    同时钉住「靠 object 字段或鸭子类型绕过」：内核连这些名字都不许有。
    """
    import ast
    forbidden = {"ArtifactId", "TaskId", "EventId", "RevisionId",
                 "Artifact", "Task", "TaskCandidate", "Constraint",
                 "Event", "Revision", "BranchGroup", "BranchCase", "Focus"}
    bad = []
    for p in _pkg_modules("kernel"):
        tree = ast.parse(p.read_text(encoding="utf-8"))
        for node in ast.walk(tree):
            if isinstance(node, ast.Name) and node.id in forbidden:
                bad.append(f"cas/kernel/{p.name}:{node.lineno} {node.id}")
            elif isinstance(node, ast.Attribute) and node.attr in forbidden:
                bad.append(f"cas/kernel/{p.name}:{node.lineno} .{node.attr}")
            elif isinstance(node, (ast.ClassDef, ast.FunctionDef)) \
                    and node.name in forbidden:
                bad.append(f"cas/kernel/{p.name}:{node.lineno} def {node.name}")
    assert not bad, "内核出现工作流概念:\n" + "\n".join(bad)


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
    from cas.math.rules import declared_ruleset
    rs = declared_ruleset()
    bad = [r.id for r in rs.rules.values() if r.auto and r.guard is not None]
    assert not bad, f"auto 规则携带守卫: {bad}"


def test_不变量14_checker不导入自身搜索算法():
    """checker 只验证给定实例，不得导入搜索器、不得遍历路径（v4 §7.3）。

    规则重写的主张由提出方给出实例（rule + path + substitution），checker
    复核该实例；「找在哪里应用哪条规则」是提出方的搜索，不进 checker。
    """
    import importlib
    mods = ("cas.math.base.checkers",
            "cas.math.calculus.differentiation.checkers",
            "cas.math.calculus.integration.checkers",
            "cas.math.solving.equations.checkers",
            "cas.kernel.services")
    bad = []
    for mod in mods:
        m = importlib.import_module(mod)
        for name in dir(m):
            obj = getattr(m, name)
            if inspect.isclass(obj) and name.endswith("Checker"):
                names = obj.check.__code__.co_names
                for forbidden in ("apply_rule", "all_paths"):
                    if forbidden in names:
                        bad.append(f"{mod}.{name}.{forbidden}")
    assert not bad, f"checker 依赖了搜索算法: {bad}"


def test_规则实例checker只认给定实例():
    """替换/路径与实例不符 → 否决；相符 → 通过（不搜索其他路径或匹配）。"""
    from cas.frontend.parser import parse
    from cas.workflow.command import Claim, Rewrite

    wf = new_workflow()
    wf.add(parse("exp(x)*exp(y)"), Claim())
    X, Y = parse("x"), parse("y")
    good = wf.add(parse("exp(x + y)"),
                  Rewrite(pred=0, rule="exp_add", path=(),
                          substitution={"a": X, "b": Y}))
    assert good.status == "committed", good.note
    assert good.judgment is not None
    # 替换不是该位置的有效匹配（?a、?b 都被绑到 x）→ 否决
    wrong = wf.add(parse("exp(x + y)"),
                   Rewrite(pred=0, rule="exp_add", path=(),
                           substitution={"a": X, "b": X}))
    assert wrong.status == "refused", wrong.note
    assert wrong.judgment is None
    # 路径越界 → 否决
    oob = wf.add(parse("exp(x + y)"),
                 Rewrite(pred=0, rule="exp_add", path=(5,),
                         substitution={"a": X, "b": Y}))
    assert oob.status == "refused", oob.note


def test_不变量16_未验证候选不参与可信推导():
    """checker 未决的候选不得以「可依赖」状态入账——unverified ≠ open。"""
    from cas.frontend.parser import parse
    from cas.syntax.term import S, N
    from cas.workflow.command import Claim, Solve

    wf = new_workflow()
    wf.add(parse("sin(x) == 1/2"), Claim())
    before = dict(wf.store.stats())
    # 回代判官在投影外诚实未决（超越函数），checker 返回 UnknownResult
    step = wf.add(parse("x == 1"), Solve(pred=0, var=S("x"), solution=N(1)))
    assert step.status == "undecided", \
        f"未决候选状态应为 unverified，实际 {step.status}"
    assert step.judgment is None, "未决候选不得持有可依赖结论"
    assert dict(wf.store.stats()) == before, "未决候选不得对账本产生任何写入"


# ---------------------------------------------------------------------------
# 阶段5：持久化 Scope 树接管可变 Context
# ---------------------------------------------------------------------------

def test_阶段5_旧可变上下文已删除():
    """v3 的 Context（可变 entries + marks/rollback）不得复活。"""
    from cas.kernel import context as C
    for name in ("Context", "Entry", "Branch"):
        assert not hasattr(C, name), f"旧可变上下文残留: {name}"
    assert hasattr(C, "TrackedContext"), "checker 读通道丢失"


def test_假设集不可变且扩充产生新对象():
    """假设集是 Scope 的只读投影：`extended` 不就地写入，故无需克隆/撤销。"""
    from cas.kernel.scope import Assumptions, ScopeStore
    base = Assumptions()
    ext = base.extended(T.S("p"))
    assert base.items == () and ext.items == (T.S("p"),)
    assert base is not ext
    assert len(base) == 0 and list(ext) == [T.S("p")]

    # Scope 是权威来源：Assumptions.of 是它在判定层的投影
    from cas.kernel.model import Assumption
    st = ScopeStore()
    root = st.create()
    child = st.child(root, assumptions=(Assumption(T.S("q")),))
    assert Assumptions.of(st, child.id).items == (T.S("q"),)
    assert Assumptions.of(st, root.id).items == ()
