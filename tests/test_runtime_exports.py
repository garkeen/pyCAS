# -*- coding: utf-8 -*-
"""运行期查询出口（职责：数学语义的唯一居所，且**必须显式装配**）。

钉子：常数此前在声明里带了 print_name 却没有查询出口，内核只能在
pprint / parser 各存一份硬编码表。补出口后内核不得再存副本。

阶段6 之后多了一条：语义来源必须是**显式 bootstrap**，不再是 import 副作用。
"""

from cas.runtime import dispatch


def test_const_by_name_returns_declaration():
    d = dispatch.const_by_name("gamma")
    assert d is not None
    assert d.print_name == "γ"
    assert d.real is True


def test_const_by_name_missing_returns_none():
    assert dispatch.const_by_name("__nope__") is None


def test_is_const_name_distinguishes_const_and_function():
    assert dispatch.is_const_name("pi") is True
    assert dispatch.is_const_name("e") is True
    assert dispatch.is_const_name("Sin") is False      # 函数头不是常数


def test_print_name_covers_constants_and_functions():
    assert dispatch.print_name("gamma") == "γ"
    assert dispatch.print_name("pi") == "π"
    assert dispatch.print_name("Sin") == "sin"          # 函数走同一出口
    assert dispatch.print_name("__nope__") is None


def test_const_literals_live_in_runtime_not_kernel():
    """内核不得再存名字→常数原子的副本表。"""
    import cas.frontend.parser as P
    assert not hasattr(P, "_CONSTS")                   # 旧硬编码表已废
    assert set(P._SYNTAX_ATOMS) == {"infinity", "true", "false"}


def test_domain_condition_single_registration_channel():
    import cas.math.domcond as DC
    assert not hasattr(DC, "DOM_HOOKS")                # 空壳通道已废


def test_importing_math_has_no_registration_side_effect():
    """v4 §7.1：禁止 import 期修改全局状态。

    在干净进程里只 import 数学模块：常数表、函数表、域阶梯、判等阶段都须为空。
    """
    import subprocess
    import sys
    code = ("import cas.math.decide, cas.math.diff, cas.math.domcond, "
            "cas.math.rules, cas.math.project; "
            "from cas.math.decide import _EQ_STAGES; "
            "from cas.math.domains.base import _DOMAINS; "
            "import cas.math.decide as D; "
            "print(len(_EQ_STAGES), len(_DOMAINS), D._DECLS is None)")
    r = subprocess.run([sys.executable, "-c", code], capture_output=True,
                       text=True, cwd=".")
    assert r.returncode == 0, r.stderr
    assert r.stdout.strip() == "0 0 True", r.stdout


def test_semantics_complete_after_bootstrap():
    rt = dispatch.get_runtime()
    s = rt.stats()
    assert s["constants"] == 4 and s["functions"] == 11
    assert s["domain_conds"] == 2 and s["eq_stages"] == 1 and s["domains"] == 3
