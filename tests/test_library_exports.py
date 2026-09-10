# -*- coding: utf-8 -*-
"""图书馆查询出口（职责：语义的唯一居所）。

钉子：常数此前在图书馆里声明了 print_name，却没有查询出口，内核只能
在 pprint / parser 各存一份硬编码表。表补出口后，内核不得再存副本。
"""

import library


def test_const_by_name_返回声明():
    d = library.const_by_name("gamma")
    assert d is not None
    assert d.print_name == "γ"
    assert d.real is True


def test_const_by_name_查无返回None():
    assert library.const_by_name("__nope__") is None


def test_is_const_name_区分常数与函数头():
    assert library.is_const_name("pi") is True
    assert library.is_const_name("e") is True
    assert library.is_const_name("Sin") is False      # 函数头不是常数


def test_print_name_覆盖常数与函数两类():
    """print_name 此前只查 _FUNCS，常数的印名因此没有出口。"""
    assert library.print_name("gamma") == "γ"
    assert library.print_name("pi") == "π"
    assert library.print_name("Sin") == "sin"          # 函数走同一出口
    assert library.print_name("__nope__") is None


def test_常数字面量在图书馆而非内核():
    """内核不得再存名字→常数原子的副本表。"""
    import cas.frontend.parser as P
    assert not hasattr(P, "_CONSTS")                   # 旧硬编码表已废
    assert set(P._SYNTAX_ATOMS) == {"infinity", "true", "false"}


def test_定义域条件只有图书馆一个注册通道():
    import cas.math.domcond as DC
    assert not hasattr(DC, "DOM_HOOKS")                # 空壳通道已废
