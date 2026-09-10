# -*- coding: utf-8 -*-
"""印名：展示形吃图书馆声明，源码形必须可重解析。

钉子：
1. Sym 曾被 _SYM_REPR 重映射——用户符号叫 pi 会被印成 π。
2. src=True 被文档承诺为"可解析源码形式"，却输出词法不认的 π/γ，
   往返断裂（pi 在改动前就已断裂）。
"""

from cas.syntax import term as T
from cas.frontend.parser import parse
from cas.frontend.pprint import to_str


def test_sym_not_remapped():
    assert to_str(T.S("pi")) == "pi"
    assert to_str(T.S("gamma")) == "gamma"


def test_const_uses_declared_print_name():
    assert to_str(parse("pi")) == "π"
    assert to_str(parse("gamma")) == "γ"


def test_display_form_separate_from_source_form():
    for src, disp, code in [("pi", "π", "pi"), ("gamma", "γ", "gamma")]:
        t = parse(src)
        assert to_str(t) == disp                    # 展示：图书馆印名
        assert to_str(t, src=True) == code          # 源码：内部名


def test_source_form_round_trips():
    """src=True 的承诺：输出能被词法接受并回到同一个驻留项。"""
    for s in ["pi", "gamma", "pi + gamma", "2*pi*x", "gamma^2",
              "e^(i*pi)", "sin(x) + pi"]:
        t = parse(s)
        assert parse(to_str(t, src=True)) is t, f"往返断裂: {s}"


def test_syntax_atoms_not_from_declarations():
    """infinity/true/false 是语言记号，不是数学常数。"""
    assert to_str(parse("infinity")) == "Infinity"
    assert to_str(parse("true")) == "true"
    assert to_str(parse("false")) == "false"


def test_function_head_print_name_same_exit():
    assert to_str(parse("sin(x)")) == "sin(x)"
    assert to_str(parse("cos(x) + log(x)")) == "cos(x) + log(x)"


def test_sqrt_rewritten_to_power_by_parser():
    """已知偏离：parser.py 为 sqrt 硬编码了 u^(1/2) 改写（句法层特判），
    未走图书馆声明通道。此钉子固化现状，防止无人知晓地漂移。
    若将来把 Sqrt 收回图书馆声明，本测试须随之改写。"""
    t = parse("sqrt(x)")
    assert t.head.name == "Power"
    assert to_str(t) == "x^(1/2)"
