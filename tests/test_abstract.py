# -*- coding: utf-8 -*-
"""子项抽象验收（v4 §5.4）。

把 sin(x) 当代数未知量是循环积分/多项式化的前提：**相同子项必须落到同一符号**，
否则 `sin(x)^2 + sin(x)` 会变成 `_u0^2 + _u1`，多项式化失去意义。
"""

from cas.syntax import term as T
from cas.syntax.abstract import Abstraction, abstract_subterms, thaw
from cas.frontend.parser import parse
from cas.frontend.pprint import to_str


def _is_sin(u):
    return isinstance(u, T.Expr) and u.head.name == "Sin"


def _is_power(u):
    return isinstance(u, T.Expr) and u.head.name == "Power"


def test_same_subterm_shares_symbol():
    a = abstract_subterms(parse("sin(x)^2 + sin(x)"), _is_sin)
    assert len(a.replacements) == 1, [s.name for s, _ in a.replacements]
    sym = a.replacements[0][0]
    # 两处出现都是同一个符号：多项式化才成立
    assert to_str(a.term).count(sym.name) == 2


def test_abstraction_is_reversible():
    t = parse("sin(x)^2 + sin(x)")
    a = abstract_subterms(t, _is_sin)
    assert to_str(a.thaw()) == to_str(t)
    assert to_str(thaw(a.term, a.replacements)) == to_str(t)


def test_maximal_match_does_not_descend_into_matched():
    a = abstract_subterms(parse("x^2*y"), _is_power)
    assert len(a.replacements) == 1
    assert _is_power(a.replacements[0][1])
    assert to_str(a.replacements[0][1]) == to_str(parse("x^2"))


def test_fresh_symbol_avoids_existing_free_vars():
    a = abstract_subterms(parse("_u0 + sin(x)"), _is_sin)
    assert [s.name for s, _ in a.replacements] == ["_u1"]


def test_identity_when_no_match():
    t = parse("x + y")
    a = abstract_subterms(t, _is_sin)
    assert a.term is t
    assert a.replacements == ()


def test_no_abstraction_inside_binder():
    """de Bruijn 索引只在原绑定作用域内有效，把体内子项冻出绑定层会让 #i 逃逸。"""
    t = parse("integrate(sin(x), x)")
    a = abstract_subterms(t, _is_sin)
    assert a.term is t
    assert a.replacements == ()


def test_abstraction_result_participates_in_arithmetic():
    """抽象只是语法：产物是普通项，交给后续代数操作（如代入具体值）。"""
    a = abstract_subterms(parse("sin(x)^2 + sin(x)"), _is_sin)
    u = a.replacements[0][0]
    val = T.subst(a.term, {u: T.N(2)})
    assert isinstance(val, T.Term)
    assert not (T.free_vars(val) & {u}), "抽象符号未被代入替换"
    assert to_str(val) == to_str(parse("2^2 + 2"))


def test_abstraction_thaw_matches_environment():
    a = abstract_subterms(parse("cos(x)*cos(x)"), lambda u: isinstance(u, T.Expr)
                          and u.head.name == "Cos")
    assert isinstance(a, Abstraction)
    assert len(a.replacements) == 1
    assert to_str(a.thaw()) == to_str(parse("cos(x)*cos(x)"))
