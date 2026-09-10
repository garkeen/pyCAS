# -*- coding: utf-8 -*-
"""作用域契约（v4 §6.2 声明/定义 + 不变量 15 局部符号不得逃逸）。

接线前：`Scope` 的 `declarations`/`definitions` 字段、`ScopeStore.declarations`/
`definition_map`/`lookup_definition`、局部符号检查**全无生产者与消费者**——
定义的局部符号机制是半成品，`commit` 第 1 步只查「scope 存在」，逃逸检查没有
执行点（而 `commit` 的 docstring 却写着「检查 scope 与项的绑定合法性」）。
本文件钉住接通后的行为。
"""

import pytest

from cas.runtime import bootstrap, new_workflow
from cas.errors import ScopeError
from cas.syntax import term as T
from cas.syntax.term import S

bootstrap()

X = S("x")
U = S("u")


def _wf():
    return new_workflow()


def _child(wf):
    """建一个子作用域并进入。"""
    parent = wf.store.scopes.get(wf.scope)
    c = wf.store.scopes.child(parent)
    wf.enter(c.id)
    return c.id


# ---------------------------------------------------------------------------
# 声明 / 定义：生产者
# ---------------------------------------------------------------------------

def test_definition_visible_on_scope_chain():
    wf = _wf()
    root = wf.scope
    body = T.times(X, X)
    wf.define(U, body)
    assert wf.store.scopes.lookup_definition(root, U) is body
    assert wf.store.scopes.definition_map(root)[U] is body


def test_declaration_enters_scope_entries():
    wf = _wf()
    root = wf.scope
    wf.declare(U, S("Real"))
    decls = wf.store.scopes.declarations(root)
    assert len(decls) == 1 and decls[0].symbol is U


def test_defined_symbol_not_flagged_as_escape():
    """定义的局部符号在其作用域内使用是合法的（不是逃逸）。"""
    wf = _wf()
    wf.define(U, T.times(X, X))
    s = wf.add(T.eq(U, T.times(X, X)), _claim())
    assert s.status == "committed", s.note


def test_descendant_sees_ancestor_definition():
    """符号被祖先引入，故对后代可见——链上有即不算逃逸。"""
    wf = _wf()
    wf.define(U, T.times(X, X))
    _child(wf)
    s = wf.add(T.eq(U, T.times(X, X)), _claim())
    assert s.status == "committed", s.note


# ---------------------------------------------------------------------------
# §6.2 的四项检查
# ---------------------------------------------------------------------------

def test_stale_symbol_rejected_redefinition():
    wf = _wf()
    wf.define(U, T.times(X, X))
    with pytest.raises(ScopeError):
        wf.define(U, X)


def test_stale_symbol_rejected_redeclaration():
    wf = _wf()
    wf.declare(U, S("Real"))
    with pytest.raises(ScopeError):
        wf.declare(U, S("Integer"))


def test_stale_symbol_rejected_declare_then_define():
    wf = _wf()
    wf.declare(U, S("Real"))
    with pytest.raises(ScopeError):
        wf.define(U, X)


def test_recursive_definition_rejected():
    wf = _wf()
    with pytest.raises(ScopeError):
        wf.define(U, T.plus(U, X))


def test_definition_body_may_not_use_scope_locals():
    """v4 §6.2：右侧须在父作用域良好绑定——本作用域刚引入的别名还不算绑定。"""
    wf = _wf()
    wf.define(U, T.times(X, X))
    with pytest.raises(ScopeError):
        wf.define(S("v"), T.plus(U, X))


# ---------------------------------------------------------------------------
# 不变量 15：局部符号不得逃逸到作用域之外的结论
# ---------------------------------------------------------------------------

def test_local_symbol_must_not_escape_to_parent():
    wf = _wf()
    root = wf.scope
    _child(wf)
    wf.define(U, T.times(X, X))
    # 本作用域内合法
    assert wf.add(T.eq(U, T.times(X, X)), _claim()).status == "committed"
    # 回到父作用域：u 在此不可见，结论不得含它
    wf.enter(root)
    s = wf.add(T.eq(U, T.times(X, X)), _claim())
    assert s.status == "refused"
    assert "逃逸" in s.note


def test_sibling_branches_do_not_share_locals():
    """两个分支各自定义同名局部符号，互不构成对方的可见引入。"""
    wf = _wf()
    root = wf.scope
    a = _child(wf)
    wf.define(U, T.times(X, X))
    wf.enter(root)
    b = _child(wf)
    # b 分支链上没有 u（a 的 u 不在 b 的链上）→ 在 b 里用 u 即逃逸
    s = wf.add(T.eq(U, T.times(X, X)), _claim())
    assert s.status == "refused" and "逃逸" in s.note
    assert a != b


def _claim():
    from cas.workflow.command import Claim
    return Claim()
