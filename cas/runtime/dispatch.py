# -*- coding: utf-8 -*-
"""运行期查询入口（v4 §三 `runtime/dispatch.py`）。

消费者（parser / pprint / decide / project / rules / domcond / diff …）经此读数学
语义——它取代旧的 `library` 包的查询面，语义相同、名字相同，但**语义来自显式
装配**而非 import 副作用。

首次调用触发一次 `bootstrap()`，此后只读。写入口只有 `RuntimeBuilder`。
"""

from cas.runtime.bootstrap import bootstrap

_runtime = None


def get_runtime():
    """取运行期（首次调用时装配）。"""
    global _runtime
    if _runtime is None:
        _runtime = bootstrap()
    return _runtime


def reset_runtime():
    """丢弃已装配的运行期（测试用；下次查询会重新装配）。"""
    global _runtime
    _runtime = None


# --- 常数 ---

def const_by_atom(atom):
    return get_runtime().const_by_atom(atom)


def const_by_name(name):
    return get_runtime().const_by_name(name)


def is_const_name(name):
    return get_runtime().is_const_name(name)


def const_positive(atom):
    return get_runtime().const_positive(atom)


def const_real(atom):
    return get_runtime().const_real(atom)


def const_bounds(atom):
    return get_runtime().const_bounds(atom)


# --- 函数 ---

def lookup_function(name):
    return get_runtime().lookup_function(name)


def function_deriv(name):
    return get_runtime().function_deriv(name)


def all_functions():
    return get_runtime().all_functions()


def print_name(head_name):
    return get_runtime().print_name(head_name)


# --- 定义域条件 ---

def lookup_domain_cond(name):
    return get_runtime().lookup_domain_cond(name)


# --- 计算转发（前端不得直连 math，§四）---

def domain_normal_form(t):
    """域标准形。前端（REPL 的 norm 命令）经此取用，不直接 import math。"""
    from cas.math.base.equality import normal_form
    return normal_form(t)


def new_workflow(**kw):
    """建工作流会话（账本 + checker + 判定服务由 runtime 装配）。"""
    from cas.runtime.runtime import new_workflow as _nw
    return _nw(**kw)
