# -*- coding: utf-8 -*-
"""规则引擎（全系统唯一重写引擎）。

规则来源只有图书馆声明（准入纪律见 library/api.py）；guard 判定走
判定管线（Verdict ADT），不存在第二套规则机制、第二套守卫词汇。

消费面：
· simplify.autosimplify —— auto 规则定点化简（自动通道）
· REPL apply 命令 —— 定向应用（交互通道）
两者共用 apply_rule，验证经 workflow Rewrite 步骤。
"""

from dataclasses import dataclass

from cas import term as T
from cas.match import matches
from cas.verdict import YES, NO, unknown


@dataclass(frozen=True)
class Rule:
    id: str
    pattern: T.Term
    template: T.Term
    guard: object = None
    auto: bool = False
    priority: int = 100           # 同位多规则时的尝试顺序（小者先，yacas 同款）


@dataclass
class ApplyResult:
    ok: bool
    guard: object                 # Verdict（YES 才可落）
    term: T.Term = None
    subst: dict = None
    rule_id: str = ""


def root_key(p):
    if isinstance(p, T.Expr):
        return p.head.name
    if isinstance(p, (T.PatVar, T.PatSeq)):
        return "*"
    return p.__class__.__name__ + ":" + repr(p)


class RuleSet:
    def __init__(self):
        self.rules = {}
        self.index = {}

    def add(self, rule):
        self.rules[rule.id] = rule
        self.index.setdefault(root_key(rule.pattern), []).append(rule)

    def remove(self, rid):
        r = self.rules.pop(rid, None)
        if r:
            lst = self.index.get(root_key(r.pattern), [])
            if r in lst:
                lst.remove(r)

    def for_term(self, t):
        seen = set()
        keys = ["*"]
        if isinstance(t, T.Expr):
            keys.append(t.head.name)
        else:
            keys.append(t.__class__.__name__ + ":" + repr(t))
        for k in keys:
            for r in sorted(self.index.get(k, ()), key=lambda r: r.priority):
                if r.id not in seen:
                    seen.add(r.id)
                    yield r

    def ids(self):
        return list(self.rules)


def apply_rule(rule, expr, path, guard_eval=None, budget=10000):
    """在 expr 的 path 处尝试应用规则。

    guard_eval: (guard_term, subst) -> Verdict。缺省（无守卫）视为 YES；
    有守卫但无评估器视为 UNKNOWN——诚实不落地。"""
    sub_t = T.term_at(expr, path)
    for sub in matches(rule.pattern, sub_t, budget=budget):
        if rule.guard is None:
            g = YES
        else:
            g = guard_eval(rule.guard, sub) if guard_eval else unknown()
        if g is YES:
            inst = T.instantiate(rule.template, sub)
            after = T.replace_at(expr, path, inst)
            return ApplyResult(True, YES, after, sub, rule.id)
        if g is NO:
            continue
        return ApplyResult(False, g, expr, sub, rule.id)
    return ApplyResult(False, None, expr, None, rule.id)


_LIB_RULESET = None


def library_ruleset() -> RuleSet:
    """从图书馆声明装配规则集（幂等缓存）。

    图书馆只持规则行字符串（纯数据），DSL 解析在本消费点完成——
    内核消费图书馆条目，图书馆不反向导入内核。损坏的规则行是图书馆
    声明缺陷：解析异常向上抛出，绝不静默吞掉。"""
    global _LIB_RULESET
    if _LIB_RULESET is None:
        import library
        from cas.loader import parse_rule_line
        rs = RuleSet()
        for decl in library.all_functions():
            for line in decl.rule_lines:
                rs.add(parse_rule_line(line))
        _LIB_RULESET = rs
    return _LIB_RULESET
