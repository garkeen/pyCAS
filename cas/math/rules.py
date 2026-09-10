# -*- coding: utf-8 -*-
"""规则引擎（全系统唯一重写引擎）。

规则来源只有运行期声明（由 bootstrap 装配，见 runtime/registry.py）；guard 判定走
判定管线（Verdict ADT），不存在第二套规则机制、第二套守卫词汇。

消费面：
· simplify.autosimplify —— auto 规则定点化简（自动通道）
· REPL apply 命令 —— 定向应用（交互通道）
两者共用 apply_rule，验证经 workflow Rewrite 步骤。
"""

from dataclasses import dataclass

from cas.syntax import term as T
from cas.syntax import pattern as P
from cas.syntax.match import matches
from cas.kernel.verdict import YES, NO, unknown

_DECLS = None


def bind_runtime(rt):
    """由 `bootstrap()` 注入声明查询面（v4 §四 依赖方向）。

    依赖方向是 **runtime → math**（bootstrap 拉全部数学模块），反向禁止：
    math 模块不得 import runtime。所以声明由装配期注入，而非模块自己去取。

    未注入时查询**报错**而不是返回 None——静默 None 会把「忘了装配」变成
    难查的错答案，而「查无此名」是另一种情况（那条仍返回 None 由调用方降级）。
    """
    global _DECLS
    _DECLS = rt


def _R():
    if _DECLS is None:
        raise RuntimeError(
            "未装配：先调用 cas.runtime.bootstrap()（v4 §7.1 禁止 import 期自注册）")
    return _DECLS



@dataclass(frozen=True)
class Rule:
    id: str
    pattern: object               # cas.syntax.pattern.Pattern（v4 不变量 2：模式非项）
    template: object              # Pattern；实例化产出 Term
    guard: object = None          # Pattern | None（条件也是模式，含洞）
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
    """规则索引键（模式层实现；洞归 '*'）。"""
    return P.root_key(p)


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
            inst = P.instantiate(rule.template, sub)
            after = T.replace_at(expr, path, inst)
            return ApplyResult(True, YES, after, sub, rule.id)
        if g is NO:
            continue
        return ApplyResult(False, g, expr, sub, rule.id)
    return ApplyResult(False, None, expr, None, rule.id)


_LIB_RULESET = None


def declared_ruleset() -> RuleSet:
    """从运行期声明装配规则集（幂等缓存）。

    声明只持规则行字符串（纯数据），DSL 解析在本消费点完成——数学模块不反向
    导入本模块。损坏的规则行是**声明缺陷**：解析异常向上抛出，绝不静默吞掉。"""
    global _LIB_RULESET
    if _LIB_RULESET is None:
        # 延迟导入：这是 cas.math.rules ↔ cas.math.loader 环的回边。loader 顶层
        # `from cas.math.rules import Rule`（去边），本处若要也提到顶层，两侧
        # 都会撞上半初始化模块。环的成因是规则行 DSL 的解析产物是 Rule，
        # 而装配点在本模块——解析与装配同居一处时此环即消失。
        from cas.math.loader import parse_rule_line
        rs = RuleSet()
        for decl in _R().all_functions():
            for line in decl.rule_lines:
                rs.add(parse_rule_line(line))
        _LIB_RULESET = rs
    return _LIB_RULESET
