# -*- coding: utf-8 -*-
"""显式装配（v4 §7.1）。

`bootstrap()` 是**唯一**把数学语义装进运行期的入口：按依赖序调用各数学模块的
`install(builder)`，再把装配结果绑给需要预计算状态的消费方（project 的基域
阶梯、decide 的恒等判定阶段）。

这取代了三处 import 期全局状态修改：

    library/__init__.py 的 load_all()            声明在 import 时自动注册
    project.py 的 _install_base_domains()        基域在 import 时自动进阶梯
    decide.py 的 register_eq_stage(...)          判定阶段在 import 时自动追加

现在 import 任何 `cas.math.*` 都不产生注册副作用；不装配就用不到语义
（查无此名 → None），装配必须由应用显式发起。

装配顺序即依赖序：elementary 先声明常数（域层要用 `i` 的身份），domains 再建
基域，base 最后装判定阶段。
"""

from cas.runtime.registry import RuntimeBuilder
from cas.runtime.runtime import Runtime


def bootstrap() -> Runtime:
    """装配全部数学模块，返回只读运行期。幂等由调用方（dispatch 的缓存）保证。"""
    builder = RuntimeBuilder()

    # 顺序即依赖：常数声明 → 基域（注入 i 的身份）→ 判定阶段
    from cas.math.elementary import module as elementary
    elementary.install(builder)

    from cas.math.domains import module as domains
    domains.install(builder)

    from cas.math.base import module as base
    base.install(builder)

    rt = Runtime(builder)

    # 把装配结果显式交给需要预计算状态的消费方（不再由它们 import 期自注册）
    from cas.math import project
    project.bind_domains(rt.domains)

    from cas.math import decide
    decide.bind_eq_stages(rt.eq_stages)

    # 声明查询面注入 math 模块（math 不 import runtime，§四）
    from cas.math import diff, domcond, rules
    for m in (decide, diff, domcond, rules):
        m.bind_runtime(rt)

    return rt
