# -*- coding: utf-8 -*-
"""域模块的装配（v4 §7.2）。

常驻基域（ℤ / ℚ / ℚ(i)）在此登记进阶梯。原先这发生在 `cas/math/project.py`
的 **import 期**（模块级调用 `_install_base_domains()` 再 lookup 回填单例），
是 AGENTS.md §六 列的三处之一；现在改为 `install(builder)`。

**ℚ(i) 的 i 身份经 builder 注入**：域包只依赖 `cas.syntax.term`，拿不到常数
声明，所以由 builder 提供已声明的 `i`。这既保证「域由显式声明进入、不做名字
嗅探」，也让装配顺序（先常数、后域）成为显式依赖而非隐式 import 顺序。
"""


def install(builder) -> None:
    from cas.math.domains.z import Z_DOMAIN
    from cas.math.domains.q import Q_DOMAIN
    from cas.math.domains.qi import QIDomain

    i_atom = builder.require_constant("i").atom
    builder.register_domain(Z_DOMAIN)
    builder.register_domain(Q_DOMAIN)
    builder.register_domain(QIDomain(i_atom))
