# -*- coding: utf-8 -*-
"""Assembly of the domain modules.

The resident base fields (Z / Q / Q(i)) are registered into the projection ladder
here. This used to happen at **import time** inside `cas/math/project.py` (a
module-level `_install_base_domains()` call, then lookup to backfill singletons);
it is now an `install(builder)` step.

**Q(i) receives the identity of `i` through the builder**: the domain package
depends only on `cas.syntax.term` and cannot see constant declarations, so the
builder supplies the declared `i`. That keeps "domains enter by explicit
declaration, never by name sniffing" true, and makes the assembly order (constants
before domains) an explicit dependency rather than a hidden import order.
"""


def install(builder) -> None:
    from cas.math.domains.z import Z_DOMAIN
    from cas.math.domains.q import Q_DOMAIN
    from cas.math.domains.qi import QIDomain

    i_atom = builder.require_constant("i").atom
    builder.register_domain(Z_DOMAIN)
    builder.register_domain(Q_DOMAIN)
    builder.register_domain(QIDomain(i_atom))
