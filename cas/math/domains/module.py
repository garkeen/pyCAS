"""Assembly of the resident domain declarations."""

from typing import Protocol

from cas.math.domains.base import Domain
from cas.syntax.term import Const


class ConstantRecord(Protocol):
    @property
    def atom(self) -> Const:
        """Return the declared constant atom."""
        ...


class DomainBuilder(Protocol):
    """Narrow assembly interface owned by the domains package."""

    def require_constant(self, name: str) -> ConstantRecord:
        """Return a previously declared constant record."""
        ...

    def register_domain(self, domain: Domain) -> None:
        """Register one resident domain."""
        ...


def install(builder: DomainBuilder) -> None:
    from cas.math.domains.q import Q_DOMAIN
    from cas.math.domains.qi import QIDomain
    from cas.math.domains.z import Z_DOMAIN

    i_atom = builder.require_constant("i").atom
    builder.register_domain(Z_DOMAIN)
    builder.register_domain(Q_DOMAIN)
    builder.register_domain(QIDomain(i_atom))
