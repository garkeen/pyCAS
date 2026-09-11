"""The number-field system: explicit declaration plus capability-dispatched
normalization and equality.

## Division of labour: this package declares, the projection layer assembles

This package is pure declaration: it defines domain and ring classes and
produces no import-time side effect, registering nothing itself. Registering a
domain into the ladder is the job of assembly, and the single assembly point is
the projection layer:

· the domain package depends only on cas.syntax.term, so it cannot reach the
  constant atoms declared in the declaration layer. The Gaussian rationals need the
  declared i injected, so assembly must happen where both the constant
  declarations and the domains are visible, namely bootstrap.
· were registration scattered across domain modules (registering on import), the
  registry content would depend on which module happened to be imported: adding
  a domain module that nobody imports would make it silently disappear from
  lookup. Centralized assembly removes that import-order sensitivity.

The registry holds resident base domains only (Z / Q / Q(i)). K[x] and K(x) are
instances parameterized by variable set, held in their own factory caches and
never registered.

Three-valued decisions belong to the decision layer; the domain layer's `equal`
returns bool or None.
"""

from cas.math.domains.base import (Ring, RingError, FracRing, Domain, register,
                              domain_scope, lookup)
from cas.math.domains import q
from cas.math.domains import z
from cas.math.domains import qi
from cas.math.domains import poly
from cas.math.domains import ratfunc

from cas.math.domains.q import Q_RING, QDomain, Q_DOMAIN
from cas.math.domains.z import Z_RING, ZDomain, Z_DOMAIN
from cas.math.domains.qi import QI_RING, QIDomain
from cas.math.domains.poly import poly_domain, PolyDomain
from cas.math.domains.ratfunc import ratfunc_domain, RatFuncDomain
