"""Public declarations for the exact domain protocol and built-in domains."""

from cas.math.domains.base import (
    DEFAULT_CAPABILITIES,
    Domain,
    DomainCapabilities,
    DomainCatalog,
    DomainElement,
    FracRing,
    PolynomialView,
    Ring,
    RingError,
)
from cas.math.domains.poly import Poly, PolyDomain, poly_domain
from cas.math.domains.q import Q_DOMAIN, Q_RING, QDomain, QRing
from cas.math.domains.qi import QI_RING, QIDomain, QIRing
from cas.math.domains.ratfunc import RatFunc, RatFuncDomain, ratfunc_domain
from cas.math.domains.z import Z_DOMAIN, Z_RING, ZDomain, ZZRing

__all__ = (
    "DEFAULT_CAPABILITIES",
    "Domain",
    "DomainCapabilities",
    "DomainCatalog",
    "DomainElement",
    "FracRing",
    "PolynomialView",
    "Poly",
    "PolyDomain",
    "Q_DOMAIN",
    "Q_RING",
    "QDomain",
    "QI_RING",
    "QIDomain",
    "QIRing",
    "QRing",
    "RatFunc",
    "RatFuncDomain",
    "Ring",
    "RingError",
    "Z_DOMAIN",
    "Z_RING",
    "ZDomain",
    "ZZRing",
    "poly_domain",
    "ratfunc_domain",
)
