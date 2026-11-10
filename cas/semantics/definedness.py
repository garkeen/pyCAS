"""Definedness records for one typed source expression.

A `Definedness` value states the source's intrinsic domain and the region on
which a chosen representation equals the source.  It is a view over the
propositions carried by `AlgebraView.source_domain`/`valid_on`; it does not
create a second domain authority.

`DefinednessExactness` distinguishes the cases the bridge can establish:

- `TOTAL`: the bridge is total on its accepted fragment; both regions are None.
- `EXACT`: `domain` is the source's exact intrinsic domain.  The bridge's
  `ConversionWitness` is the exactness evidence for this fragment; no separate
  region certificate is needed.  `valid_on` is None or the same region.
- `SUFFICIENT`: the representation is only proved on a working region.  It
  supports `EqualOn` claims, not `SamePartialFunction`.  There are two forms:
  the source has a nontrivial intrinsic `domain` and `valid_on` is a strict
  subregion proved by a `SubregionCertificate`; or the source is total
  (`domain` is None) while the representation is valid only on `valid_on`, in
  which case the bridge's `ConversionWitness` is the evidence and no region
  certificate is needed.

Any view that carries a region records a `ConversionWitness` that preserves
definedness; a witness that does not preserve definedness cannot support a
source-domain or representation-region claim, so it is only admissible on a
total view with no region claim.

The region coordinates must contain every free symbol of the source; a region
may be stated over a larger coordinate space and keeps its own order.  The
distinction between an exact intrinsic domain and a merely sufficient working
region follows `cas_v5_arch.md` §10.1, §10.3 and §32.4.

The record is sealed: only `AlgebraView.definedness` issues it through
`_issue_definedness`.  The seal is the evidence boundary.  The bridge's
`ConversionWitness` is the evidence for `EXACT` and for the total-source
`SUFFICIENT` case; a nontrivial-domain `SUFFICIENT` record carries the
`SubregionCertificate` produced by the same restricted region logic.
`dataclasses.replace` cannot forge a record because the replacement is built
through `__init__` without the module seal.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import StrEnum

from cas.language.typing import TypedExpr
from cas.semantics.regions import (
    RegionCertificate,
    RegionSpec,
    SubregionCertificate,
)

_SEAL = object()
_DEFINEDNESS_FIELDS = frozenset(
    {"source", "domain", "valid_on", "exactness", "certificate"}
)


def _require_definedness_seal(value: object) -> None:
    """Refuse a definedness record whose factory did not set the module seal."""
    try:
        seal = object.__getattribute__(value, "_seal")
    except AttributeError:
        seal = None
    if seal is not _SEAL:
        raise ValueError(
            "a definedness record is issued only by "
            "AlgebraView.definedness"
        )


class DefinednessExactness(StrEnum):
    """How much the recorded domain and validity region are claimed to be."""

    TOTAL = "total"
    EXACT = "exact"
    SUFFICIENT = "sufficient"


@dataclass(frozen=True, slots=True)
class Definedness:
    """The intrinsic domain and representation region of one source.

    The record is built from `AlgebraView.source_domain`/`valid_on`; the bridge
    remains the only region authority.  `certificate` is present exactly when
    a nontrivial domain has a strict, proved subregion.  A total source may
    still have a partial representation region: then `domain` is None and the
    bridge's `ConversionWitness` is the evidence for the sufficient region.

    Construction requires the module seal; use `_issue_definedness`, which is
    called only by `AlgebraView.definedness`.  `dataclasses.replace` cannot
    reproduce the record because the replacement is built through `__init__`
    without the seal and is refused by `__post_init__`.
    """

    source: TypedExpr
    domain: RegionSpec | None
    valid_on: RegionSpec | None
    exactness: DefinednessExactness
    certificate: RegionCertificate | None = None
    _seal: object | None = field(
        init=False, default=None, repr=False, compare=False
    )

    def __post_init__(self) -> None:
        if self._seal is not _SEAL:
            raise ValueError(
                "a definedness record is issued only by "
                "AlgebraView.definedness"
            )
        if not isinstance(self.source, TypedExpr):
            raise TypeError("definedness needs a typed source")
        if self.domain is not None and not isinstance(
            self.domain, RegionSpec
        ):
            raise TypeError(
                "definedness domain must be a region or None"
            )
        if self.valid_on is not None and not isinstance(
            self.valid_on, RegionSpec
        ):
            raise TypeError(
                "definedness validity region must be a region or None"
            )
        if not isinstance(self.exactness, DefinednessExactness):
            raise TypeError(
                "definedness exactness must be a DefinednessExactness"
            )
        source_coordinates = {
            item.symbol_id for item in self.source.bindings.symbols
        }
        for name, region in (
            ("domain", self.domain),
            ("valid_on", self.valid_on),
        ):
            if region is not None:
                missing = source_coordinates - set(region.coordinates)
                if missing:
                    rendered = ", ".join(
                        str(item) for item in sorted(missing)
                    )
                    raise ValueError(
                        f"definedness {name} coordinates must contain every "
                        f"source free symbol; missing: {rendered}"
                    )

        if self.exactness is DefinednessExactness.TOTAL:
            if self.domain is not None or self.valid_on is not None:
                raise ValueError(
                    "a total definedness cannot carry a region"
                )
            if self.certificate is not None:
                raise ValueError(
                    "a total definedness cannot carry a region certificate"
                )
        elif self.exactness is DefinednessExactness.EXACT:
            if self.domain is None:
                raise ValueError("an exact definedness needs a domain")
            if (
                self.valid_on is not None
                and self.valid_on != self.domain
            ):
                raise ValueError(
                    "an exact definedness validity region must be the domain"
                )
            if self.certificate is not None:
                raise ValueError(
                    "an exact definedness carries no separate certificate"
                )
        elif self.exactness is DefinednessExactness.SUFFICIENT:
            if self.valid_on is None:
                raise ValueError(
                    "a sufficient definedness needs a validity region"
                )
            if self.domain is None:
                if self.certificate is not None:
                    raise ValueError(
                        "a sufficient definedness over a total source carries "
                        "no region certificate; the conversion witness is the "
                        "evidence"
                    )
            else:
                if self.valid_on == self.domain:
                    raise ValueError(
                        "a sufficient definedness needs a strict subregion"
                    )
                if not isinstance(self.certificate, SubregionCertificate):
                    raise ValueError(
                        "a sufficient definedness needs a subregion "
                        "certificate"
                    )
                if (
                    self.certificate.subregion != self.valid_on
                    or self.certificate.region != self.domain
                ):
                    raise ValueError(
                        "the subregion certificate does not match the regions"
                    )
        else:
            raise ValueError("unknown definedness exactness")

    def __getattribute__(self, name: str) -> object:
        if name in _DEFINEDNESS_FIELDS:
            _require_definedness_seal(self)
        return object.__getattribute__(self, name)


def _issue_definedness(
    source: TypedExpr,
    domain: RegionSpec | None,
    valid_on: RegionSpec | None,
    exactness: DefinednessExactness,
    certificate: RegionCertificate | None = None,
) -> Definedness:
    """Construct one definedness record after setting the module seal."""
    value = object.__new__(Definedness)
    object.__setattr__(value, "source", source)
    object.__setattr__(value, "domain", domain)
    object.__setattr__(value, "valid_on", valid_on)
    object.__setattr__(value, "exactness", exactness)
    object.__setattr__(value, "certificate", certificate)
    object.__setattr__(value, "_seal", _SEAL)
    value.__post_init__()
    return value


__all__ = ["Definedness", "DefinednessExactness"]
