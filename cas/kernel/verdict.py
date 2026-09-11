"""Verdict ADT: the language contract of the decision layer.

A verdict is an algebraic data type, not a string and not a bare enum:

· Yes carries evidence recording where the decision came from;
· No is a refutation;
· Unknown carries a reason, and the reason determines what happens next.

Reasons for Unknown:

· FRAGMENT    the fragment does not cover the input; extending the declarations
              or the algorithm can decide it;
· GUARDED     blocked by an unconfirmed condition; discharging the condition
              can flip the answer;
· UNDECIDABLE undecidable in principle, along the Richardson/Skolem boundary;
· BUDGET      the search budget ran out, an internal resource limit. This is a
              different conclusion from undecidability: a larger budget may
              flip it (not found is not the same as does not exist).

YES/NO are singletons and support `is` comparison; Unknown is interned per
reason via the `unknown()` factory. The hierarchy is closed: consumers must
exhaust the Yes/No/Unknown branches rather than compare strings.
"""

from enum import Enum


class Reason(Enum):
    FRAGMENT = "fragment"
    GUARDED = "guarded"
    UNDECIDABLE = "undecidable"
    BUDGET = "budget"


class Verdict:
    """Closed hierarchy of the three-valued verdict."""
    __slots__ = ()

    def is_yes(self):
        return self is YES

    def is_no(self):
        return self is NO

    def is_unknown(self):
        return isinstance(self, Unknown)


class Yes(Verdict):
    __slots__ = ("proof",)

    def __init__(self, proof=None):
        self.proof = proof

    def __repr__(self):
        return "YES" if self.proof is None else f"YES[{self.proof}]"


class No(Verdict):
    __slots__ = ()

    def __repr__(self):
        return "NO"


class Unknown(Verdict):
    __slots__ = ("reason",)

    def __init__(self, reason):
        self.reason = reason

    def __repr__(self):
        return f"UNKNOWN[{self.reason.value}]"


YES = Yes()
NO = No()
_UNKNOWN_CACHE = {}


def unknown(reason=Reason.FRAGMENT):
    u = _UNKNOWN_CACHE.get(reason)
    if u is None:
        u = Unknown(reason)
        _UNKNOWN_CACHE[reason] = u
    return u


# ---------------------------------------------------------------------------
# Propositional composition: the logic layer only needs three-valued connectives
# ---------------------------------------------------------------------------

def _first_unknown(*vs):
    for v in vs:
        if isinstance(v, Unknown):
            return v
    return unknown()


def and3(a, b):
    if a is NO or b is NO:
        return NO
    if a is YES and b is YES:
        return YES
    return _first_unknown(a, b)


def or3(a, b):
    if a is YES or b is YES:
        return YES
    if a is NO and b is NO:
        return NO
    return _first_unknown(a, b)


def not3(a):
    if a is YES:
        return NO
    if a is NO:
        return YES
    return a
