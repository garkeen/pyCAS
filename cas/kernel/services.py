"""Kernel service interface.

The kernel does not import concrete mathematical modules. Decision and context
queries are injected through this interface, implemented by the runtime layer.

`NullServices` is the honest default: every decision returns Unknown. It lets
the kernel be constructed and tested without any mathematical module, and it
guarantees that "no decider is wired up" is never mistaken for "decided true".
"""

from typing import Protocol

from cas.kernel.evidence import Accepted, Rejected, UnknownResult
from cas.kernel.verdict import Reason, Verdict, unknown


class KernelServices(Protocol):
    """The capability surface visible to a checker and to commit."""

    def decide(self, proposition, scope_id) -> Verdict:
        """Decide a proposition in the given scope. Returns a Verdict, never a
        bare boolean."""
        ...


class NullServices:
    """Default services: decide nothing (Unknown / FRAGMENT)."""

    def decide(self, proposition, scope_id) -> Verdict:
        return unknown()

    def lookup_definition(self, scope_id, symbol):
        return None

    def assumptions(self, scope_id):
        return ()


class DecideChecker:
    """Wrap the injected decider as a checker: a kernel-provided verifier that
    decides no mathematics itself, it only forwards.

    With it, condition discharge can run on the same commit protocol even
    without concrete mathematical modules: only a Yes is accepted, and it
    accepts no direct conditions, which keeps it recursion-safe.
    """

    def check(self, proposal, context, services):
        if len(proposal.conclusions) != 1:
            return Rejected(Reason.FRAGMENT, "decide checker handles one conclusion only")
        v = services.decide(proposal.conclusions[0], proposal.scope)
        if v.is_yes():
            return Accepted(reads=context.read_set())
        if v.is_no():
            return Rejected(Reason.GUARDED, "decided false")
        return UnknownResult(v.reason, "decision undecided")


def register_core_checkers(store) -> None:
    """Install the kernel-provided checker. Called explicitly; import never
    mutates global state. A duplicate raises, matching the builder's policy: a
    checker-id collision is a decision that must surface, not one to resolve
    silently by registration order."""
    store.checkers.register("kernel.decide", DecideChecker())
