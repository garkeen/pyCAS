"""Frontend: text parsing, rendering and a session over one runtime.

The parser resolves names to stable ids and builds pure terms. The session binds
a workspace and lets a user store expressions, differentiate them, and move
through revisions. No frontend code decides mathematics or writes the ledger.
"""

from cas.frontend.errors import FrontendError, ParseError, SessionError
from cas.frontend.parser import parse
from cas.frontend.pprint import to_source, to_str
from cas.frontend.session import Session

__all__ = [
    "FrontendError",
    "ParseError",
    "Session",
    "SessionError",
    "parse",
    "to_source",
    "to_str",
]
