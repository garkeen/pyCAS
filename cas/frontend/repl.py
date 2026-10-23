"""A small line-oriented REPL over one session.

Every command line goes through `Session.execute`; the REPL only reads lines,
prints results and reports frontend errors. It never decides mathematics.
"""

from __future__ import annotations

from collections.abc import Callable, Iterable

from cas.frontend.errors import FrontendError
from cas.frontend.session import Session
from cas.runtime.bootstrap import bootstrap

_BANNER = "pyCAS v5 — polynomial differentiation. Type help for commands."


def run(
    session: Session,
    lines: Iterable[str],
    write: Callable[[str], None],
) -> None:
    """Execute lines until the session closes or the input ends."""
    for line in lines:
        try:
            output = session.execute(line)
        except FrontendError as error:
            write(f"error: {error}")
        else:
            if output:
                write(output)
        if session.closed:
            break


def main() -> None:
    session = Session(bootstrap())
    print(_BANNER)
    while not session.closed:
        try:
            line = input("cas> ")
        except (EOFError, KeyboardInterrupt):
            print()
            break
        run(session, (line,), print)


__all__ = ["main", "run"]
