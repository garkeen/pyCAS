"""Frontend errors: surface failures are reported, never swallowed."""

from __future__ import annotations


class FrontendError(Exception):
    """Base class for errors a frontend can report to the user."""


class ParseError(FrontendError):
    """Surface text cannot be decoded into a term."""

    def __init__(self, message: str, position: int, text: str) -> None:
        super().__init__(message)
        self.message = message
        self.position = position
        self.text = text

    def __str__(self) -> str:
        return f"{self.message} at column {self.position + 1}"


class SessionError(FrontendError):
    """A session command cannot be carried out as asked."""
