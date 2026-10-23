"""Shared fixtures and directory-based classification for the v5 suite.

Every test gets a fresh runtime. The kernel ledger is append-only, so sharing one
assembled world across tests would leak judgments between them.
"""

import pytest

from cas.runtime.bootstrap import Runtime, bootstrap


@pytest.fixture
def runtime() -> Runtime:
    return bootstrap()


_KIND_BY_DIR = {
    "unit": "unit",
    "integration": "integration",
    "property": "property",
}


def pytest_collection_modifyitems(items):
    for item in items:
        parts = set(item.path.parts)
        for directory, mark in _KIND_BY_DIR.items():
            if directory in parts:
                item.add_marker(getattr(pytest.mark, mark))
                break
