"""Test fixtures and test classification."""

import pytest

from cas.frontend.repl import REPL
from cas.frontend.session import Session
from cas.runtime import Runtime, bootstrap


@pytest.fixture(scope="session")
def runtime() -> Runtime:
    return bootstrap()


@pytest.fixture
def session(runtime: Runtime) -> Session:
    return REPL(runtime).session


_KIND_BY_DIR = {
    "unit": "unit",
    "contract": "contract",
    "integration": "integration",
    "regression": "regression",
    "random": "random",
}


def pytest_collection_modifyitems(items):
    for item in items:
        parts = set(item.path.parts)
        for directory, mark in _KIND_BY_DIR.items():
            if directory in parts:
                item.add_marker(getattr(pytest.mark, mark))
                break
