# -*- coding: utf-8 -*-
"""Test-session assembly and test classification.

Bootstrap runs once at session start (mathematical semantics are not an import
side effect). Tests are classified by directory -- unit / contract / integration
/ regression / random -- and the marker is assigned from the path here, so no
per-file boilerplate is needed and the kind stays queryable: `pytest -m
regression` runs only the nailed-bug nails, `pytest -m contract` runs only the
architecture gates, `pytest -m random` runs the randomized benches, and so on.
The directory is the source of truth; the marker mirrors it.
"""

import pytest

from cas.runtime import bootstrap
from cas.runtime.dispatch import install

install(bootstrap())

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
        for d, mark in _KIND_BY_DIR.items():
            if d in parts:
                item.add_marker(getattr(pytest.mark, mark))
                break
