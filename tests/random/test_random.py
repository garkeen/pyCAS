# -*- coding: utf-8 -*-
"""The pytest collection layer for the randomized property benches.

Each bench is a standalone script (fully self-proving, no external ground
truth; it exits non-zero on failure). This layer wraps each random_*.py as one
pytest case so `pytest` works directly and CI can gate on it, while the bench
scripts stay unchanged and independently runnable.
"""

import subprocess
import sys
from pathlib import Path

import pytest

_DIR = Path(__file__).parent
# The benches run with the repo root as cwd so their `cas.*` imports resolve;
# _DIR is tests/random/, so the root is two levels up.
_ROOT = _DIR.parent.parent
_SCRIPTS = sorted(p for p in _DIR.glob("random_*.py"))


@pytest.mark.parametrize("script", _SCRIPTS, ids=[p.stem for p in _SCRIPTS])
@pytest.mark.timeout(300)
def test_random_bench(script):
    r = subprocess.run(
        [sys.executable, str(script)], cwd=_ROOT,
        capture_output=True, text=True, timeout=280)
    assert r.returncode == 0, (
        f"{script.name} failed (exit code {r.returncode}):\n{r.stdout}\n{r.stderr}")
