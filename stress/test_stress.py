# -*- coding: utf-8 -*-
"""The pytest collection layer for the stress benches.

The benches themselves are standalone scripts (fully self-proving, no external ground
truth; they exit non-zero on failure). This layer wraps each stress_*.py as one pytest
case so `pytest` works directly and CI can gate on it, while the bench scripts stay
unchanged and independently runnable.
"""

import subprocess
import sys
from pathlib import Path

import pytest

_DIR = Path(__file__).parent
_ROOT = _DIR.parent
_SCRIPTS = sorted(p for p in _DIR.glob("stress_*.py"))


@pytest.mark.parametrize("script", _SCRIPTS, ids=[p.stem for p in _SCRIPTS])
@pytest.mark.timeout(300)
def test_stress(script):
    r = subprocess.run(
        [sys.executable, str(script)], cwd=_ROOT,
        capture_output=True, text=True, timeout=280)
    assert r.returncode == 0, (
        f"{script.name} failed (exit code {r.returncode}):\n{r.stdout}\n{r.stderr}")
