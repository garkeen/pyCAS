# -*- coding: utf-8 -*-
"""stress 台架的 pytest 收集层。

台架本体是独立脚本（全部自证、无外部真值；失败 sys.exit 非零）。
本层把每个 stress_*.py 包成一条 pytest 用例，使 `pytest` 直接可用、
CI 可守门；台架脚本本身保持零改动、可独立运行。
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
        f"{script.name} 失败（退出码 {r.returncode}）:\n{r.stdout}\n{r.stderr}")
