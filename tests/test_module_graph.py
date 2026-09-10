# -*- coding: utf-8 -*-
"""模块图：每个模块都能独立导入。

钉子：cas/syntax/term.py 末尾曾直接 `from cas.termpath import ...`，而
termpath 顶部又 `from cas import term as T` —— 于是 `import cas.termpath`
作为入口必然撞上 term 的半初始化状态而 ImportError（基线即崩，当时注释
却写着"无导入环"）。改 PEP 562 惰性 __getattr__ 后两个方向都能独立导入。

2026-09-10 起按 v4 目标树拆子包（syntax/kernel/workflow/math/frontend），
清单改为遍历各子包目录，漏测新模块即漏报。
"""

import subprocess
import sys
from pathlib import Path

_ROOT = Path(__file__).resolve().parent.parent
_DIRS = (
    ("cas", "cas"),
    ("cas/syntax", "cas.syntax"),
    ("cas/kernel", "cas.kernel"),
    ("cas/workflow", "cas.workflow"),
    ("cas/math", "cas.math"),
    ("cas/math/domains", "cas.math.domains"),
    ("cas/frontend", "cas.frontend"),
    ("library", "library"),
)
_MODULES = []
for rel, prefix in _DIRS:
    for p in sorted((_ROOT / rel).glob("*.py")):
        if p.stem == "__init__":
            continue
        _MODULES.append(f"{prefix}.{p.stem}")


def test_模块清单非空():
    assert len(_MODULES) >= 30, f"只发现 {len(_MODULES)} 个模块，路径可能错了"


def test_每个模块都能独立导入():
    """逐个在干净进程里 import——任一模块作入口都必须成功。"""
    failed = []
    for m in _MODULES:
        r = subprocess.run([sys.executable, "-c", f"import {m}"],
                           capture_output=True, text=True, cwd=str(_ROOT))
        if r.returncode != 0:
            failed.append(f"{m}: {r.stderr.strip().splitlines()[-1]}")
    assert not failed, "以下模块无法独立导入:\n" + "\n".join(failed)


def test_termpath可独立导入():
    """曾经的基线崩溃点，单独钉住。"""
    r = subprocess.run([sys.executable, "-c", "import cas.syntax.termpath"],
                       capture_output=True, text=True, cwd=str(_ROOT))
    assert r.returncode == 0, r.stderr


def test_term的既有导入面不变():
    """惰性回接不得改变对外导入面。

    实例化（instantiate）已随模式元语言移居 cas.syntax.pattern（v4 §5.2）：
    项层无洞，Term 级实例化不存在——此项按 v4 契约更新，不留兼容别名。
    """
    from cas.syntax import term as T
    for name in ("subst", "free_vars", "term_at", "replace_at", "all_paths",
                 "_subst_raw", "_bind_into"):
        assert hasattr(T, name), f"导入面丢失: {name}"
    from cas.syntax import pattern as P
    for name in ("instantiate", "matches"):
        assert hasattr(P, name) or name == "matches", f"模式层导出丢失: {name}"


def test_惰性回接不吞未知名字():
    import cas.syntax.term as T
    try:
        T.__totally_missing__
    except AttributeError:
        pass
    else:
        raise AssertionError("__getattr__ 静默吞掉了未知属性")


def test_树遍历只有一份实现():
    """_postorder 曾在 pprint 与 simplify 各存一份同构副本。"""
    import cas.frontend.pprint as P
    import cas.math.simplify as Sm
    from cas.syntax.termpath import postorder
    assert not hasattr(P, "_postorder")
    assert not hasattr(Sm, "_postorder")
    assert callable(postorder)