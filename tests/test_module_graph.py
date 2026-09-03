# -*- coding: utf-8 -*-
"""模块图：每个模块都能独立导入。

钉子：cas/term.py 末尾曾直接 `from cas.termpath import ...`，而 termpath
顶部又 `from cas import term as T` —— 于是 `import cas.termpath` 作为入口
必然撞上 term 的半初始化状态而 ImportError（基线即崩，当时注释却写着
"无导入环"）。改 PEP 562 惰性 __getattr__ 后两个方向都能独立导入。
"""

import subprocess
import sys
from pathlib import Path

_ROOT = Path(__file__).resolve().parent.parent
_MODULES = []
for rel in ("cas", "cas/domains", "library"):
    for p in sorted((_ROOT / rel).glob("*.py")):
        mod = f"{p.parent.name}.{p.stem}" if rel != "cas" else f"cas.{p.stem}"
        if rel == "cas/domains":
            mod = f"cas.domains.{p.stem}"
        if p.stem != "__init__":
            _MODULES.append(mod)


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
    r = subprocess.run([sys.executable, "-c", "import cas.termpath"],
                       capture_output=True, text=True, cwd=str(_ROOT))
    assert r.returncode == 0, r.stderr


def test_term的既有导入面不变():
    """惰性回接不得改变对外导入面。"""
    from cas import term as T
    for name in ("subst", "instantiate", "free_vars", "term_at",
                 "replace_at", "all_paths", "_subst_raw",
                 "_instantiate_raw", "_bind_into"):
        assert hasattr(T, name), f"导入面丢失: {name}"


def test_惰性回接不吞未知名字():
    import cas.term as T
    try:
        T.__totally_missing__
    except AttributeError:
        pass
    else:
        raise AssertionError("__getattr__ 静默吞掉了未知属性")


def test_树遍历只有一份实现():
    """_postorder 曾在 pprint 与 simplify 各存一份同构副本。"""
    import cas.pprint as P
    import cas.simplify as Sm
    from cas.termpath import postorder
    assert not hasattr(P, "_postorder")
    assert not hasattr(Sm, "_postorder")
    assert callable(postorder)
