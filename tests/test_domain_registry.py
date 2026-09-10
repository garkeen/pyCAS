# -*- coding: utf-8 -*-
"""域注册表：装配集中、职责单一。

钉子（收敛前的事实）：
· 注册散在 4 处（q.py / z.py 自注册、poly.py 运行时按变元集懒注册、
  project.py 代注册 ℚ(i)），注册表内容取决于谁碰巧被 import。
· `lookup()` / `domain_scope()` 全项目零调用——注册表只写不读。
· K(x) 从不注册，与 K[x] 不对称；poly 的懒注册让表无界增长。
"""

import subprocess
import sys

from cas.math.domains.base import _DOMAINS, lookup
from cas.syntax.term import S


def test_域包纯声明_零导入副作用():
    """导入 cas.math.domains 不得往注册表里写任何东西。"""
    code = ("from cas.math.domains.base import _DOMAINS; "
            "import cas.math.domains; print(len(_DOMAINS))")
    out = subprocess.run([sys.executable, "-c", code], capture_output=True,
                         text=True, cwd=".")
    assert out.returncode == 0, out.stderr
    assert out.stdout.strip() == "0"


def test_装配点是project_注册三个常驻基域():
    code = ("from cas.math.domains.base import _DOMAINS; "
            "import cas.math.project; print(','.join(sorted(_DOMAINS)))")
    out = subprocess.run([sys.executable, "-c", code], capture_output=True,
                         text=True, cwd=".")
    assert out.returncode == 0, out.stderr
    assert out.stdout.strip().split(",") == ["Q", "Q(i)", "Z"]


def test_参数化域不进注册表():
    """K[x]/K(x) 是按变元集参数化的实例，归工厂缓存，不进注册表。"""
    before = set(_DOMAINS)
    from cas.math.domains.poly import poly_domain
    from cas.math.domains.ratfunc import ratfunc_domain
    for v in ("x", "y", "zzz_unique"):
        poly_domain(S(v))
        ratfunc_domain(S(v))
    assert set(_DOMAINS) == before, "参数化实例涌入了注册表"


def test_注册表被投影层消费_不是只写不读():
    import cas.math.project  # noqa: F401  触发装配
    for name, cls in [("Z", "ZDomain"), ("Q", "QDomain"), ("Q(i)", "QIDomain")]:
        d = lookup(name)
        assert d is not None, f"{name} 未注册"
        assert type(d).__name__ == cls


def test_工厂缓存仍然复用同变元集实例():
    from cas.math.domains.poly import poly_domain
    from cas.math.domains.ratfunc import ratfunc_domain
    assert poly_domain(S("x")) is poly_domain(S("x"))
    assert ratfunc_domain(S("x")) is ratfunc_domain(S("x"))
    assert poly_domain(S("x")) is not poly_domain(S("y"))


def test_register在项目里只有一处调用点():
    """注册责任唯一：全项目仅 cas/project 一处调用 register()。

    只钉文件不钉行号——行号会随正常编辑漂移，钉了就是自找麻烦。
    """
    import pathlib
    hits = []
    for p in pathlib.Path("cas").rglob("*.py"):
        for i, line in enumerate(p.read_text(encoding="utf-8").splitlines(), 1):
            s = line.strip()
            if s.startswith("register(") and "def register(" not in s:
                hits.append(f"{p.as_posix()}:{i}")
    assert len(hits) == 1, f"注册点不唯一: {hits}"
    assert hits[0].startswith("cas/math/project.py:"), f"装配点漂移: {hits[0]}"


def test_作用域注册机制可用_供ℚ_α_将来使用():
    """架构 §3.4 要求代数扩张必须限定在单次计算作用域内。"""
    from cas.math.domains.base import Domain, domain_scope, register

    class _Tmp(Domain):
        name = "Tmp-scope-test"
        scoped = True

        def normalize(self, t):
            return t

        def equal(self, a, b):
            return a is b

    d = _Tmp()
    with domain_scope(d):
        assert lookup("Tmp-scope-test") is d
    assert lookup("Tmp-scope-test") is None      # 退出即注销

    try:
        register(d)                              # scoped 域禁止常驻注册
    except ValueError:
        pass
    else:
        raise AssertionError("scoped 域竟被允许常驻注册")
