# -*- coding: utf-8 -*-
"""测试会话装配：显式 bootstrap（v4 §7.1）。

数学语义不再由 import 副作用注册，所以测试必须先装配一次。放在 conftest 里
是为了让「装配」成为测试环境的一部分，而不是每个用例自己重复。
"""

from cas.runtime import bootstrap

bootstrap()
