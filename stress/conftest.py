# -*- coding: utf-8 -*-
"""Test-session assembly: explicit bootstrap.

Mathematical semantics are no longer registered by an import side effect, so the tests
must assemble once. It lives in conftest so that assembly is part of the test
environment rather than repeated by every case.
"""

from cas.runtime import bootstrap

bootstrap()
