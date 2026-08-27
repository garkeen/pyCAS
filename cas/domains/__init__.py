# -*- coding: utf-8 -*-
"""数域系统：显式声明、按域分派的规范化/判等（docs/cas_v3_arch.md 三）。

导入即注册可用域；上层通过 poly_domain / ratfunc_domain 取用。
判定的三值性属于判定层（cas/verdict）；域层 equal 返回 bool|None。
"""

from cas.domains.base import Ring, RingError, FracRing, Domain, register
from cas.domains import q
from cas.domains import poly
from cas.domains import ratfunc

from cas.domains.q import Q_RING, QDomain
from cas.domains.poly import poly_domain, PolyDomain
from cas.domains.ratfunc import ratfunc_domain, RatFuncDomain
