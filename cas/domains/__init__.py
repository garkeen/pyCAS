"""数域系统：显式声明、按域分派的规范化/判等（docs/cas_v3_arch.md 三）。

导入即注册可用域；上层通过 by_name / poly_domain / ratfunc_domain 取用。
"""

from cas.domains.base import (T3, Ring, RingError, FracRing, Domain,
                              register, by_name, all_domains)
from cas.domains import q
from cas.domains import poly
from cas.domains import ratfunc

from cas.domains.q import Q_RING
from cas.domains.poly import poly_domain, PolyDomain
from cas.domains.ratfunc import ratfunc_domain, RatFuncDomain
