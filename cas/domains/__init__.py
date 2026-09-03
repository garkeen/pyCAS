# -*- coding: utf-8 -*-
"""数域系统：显式声明、按域分派的规范化/判等（docs/cas_v3_arch.md 三）。

## 分工：本包只声明，装配归投影层

本包是**纯声明**——定义域与环的类，不产生任何导入期副作用（不自注册）。
把域注册进阶梯是装配的职责，唯一装配点是投影层 `cas/project`：

· 域包只依赖 cas.term（层位纪律，见 base.py 模块串），因此拿不到图书馆
  声明的常数原子——ℚ(i) 需要注入 library 的 i，装配必然发生在能同时看见
  library 与 domains 的层，即投影层。
· 注册若散在各域模块（import 即注册），注册表内容就取决于谁碰巧被
  import：新增一个域模块而无人 import 它，就会静默从 lookup() 里消失。
  集中装配消除这种导入顺序敏感性。

注册表只管**常驻基域**（ℤ / ℚ / ℚ(i)）。K[x]、K(x) 是按变元集参数化的
实例，由各自的工厂缓存持有，不进注册表（理由见 poly_domain 文档串）。

判定的三值性属于判定层（cas/verdict）；域层 equal 返回 bool | None。
"""

from cas.domains.base import (Ring, RingError, FracRing, Domain, register,
                              domain_scope, lookup)
from cas.domains import q
from cas.domains import z
from cas.domains import qi
from cas.domains import poly
from cas.domains import ratfunc

from cas.domains.q import Q_RING, QDomain, Q_DOMAIN
from cas.domains.z import Z_RING, ZDomain, Z_DOMAIN
from cas.domains.qi import QI_RING, QIDomain
from cas.domains.poly import poly_domain, PolyDomain
from cas.domains.ratfunc import ratfunc_domain, RatFuncDomain
