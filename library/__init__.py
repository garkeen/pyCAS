"""图书馆包出口：装载 + 常数原子再导出。

内核引用常数一律 `from library import PI, E, IU, GAMMA`——
cas.term 不再携带任何具体数学常数。
"""

from library.api import (load_all, constant, function,
                         const_by_atom, const_by_name, is_const_name,
                         lookup_function, print_name,
                         const_positive, const_real, const_bounds,
                         register_domain_cond,
                         lookup_domain_cond,
                         all_functions, function_deriv,
                         ConstantDecl, FunctionDecl)
from library.constants import PI, E, IU, GAMMA

load_all()
