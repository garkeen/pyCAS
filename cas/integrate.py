"""有理函数不定积分：Hermite 分解 + 对数部分（线性闭式 / RootOf）+ 符号验证通道。

兼容门面（M6.7 拆分）：实现按功能分居三个模块——
    cas/ratint.py   有理积分核（Hermite/RootOf、AN 区间、参数化收集）
    cas/intcore.py  不定积分入口与快速通道（u-sub/spec 表/tan-half/SOLVERS）
    cas/defint.py   定积分（NL+奇点拆分+反常判敛+分段+对称折叠）
本文件显式重导出三者的全部历史公开名与内部协作名——既有
`from cas.integrate import ...`（含测试引用的内部名）零改动。
"""

from fractions import Fraction as Fr

from cas.errors import PolyError
from cas.risch import RischNonElementary, RischUnsupported
from cas.poly import Poly, SymRat, ugcd
from cas.apart import apart
from cas.algnum import RootOf, qa_div, qa_mul, qa_inv, tr_power_sums, tr_eval, coefs
from cas.simplify import simplify
from cas.pprint import to_str
from cas import term as T
from cas.term import S, N, Sym, IU
from cas.scalarutil import (rf_const_ga, ga_den, lcm2,
                            ga_vec_to_ints, mk_zero_like,
                            leaf_has_ga, symrat_has_ga,
                            coef_zero, coef_re_im, poly_re_im)

# --- ratint：有理积分核 + AN 区间 + 参数化收集 ---
# （AN_INTERVALS/AN_RELATIONS 已退役，M7.0-b：统一迁 cas.algfield.ALG_FIELDS）
from cas.ratint import (_coef_term, _frac, _rat_pair,
                        _is_named_const, _CONST_FUNCT_HEADS,
                        _collect_const_params, _collect_rad_params,
                        _qa_to_term, _hermitte_power,
                        _classify_discriminant,
                        _RC_COUNTER,
                        _radical_bracket, _iv_mul, _poly_interval_sign,
                        _an_interval_sign, _log_terms, _integrate_poly,
                        _exact_sqrt_term, _assemble, _poly_eq_relaware,
                        _verify, _ga_rational_split, integrate_rational)

# --- intcore：不定积分入口与快速通道 ---
from cas.intcore import (_USUB_DEPTH, _term_size, _try_usub,
                         integrate, _symbol_power_antideriv,
                         _power_antideriv, _integrate_core,
                         _special_output, _trig_linear_integrand,
                         _spec_antideriv, _trig_check, _trig_sub,
                         _trig_tan_half, _flatten_inv)

# --- defint：定积分 ---
from cas.defint import (_parity_normalize, _defint_reflect,
                        _period_candidates, _absorb_shift,
                        _defint_period_fold, defint, defint_auto,
                        _is_inf, _is_pos_inf, _is_neg_inf,
                        _sing_points_half, _defint_improper,
                        _defint_piecewise, _sing_points, _numeric_cross)
