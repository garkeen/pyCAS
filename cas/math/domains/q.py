"""ℚ 域：字面有理算术。

标准形 = qarith.fold（全数字子树精确折叠，中性元吸收）。
判等 = 折叠后数值比较，片段内完全判定。
成员 = 纯数字树（eval_exact 空环境求值成功）。
"""

from fractions import Fraction as Fr

from cas.syntax import term as T
from cas.math.qarith import fold, eval_exact, EvalNumError
from cas.math.domains.base import Domain, FracRing


class QRing(FracRing):
    """ℚ 系数环：Fraction 原生运算，零包装。"""

    is_euclidean = True

    def from_int(self, n):
        return Fr(n)

    def from_frac(self, f):
        return f

    def add(self, a, b):
        return a + b

    def neg(self, a):
        return -a

    def mul(self, a, b):
        return a * b

    def divmod_(self, a, b):
        return a / b, Fr(0)


Q_RING = QRing()


class QDomain(Domain):
    """有理数域 ℚ。"""

    name = "Q"
    is_field = True
    is_ordered = True
    is_euclidean = True

    def member(self, t) -> bool:
        try:
            eval_exact(t, {})
            return True
        except (EvalNumError, ZeroDivisionError):
            return False

    def normalize(self, t):
        if not self.member(t):
            return None
        return fold(t)

    def equal(self, a, b):
        if not (self.member(a) and self.member(b)):
            return None                  # 非成员：调用方越界
        return T.num_val(fold(a)) == T.num_val(fold(b))


# 单例。注册不是本模块的事：域包只声明，装配（含注册进阶梯）归
# 投影层 cas/project——见 cas/domains/__init__.py 的分工说明。
Q_DOMAIN = QDomain()
