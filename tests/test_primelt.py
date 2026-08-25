"""N9 本原元压缩类级验收（M78.5）。

参照 primelt.spad：两生成元 resultant 压缩 + 强化判据（不可约门 +
生成元精确回验，覆盖源码 sqfree 判据的死循环类）。通用入口
compress_chain 叶数无关；依赖退化域诚实 None。
"""

import unittest
from fractions import Fraction as Fr

from cas.primelt import primitive_pair, compress_chain
from cas.parser import parse
from cas.pprint import to_str


class TestPrimitivePair(unittest.TestCase):
    def test_independent_sqrt_pair(self):
        res = primitive_pair([Fr(-2), Fr(0), Fr(1)],
                             [Fr(-3), Fr(0), Fr(1)])
        self.assertIsNotNone(res)
        Scoefs, c, mapA, mapB = res
        self.assertEqual(len(Scoefs) - 1, 4)
        self.assertEqual(c, 1)
        # 手推一致：√2=(β³−9β)/2、√3=(11β−β³)/2
        self.assertEqual(mapA, [Fr(0), Fr(-9, 2), Fr(0), Fr(1, 2)])
        self.assertEqual(mapB, [Fr(0), Fr(11, 2), Fr(0), Fr(-1, 2)])

    def test_dependent_field_honest_none(self):
        # ∛4 ∈ ℚ(∛2)：独立结果式给出分支乘积，不可约门拒绝
        res = primitive_pair([Fr(-2), Fr(0), Fr(0), Fr(1)],
                             [Fr(-4), Fr(0), Fr(0), Fr(1)])
        self.assertIsNone(res)


class TestCompressChain(unittest.TestCase):
    def test_chain_three_generators(self):
        ms = [[Fr(-2), Fr(0), Fr(1)], [Fr(-3), Fr(0), Fr(1)],
              [Fr(-5), Fr(0), Fr(1)]]
        leaves = [parse('2^(1/2)'), parse('3^(1/2)'), parse('5^(1/2)')]
        res = compress_chain(ms, leaves)
        self.assertIsNotNone(res)
        Scoefs, maps, beta_term = res
        # 独立三元二次域：次数 8
        self.assertEqual(len(Scoefs) - 1, 8)
        self.assertEqual(len(maps), 3)

    def test_single_pass_through(self):
        res = compress_chain([[Fr(-2), Fr(0), Fr(1)]],
                             [parse('2^(1/2)')])
        self.assertIsNotNone(res)
        Scoefs, maps, _t = res
        self.assertEqual(Scoefs, [Fr(-2), Fr(0), Fr(1)])
        self.assertEqual(maps, [[Fr(0), Fr(1)]])


class TestGeneralCollapse(unittest.TestCase):
    """try_collapse 通用路径（叶数无关）：形态+数值双验收。"""

    def _collapsed(self, src):
        from cas.evalnum import eval_approx
        t = parse(src)
        r = to_str(t)
        va = eval_approx(t, {})
        vb = eval_approx(parse(r), {})
        self.assertLess(abs(va - vb), 1e-9, src)
        return r

    def test_one_and_two_leaf(self):
        self.assertEqual(self._collapsed('sqrt(3+2*sqrt(2))'),
                         '2^(1/2) + 1')
        self.assertIn('5^(1/2)', self._collapsed('sqrt(6+2*sqrt(5))'))

    def test_negative_stays(self):
        # ℚ(√6) 内非完全幂：不坍缩
        self.assertIn('(6^(1/2) + 5)^(1/2)',
                      self._collapsed('sqrt(5+sqrt(6))'))

    def test_dependent_triple_honest(self):
        # √6=√2·√3：依赖叶集诚实不坍缩（关系检测属后续批次）
        r = self._collapsed(
            'sqrt(6+2*sqrt(2)+2*sqrt(3)+2*sqrt(6))')
        self.assertIn('^(1/2)', r.split(')^')[-2] + '^')


if __name__ == "__main__":
    unittest.main(verbosity=2)
