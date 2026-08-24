"""N6-P1 统一注册表类级验收（M78.5）。"""

import unittest
from fractions import Fraction as Fr

from cas.term import S, N
from cas.parser import parse
from cas.algfield import AlgField, AlgElem, ALG_FIELDS
from cas.kernelreg import (alg_field, alg_fields, register, unregister,
                           const_face_key, same_constant)


def _qf(v):
    return AlgField([Fr(-v), Fr(0), Fr(1)], Fr(1))


class TestAlgebraicSection(unittest.TestCase):
    """代数区 = ALG_FIELDS 本尊的统一视图（零破坏契约）。"""

    def test_roundtrip_shared_storage(self):
        f2 = _qf(2)
        sym = S("_kr_test_a")
        register(sym, f2)
        try:
            self.assertIs(alg_field(sym), ALG_FIELDS[sym])
            self.assertIn(sym, alg_fields())
        finally:
            unregister([sym])
        self.assertNotIn(sym, alg_fields())
        self.assertIsNone(alg_field(sym))

    def test_view_is_snapshot(self):
        f3 = _qf(3)
        sym = S("_kr_test_b")
        before = alg_fields()
        register(sym, f3)
        try:
            self.assertNotIn(sym, before)   # 快照不受后续注册影响
        finally:
            unregister([sym])


class TestConstFaceKeys(unittest.TestCase):
    """超越常数关系区：两面孔同值 ⟹ 同键。"""

    def test_dual_face_unification(self):
        k1 = const_face_key(parse("e"))
        k2 = const_face_key(parse("exp(1)"))
        self.assertEqual(k1, ('exp', Fr(1)))
        self.assertEqual(k2, ('exp', Fr(1)))
        self.assertTrue(same_constant(parse("e"), parse("exp(1)")))

    def test_literal_powers_distinct(self):
        self.assertEqual(const_face_key(parse("exp(2)")),
                         ('exp', Fr(2)))
        self.assertFalse(same_constant(parse("e"), parse("exp(2)")))

    def test_named_and_unknown(self):
        self.assertEqual(const_face_key(parse("pi")), ('named', 'pi'))
        self.assertFalse(same_constant(parse("e"), parse("pi")))
        self.assertIsNone(const_face_key(parse("x")))          # 变元
        self.assertIsNone(const_face_key(parse("sin(x)")))     # 未声明形态
        self.assertIsNone(same_constant(parse("x"), parse("e")))


class TestEngineFaceUnification(unittest.TestCase):
    """N6-P2：z-参数化层叶键级同一性（risch_core 单点）。"""

    def test_parametrize_unifies_dual_face(self):
        from cas.risch_core import _parametrize_const_logs
        from cas.pprint import to_str
        xv = S('x')
        f1, _ = _parametrize_const_logs(parse('exp(1)*x'), xv)
        f2, _ = _parametrize_const_logs(parse('e*x'), xv)
        self.assertEqual(to_str(f1), to_str(f2))
        self.assertEqual(to_str(f1), '_nc2*x')

    def test_dual_face_sum_counts(self):
        # exp(1)+e -> 2*_nc2：同面孔合并计数
        from cas.risch_core import _parametrize_const_logs
        from cas.pprint import to_str
        f, _ = _parametrize_const_logs(parse('exp(1)+e'), S('x'))
        self.assertEqual(to_str(f), '2*_nc2')

    def test_integer_literal_power_relation(self):
        # N6-P2c：exp(k)（非零整字面）与 e 的精确幂关系收进参数化层
        # ——复合替换 _nc2^k，不进回代；出口随 _nc2->E 统一还原 e^k
        from cas.risch_core import _parametrize_const_logs
        from cas.pprint import to_str
        f, bs = _parametrize_const_logs(parse('exp(2)*x'), S('x'))
        self.assertEqual(to_str(f), 'x*_nc2^2')
        self.assertEqual(to_str(bs[S('_nc2')]), 'e')

    def test_dual_face_sum_with_powers(self):
        # exp(2)+e -> _nc2+_nc2^2：两面孔+幂关系合并算术
        from cas.risch_core import _parametrize_const_logs
        from cas.pprint import to_str
        f, _bs = _parametrize_const_logs(parse('exp(2)+e'), S('x'))
        self.assertEqual(to_str(f), '_nc2 + _nc2^2')

    def test_nonunit_literal_honest(self):
        # 非整字面 / 超上限整字面：诚实保持核形态（分数幂需关系
        # 感知参数，N9/M78.8 辖区；|k|<=64 规模守卫）
        from cas.risch_core import _parametrize_const_logs
        from cas.pprint import to_str
        for src in ('exp(1/2)*x', 'exp(100)*x'):
            f, _ = _parametrize_const_logs(parse(src), S('x'))
            self.assertIn('exp(', to_str(f), src)


if __name__ == "__main__":
    unittest.main(verbosity=2)
