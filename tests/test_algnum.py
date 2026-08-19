import unittest

from cas.term import S
from cas.parser import parse


x = S("x")


class TestAlgnum(unittest.TestCase):
    def test_trace_shift(self):
        from cas.algnum import tr_eval, tr_power_sums
        from cas.poly import Poly

        m = Poly.from_term(parse("x^2+1"), (x,))
        self.assertEqual(tr_power_sums(m, 6), [0, -2, 0, 2, 0, -2])
        self.assertEqual(tr_eval(m, Poly.one((x,)), 0), 2)
        self.assertEqual(tr_eval(m, Poly.one((x,)), 1), 0)
        self.assertEqual(tr_eval(m, Poly.one((x,)), 2), -2)
        self.assertEqual(tr_eval(m, Poly((x,), {(1,): 1}), 0), 0)
        self.assertEqual(tr_eval(m, Poly((x,), {(1,): 1}), 1), -2)
        self.assertEqual(tr_eval(m, Poly((x,), {(1,): 1}), 2), 0)


if __name__ == "__main__":
    unittest.main(verbosity=2)
