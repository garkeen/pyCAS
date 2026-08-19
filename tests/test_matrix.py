import unittest

from cas.term import N
from cas.pprint import to_str


class TestMatrix(unittest.TestCase):
    def _M(self, spec):
        from cas.matrix import Matrix

        return Matrix.parse(spec)

    def test_parse_and_errors(self):
        from cas.matrix import MatrixError

        self.assertEqual(self._M("[[1,2],[3,4]]").nrows, 2)
        self.assertEqual(self._M("[[1,2],[3,4]]").ncols, 2)
        with self.assertRaises(MatrixError):
            self._M("[[1,2],[3]]")
        with self.assertRaises(MatrixError):
            self._M("[[1,2],[c")

    def test_arith(self):
        m = self._M("[[1,2],[3,4]]")
        self.assertEqual(to_str(m.add(m).rows[0][1]), "4")
        self.assertEqual(to_str(m.scale(N(3)).rows[1][0]), "9")
        p = m.mul(m)
        self.assertEqual(to_str(p.rows[0][0]), "7")
        self.assertEqual(to_str(p.rows[1][1]), "22")
        self.assertEqual(to_str(m.transpose().rows[0][1]), "3")
        self.assertEqual(to_str(m.trace()), "5")

    def test_det(self):
        self.assertEqual(to_str(self._M("[[1,2],[3,4]]").det()), "-2")
        self.assertEqual(to_str(self._M("[[2,0,1],[1,3,0],[0,1,2]]").det()), "13")
        self.assertEqual(to_str(self._M("[[1,2,3],[4,5,6],[7,8,9]]").det()), "0")
        self.assertEqual(to_str(self._M("[[a,b],[c,d]]").det()), "a*d - b*c")

    def test_inv(self):
        m = self._M("[[1,2],[3,4]]")
        i = m.inv()
        self.assertEqual(to_str(i.rows[0][0]), "-2")
        self.assertEqual(to_str(i.rows[1][1]), "-1/2")
        p = m.mul(i)
        self.assertEqual(to_str(p.rows[0][0]), "1")
        self.assertEqual(to_str(p.rows[1][1]), "1")
        self.assertIs(self._M("[[1,2],[2,4]]").inv(), None)

    def test_rank(self):
        self.assertEqual(self._M("[[1,2],[3,4]]").rank(), 2)
        self.assertEqual(self._M("[[1,2,3],[4,5,6],[7,8,9]]").rank(), 2)
        self.assertEqual(self._M("[[1,1],[2,2]]").rank(), 1)

    def test_solve(self):
        from cas.matrix import LinResult

        r = self._M("[[1,2],[3,4]]").solve([N(3), N(0)])
        self.assertEqual([to_str(t) for t in r.unique], ["-6", "9/2"])
        r2 = self._M("[[1,1],[2,2]]").solve([N(1), N(2)])
        self.assertEqual([to_str(t) for t in r2.particular], ["1", "0"])
        self.assertEqual([to_str(t) for t in r2.null_basis[0]], ["-1", "1"])
        r3 = self._M("[[1,1],[2,2]]").solve([N(1), N(3)])
        self.assertIsInstance(r3, LinResult)
        self.assertIsNone(r3.unique)
        self.assertIsNone(r3.particular)
        r4 = self._M("[[1,0,1],[0,1,1]]").solve([N(1), N(2)])
        self.assertEqual([to_str(t) for t in r4.particular], ["1", "2", "0"])

    def test_session_matrix(self):
        from cas.session import Session

        s = Session()
        self.assertEqual(s.mdet("[[1,2],[3,4]]"), "-2")
        self.assertIn("x1 = -6", s.msolve("[[1,2],[3,4]]", "[3,0]"))
        self.assertEqual(s.minv("[[1,2],[2,4]]"), "singular")
        self.assertEqual(s.mrank("[[1,2],[3,4]]"), "2")

    def test_symbolic_zero(self):
        # 构造器规范化后，符号消元的判零可靠（det/rank 一致）
        m = self._M("[[a,a],[a,a]]")
        self.assertEqual(to_str(m.det()), "0")
        self.assertEqual(m.rank(), 1)


if __name__ == "__main__":
    unittest.main(verbosity=2)
