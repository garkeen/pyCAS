"""examples/*.pycas 验证案例：DSL 文本即推导，回放即重建（驻留保证指针同一）。"""

import os
import unittest

from cas.pprint import to_str
from cas.session import Session

EXAMPLES = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "examples")


def replay_lines(fn):
    """逐条回放并返回每条输出（首行）。"""
    s = Session()
    outs = []
    with open(os.path.join(EXAMPLES, fn), encoding="utf-8") as fh:
        for line in fh:
            line = line.rstrip("\n")
            if not line.strip() or line.startswith("#"):
                continue
            outs.append(s.handle(line) or "")
    return s, outs


class TestCyclicPartsExample(unittest.TestCase):
    def test_derivation_replays_to_verified(self):
        s, outs = replay_lines("01_cyclic_parts.pycas")
        self.assertEqual(outs[-1], "VERIFIED")          # 微分回验收尾
        self.assertEqual(to_str(s.current), "-1/2*(cos(x)*exp(x) - exp(x)*sin(x))")
        # 推导全程入账：两步分部 + 一步消循环
        kinds = [st.rule_id for st in s.log]
        self.assertEqual(sum(1 for k in kinds if k.startswith("scheme:parts")), 2)
        self.assertIn("scheme:solveq", kinds)

    def test_replay_file_roundtrip(self):
        s, _ = replay_lines("01_cyclic_parts.pycas")
        s2 = Session()
        out = s2.handle(":replay " + os.path.join(EXAMPLES, "01_cyclic_parts.pycas"))
        self.assertIn("replayed 7 commands", out)
        self.assertIs(s2.current, s.current)   # 驻留：回放产物指针同一


class TestDefintGalleryExample(unittest.TestCase):
    def test_gallery(self):
        _s, outs = replay_lines("02_defint_gallery.pycas")
        self.assertIn("1/2*(exp(1) + 1)^2 - 1/2", outs[0])        # 正向换元（不求逆）
        self.assertIn("VERIFIED", outs[0])
        self.assertIn("exp(1) - 1", outs[1])                      # 嵌套换元 u=x^2
        self.assertEqual(outs[2].split()[0], "1")                 # ∫1/x^2 on [1,∞) 收敛
        self.assertIn("DIVERGES", outs[3])                        # ∫1/x on [1,∞) 判敛
        self.assertEqual(outs[4].split()[0], "1")                 # 分段 |x-1| on [0,2]


class TestRulesRefineSetsExample(unittest.TestCase):
    def test_session_rule_and_refine(self):
        s, outs = replay_lines("03_rules_refine_sets.pycas")
        self.assertIn("defined: cube_sum", outs[0])
        self.assertIn("(a + b)", outs[2])
        self.assertEqual(outs[5], "3*a")                          # refine 消费 a>0
        self.assertEqual(outs[6], "x in {-2, 2}")                 # 解集一等结构
        self.assertEqual(s.rules.rules["cube_sum"].origin, "session")


if __name__ == "__main__":
    unittest.main(verbosity=2)
