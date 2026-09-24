import random
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

from cas.api import back_substitute, solve_linear_with_condition
from cas.frontend.parser import parse
from cas.runtime import bootstrap
from cas.syntax.term import S


def main() -> None:
    runtime = bootstrap()
    for _ in range(20):
        slope = random.choice([value for value in range(-5, 6) if value])
        constant = random.randint(-5, 5)
        equation = parse(runtime, f"{slope}*x + {constant} == 0")
        solution, condition = solve_linear_with_condition(runtime, equation, S("x"))
        assert condition is not None
        assert back_substitute(runtime, equation, S("x"), solution).verdict.is_yes()
    print("random linear solve passed")


if __name__ == "__main__":
    main()
