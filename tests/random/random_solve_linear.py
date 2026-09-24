"""Random parametric linear solving checks."""

import random

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

from cas.api import back_substitute, solve_linear_with_condition
from cas.frontend.parser import parse
from cas.runtime import bootstrap
from cas.runtime.dispatch import install
from cas.syntax.term import S


def main():
    install(bootstrap())
    for _ in range(20):
        slope = random.choice([value for value in range(-5, 6) if value])
        constant = random.randint(-5, 5)
        equation = parse(f"{slope}*x + {constant} == 0")
        solution, condition = solve_linear_with_condition(equation, S("x"))
        assert condition is not None
        assert back_substitute(equation, S("x"), solution).zero is True
    print("random linear solve passed")


if __name__ == "__main__":
    main()
