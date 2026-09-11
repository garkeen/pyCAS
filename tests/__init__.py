# Deterministic unit tests.
#
# Division of labour with stress/:
#   stress/ -- randomized stress tests covering the mathematical properties broadly
#   tests/  -- deterministic nails pinning degenerate shapes, fixed bugs, and
#              responsibility boundaries
#
# Both run in CI and neither substitutes for the other: the randomized bench is
# responsible for "the mathematics is right", the nails for "the structure and
# contracts have not regressed".
