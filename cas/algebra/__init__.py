"""Algebra: effective structures, their descriptions, and exact algorithms.

This layer does not import terms, frames or the kernel. A structure consumes and
produces its own element type; bridging those elements to syntax belongs to the
semantics layer.

The domain-matrix algorithms in `linear` and the integer normal forms in
`integer_matrix` are a public low-level API.  They have exact contracts and
property tests, but no matrix expression bridge yet, so they are not registered
as workflow operations.  Polynomial gcd and resultant are registered operations
with independent checkers because the polynomial term bridge exists.

The Groebner core is split between `multivariate` (exact multivariate division,
leading terms and S-polynomials) and `groebner` (Buchberger, reduced bases and
cofactors).  Both remain a public low-level API with exact contracts and
property tests.  The `HasGroebnerBasis` checker, fixed `Q[x, y]`/LEX operation
and runtime/workflow/REPL wiring live in the math, semantics and workflow
layers respectively; the generator-mode request/view foundation stays in the
language and semantics layers.

The A2a1 finite-field and integer-polynomial primitives are split by
responsibility: `finite_field` provides deterministic 64-bit primality and the
canonical prime field `F_p`; `modular_polynomial` provides modular
exponentiation, coefficient reduction, the squarefree predicate and the
deterministic Rabin irreducibility test; `modular_factorization` provides
deterministic Berlekamp factorization of monic squarefree polynomials; and
`integer_polynomial` provides the `Z[x]`/`Q[x]` primitive form, the
Landau/Mignotte coefficient bound and exact integer coefficient helpers.
These are a public low-level API with exact contracts and property tests.

The A2a2a Hensel slice lives in `factorization`: `FactorizationBudget`,
`HenselLift`, `hensel_lift_factorization` (binary-tree linear lifting of a
complete modular factorization to a prime power) and
`hensel_witness_for_radical` (deterministic prime scan, independent Berlekamp
recomputation and the minimal precision above twice the coefficient bound).
This is also a public low-level API with exact contracts and property tests.

The A2a2b slice in the same module adds Zassenhaus subset recombination and the
first `Z[x]`/`Q[x]` factorization entries: `factor_primitive_integer` factors a
primitive squarefree integer polynomial into primitive irreducible integer
factors, `factor_polynomial_over_q` combines Yun's squarefree decomposition
with that search into a `Factorization` record of a nonzero rational unit and
monic rational factors with multiplicities, `factorization_key` fixes the
deterministic factor order, and `FactorizationBudget.max_recombination_tests`
bounds the recombination tests.  The `Factorization` record checks only the
structural invariants and does not claim irreducibility.  This remains a public
low-level API with exact contracts and property tests.  `HasFactorization`, an
independent checker, operation, bootstrap, workflow/REPL wiring, a public
`Z[x]` factorization entry with unit/multiplicity output, multivariate
gcd/factorization and algebraic extensions are not implemented; A2 is not
complete.
"""
