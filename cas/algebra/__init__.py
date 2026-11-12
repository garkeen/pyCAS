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
low-level API with exact contracts and property tests.

A2c registers that search end to end for the fixed default ``Q[x]`` view:
`cas.math.algebra.factorization_operation` proposes `HasFactorization` with
the search unit, the canonical encoded factor set, a `FactorizationCertificate`
and the search-generated Hensel witness; `FactorizationChecker` independently
re-proves the product, radical and irreducibility.  `bootstrap` and
`bootstrap_elementary` install the checker and operation, the workspace
publishes a `DECOMPOSITION`/`ONE_VERIFIED` result with the `unit`/`factors`
structured components, and the REPL exposes `factor [@LABEL]`.  The
parameterized assembly does not intern `HasFactorization` or register the
operation.  A public `Z[x]` factorization entry with unit/multiplicity output,
multivariate gcd/factorization, algebraic extensions and A3 are still not
implemented; A2 is not complete.

The I0-L0/L1/L2/L3 slice in `logarithmic_integration` adds the rational-residue
logarithmic part of a `Q(x)` integral: `residue_polynomial` computes
`Res_x(B, A - y*B')` exactly in a private `Q(y)` tower, and
`rational_log_integral` divides out the polynomial part, reuses the existing
Hermite reduction, factors the residue polynomial over `Q`, and returns a
`RationalLogIntegral` of a rational-function part and monic squarefree
logarithm terms with rational coefficients.  An irreducible residue factor of
degree at least two is refused with `rational_residues` and
`algebraic_logarithmic_part`, and no partial result is returned.  This is a
public low-level API with exact contracts and property tests; the
`HasRationalLogAntiderivative` specification and independent checker, the
`integrate_rational_logarithmic` operation, the elementary bootstrap,
workspace helper and REPL `integrate_log` are now wired end to end for the
fixed default `Q[x]` view.  The checker consumes the declared `log`
`FunctionSymbol` domain and derivative law through `LogFunctionSemantics` and
enforces a degree/log-term budget; the operation and checker reject a
vocabulary without that declared semantics.  `bootstrap` and the parameterized
assemblies do not intern the predicate or register the operation.  The
fragment is rational-residue-only, and full I0 (algebraic residues, RootSum
representations, real-log branches and the Risch tower) remains open.
"""
