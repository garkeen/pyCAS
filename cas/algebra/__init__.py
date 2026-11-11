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
Hensel lifting, Zassenhaus recombination, `Z[x]`/`Q[x]` factorization, a
factorization specification/checker/operation and any workflow or REPL wiring
are not implemented; A2 is not complete.
"""
