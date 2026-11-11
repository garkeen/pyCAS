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
cofactors).  Both are a public low-level API: they have exact contracts and
property tests, but no registered multivariate operation, independent checker
or frontend consumer yet.  The generator-mode request/view foundation lives in
the language and semantics layers; the multivariate result model and the S1
wiring are still missing.
"""
