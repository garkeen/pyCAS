"""Linear algebra machine: row elimination over a field, rank, nullspace and
linear-system solving.

Linear dependence tests, the method of undetermined coefficients and the
parametric logarithmic-derivative test all rest on this layer, so it is a hard
item of the foundation gate. A matrix is a table of coefficient tables (a list of
rows); coefficients are manipulated through the generic ring protocol. Nullspace
bases and particular solutions are exact, with no floating point.

Determinants use the purely integer Bareiss algorithm (det_bareiss), which avoids
fraction growth on integer matrices and also serves matrices over Q after
clearing denominators.
"""


def _copy(rows):
    return [list(r) for r in rows]


def echelon(ring, rows, ncols=None):
    """Row echelon form (Gaussian elimination over a field).

    Returns (echelon matrix, list of pivot column indices). The input is not
    modified. `ncols` bounds the columns searched for pivots, so an augmented
    system eliminates only the coefficient columns and leaves the augmented
    column alone.
    """
    if not ring.is_field:
        from cas.math.domains.base import RingError
        raise RingError("row elimination requires field coefficients")
    m = _copy(rows)
    nrows = len(m)
    width = len(m[0]) if m else 0
    if ncols is None:
        ncols = width
    pivots = []
    r = 0
    for c in range(ncols):
        if r >= nrows:
            break
        piv = None
        for i in range(r, nrows):
            if not ring.is_zero(m[i][c]):
                piv = i
                break
        if piv is None:
            continue
        m[r], m[piv] = m[piv], m[r]
        inv = ring.div_exact(ring.from_int(1), m[r][c])
        m[r] = [ring.mul(x, inv) for x in m[r]]
        for i in range(nrows):
            if i != r and not ring.is_zero(m[i][c]):
                f = m[i][c]
                m[i] = [ring.sub(m[i][j], ring.mul(f, m[r][j]))
                        for j in range(width)]
        pivots.append(c)
        r += 1
    return m, pivots


def rank(ring, rows) -> int:
    _, pivots = echelon(ring, rows)
    return len(pivots)


def nullspace(ring, rows):
    """A nullspace basis: basis vectors of {x | Ax = 0}, each a tuple of length
    equal to the number of columns."""
    m, pivots = echelon(ring, rows)
    ncols = len(m[0]) if m else 0
    free = [c for c in range(ncols) if c not in pivots]
    basis = []
    for f in free:
        x = [ring.from_int(0)] * ncols
        x[f] = ring.from_int(1)
        for ri, pc in enumerate(pivots):
            x[pc] = ring.neg(m[ri][f])      # pivot row: x_pc + sum m*x_free = 0
        basis.append(tuple(x))
    return basis


def solve_system(ring, rows, b):
    """Solve Ax = b. Returns (particular solution, homogeneous basis), or None
    when there is no solution.

    `b` is a sequence of length equal to the number of rows. The augmented column
    is eliminated; if some row has all-zero coefficients but a nonzero augmented
    entry, there is no solution.
    """
    aug = [list(r) + [bi] for r, bi in zip(rows, b)]
    ncols = len(rows[0]) if rows else 0
    m, pivots = echelon(ring, aug, ncols=ncols)
    for ri, row in enumerate(m):
        if ri >= len(pivots) and all(ring.is_zero(x) for x in row[:ncols]):
            if not ring.is_zero(row[ncols]):
                return None                  # 0 = nonzero: no solution
    x0 = [ring.from_int(0)] * ncols
    for ri, pc in enumerate(pivots):
        x0[pc] = m[ri][ncols]
    basis = [v for v in nullspace(ring, rows)]
    return tuple(x0), basis


def det_bareiss(mat):
    """Determinant of an integer matrix by the fraction-free Bareiss algorithm,
    exact throughout.

    A step that does not divide evenly means the implementation is wrong, because
    Bareiss's theorem guarantees divisibility, so this raises. The empty matrix
    has determinant 1; a non-square matrix is refused.
    """
    n = len(mat)
    if any(len(r) != n for r in mat):
        raise ValueError("not a square matrix")
    if n == 0:
        return 1
    m = [list(r) for r in mat]
    sign = 1
    prev = 1
    for k in range(n - 1):
        if m[k][k] == 0:                     # find a nonzero pivot and swap rows
            sw = next((i for i in range(k + 1, n) if m[i][k] != 0), None)
            if sw is None:
                return 0
            m[k], m[sw] = m[sw], m[k]
            sign = -sign
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                num = m[k][k] * m[i][j] - m[i][k] * m[k][j]
                if num % prev != 0:
                    raise ArithmeticError("Bareiss divisibility violated")
                m[i][j] = num // prev
        prev = m[k][k]
    return sign * m[n - 1][n - 1]
