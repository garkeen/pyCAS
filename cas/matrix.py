import re

from cas import term as T
from cas.parser import parse
from cas.pprint import to_str
from cas.simplify import simplify, expand

_PLUS = T.fn("Plus")
_TIMES = T.fn("Times")


class MatrixError(Exception):
    pass


def _zero(t):
    return t is T.ZERO


def _row_str(row):
    return "[" + ", ".join(to_str(t) for t in row) + "]"


class LinResult:
    __slots__ = ("unique", "particular", "null_basis")

    def __init__(self, unique=None, particular=None, null_basis=None):
        self.unique = unique
        self.particular = particular
        self.null_basis = null_basis


class Matrix:
    __slots__ = ("rows", "nrows", "ncols")

    def __init__(self, rows):
        if not rows:
            raise MatrixError("empty matrix")
        ncols = len(rows[0])
        if ncols == 0 or any(len(r) != ncols for r in rows):
            raise MatrixError("non-rectangular matrix")
        for r in rows:
            for t in r:
                if not isinstance(t, T.Term):
                    raise MatrixError("matrix entries must be terms")
        self.rows = rows
        self.nrows = len(rows)
        self.ncols = ncols

    @classmethod
    def parse(cls, spec):
        s = spec.strip()
        if not (s.startswith("[[") and s.endswith("]]")):
            raise MatrixError("matrix spec must look like [[a,b],[c,d]]")
        rows = []
        for raw in s[2:-2].split("],["):
            cells = [c.strip() for c in raw.split(",")]
            if any(not c for c in cells):
                raise MatrixError("empty cell")
            rows.append([parse(c) for c in cells])
        return cls(rows)

    def add(self, other):
        if (self.nrows, self.ncols) != (other.nrows, other.ncols):
            raise MatrixError("shape mismatch in add")
        return Matrix(
            [
                [_PLUS(a, b) for a, b in zip(r1, r2)]
                for r1, r2 in zip(self.rows, other.rows)
            ]
        )

    def scale(self, c):
        return Matrix([[simplify(_TIMES(c, t)) for t in r] for r in self.rows])

    def mul(self, other):
        if self.ncols != other.nrows:
            raise MatrixError("shape mismatch in mul")
        cols = list(zip(*other.rows))
        return Matrix(
            [
                [simplify(_PLUS(*[_TIMES(a, b) for a, b in zip(r, col)])) for col in cols]
                for r in self.rows
            ]
        )

    def transpose(self):
        return Matrix([list(r) for r in zip(*self.rows)])

    def trace(self):
        if self.nrows != self.ncols:
            raise MatrixError("trace needs square")
        return simplify(_PLUS(*[self.rows[i][i] for i in range(self.nrows)]))

    def _eliminate(self, nrhs=None):
        n = self.nrows
        if nrhs is None:
            aug = [list(r) for r in self.rows]
            total = self.ncols
        else:
            aug = [list(r) + rhs for r, rhs in zip(self.rows, nrhs)]
            total = self.ncols + len(nrhs[0])
        pivot_cols = []
        swaps = 0
        r = 0
        for c in range(self.ncols):
            piv = None
            for i in range(r, n):
                if not _zero(aug[i][c]):
                    piv = i
                    break
            if piv is None:
                continue
            if piv != r:
                aug[r], aug[piv] = aug[piv], aug[r]
                swaps += 1
            p = aug[r][c]
            for i in range(r + 1, n):
                if _zero(aug[i][c]):
                    continue
                f = T.div(aug[i][c], p)
                aug[i] = [
                    _PLUS(aug[i][j], T.neg(_TIMES(f, aug[r][j])))
                    for j in range(total)
                ]
            pivot_cols.append(c)
            r += 1
            if r == n:
                break
        return aug, pivot_cols, swaps

    def _backsub(self, aug, pivot_cols, nrhs):
        r = len(pivot_cols)
        for k in range(r - 1, -1, -1):
            c = pivot_cols[k]
            p = aug[k][c]
            for i in range(k - 1, -1, -1):
                if _zero(aug[i][c]):
                    continue
                f = T.div(aug[i][c], p)
                aug[i] = [
                    _PLUS(aug[i][j], T.neg(_TIMES(f, aug[k][j])))
                    for j in range(self.ncols + nrhs)
                ]

    def det(self):
        if self.nrows != self.ncols:
            raise MatrixError("det needs square")
        aug, pivot_cols, swaps = self._eliminate()
        if len(pivot_cols) < self.nrows:
            return T.ZERO
        prod = T.ONE
        for i in range(self.nrows):
            prod = _TIMES(prod, aug[i][pivot_cols[i]])
        if swaps % 2:
            prod = T.neg(prod)
        return simplify(expand(prod))

    def rank(self):
        aug, pivot_cols, _ = self._eliminate()
        return len(pivot_cols)

    def inv(self):
        if self.nrows != self.ncols:
            raise MatrixError("inv needs square")
        n = self.nrows
        id_rhs = [
            [T.ONE if i == j else T.ZERO for j in range(n)]
            for i in range(n)
        ]
        aug, pivot_cols, _ = self._eliminate(id_rhs)
        if len(pivot_cols) < n:
            return None
        self._backsub(aug, pivot_cols, n)
        for k in range(n):
            p = aug[k][pivot_cols[k]]
            aug[k] = [simplify(T.div(t, p)) for t in aug[k][n:]]
        return Matrix(aug)

    def solve(self, b):
        if len(b) != self.nrows:
            raise MatrixError("rhs length mismatch")
        n = self.ncols
        aug, pivot_cols, _ = self._eliminate([ [bi] for bi in b ])
        r = len(pivot_cols)
        for i in range(r, self.nrows):
            if not _zero(aug[i][n]):
                return LinResult()
        if r == n:
            self._backsub(aug, pivot_cols, 1)
            sol = []
            for k in range(n):
                p = aug[k][pivot_cols[k]]
                sol.append(simplify(T.div(aug[k][n], p)))
            return LinResult(unique=sol)
        free = [c for c in range(n) if c not in pivot_cols]
        self._backsub(aug, pivot_cols, 1)
        part = [T.ZERO] * n
        for k, c in enumerate(pivot_cols):
            part[c] = simplify(T.div(aug[k][n], aug[k][c]))
        basis = []
        for f in free:
            v = [T.ZERO] * n
            v[f] = T.ONE
            for k, c in enumerate(pivot_cols):
                v[c] = simplify(T.div(T.neg(aug[k][f]), aug[k][c]))
            basis.append(v)
        return LinResult(particular=part, null_basis=basis)

    def show(self):
        return "\n".join(_row_str(r) for r in self.rows)

    # ---------------- 谱理论（ODE 常系数系统前置） ----------------

    def charpoly(self, lam=None):
        """特征多项式 det(lam*I - M) -> (term, lam)。

        用排列定义（Leibniz 公式）而非消元：消元的除法会在元素里留分母，
        det 的 expand 无法通分清掉；纯乘加展开天然是多项式表示。
        ODE 尺度的矩阵（n 小）代价可接受。
        """
        if self.nrows != self.ncols:
            raise MatrixError("charpoly needs square")
        lam = lam if lam is not None else T.S("lam")
        a = [
            [
                _PLUS(lam, T.neg(self.rows[i][j])) if i == j else T.neg(self.rows[i][j])
                for j in range(self.ncols)
            ]
            for i in range(self.nrows)
        ]
        n = self.nrows

        def perms(k, used, acc):
            if k == n:
                return [acc]
            out = []
            for j in range(n):
                if j in used:
                    continue
                out.extend(perms(k + 1, used | {j}, acc + [(k, j)]))
            return out

        terms = []
        for p in perms(0, set(), []):
            prod = T.ONE
            for i, j in p:
                prod = _TIMES(prod, a[i][j])
            inv = sum(1 for x in range(len(p)) for y in range(x + 1, len(p)) if p[x][1] > p[y][1])
            terms.append(T.neg(prod) if inv % 2 else prod)
        return simplify(expand(_PLUS(*terms))), lam

    def eigenvalues(self):
        """特征值：特征多项式走 solve（数值系数低次/有理根；符号系数走参数化路径）。

        返回 SolveResult；高次不可解时诚实 unsupported。
        """
        from cas.solve import solve

        term, lam = self.charpoly()
        return solve(term, lam)

    def eigenvectors(self):
        """[(特征值, 零空间基向量列表)]：对每个特征值解 (M - v*I) x = 0。

        特征值不可解时抛 MatrixError（诚实拒答）。判零依赖构造器规范形。
        """
        r = self.eigenvalues()
        if r.status != "ok":
            raise MatrixError("eigenvalues unsupported: " + (r.note or r.status))
        out = []
        n = self.nrows
        for v in r.solutions:
            shifted = Matrix([
                [
                    _PLUS(self.rows[i][j], T.neg(v)) if i == j else self.rows[i][j]
                    for j in range(self.ncols)
                ]
                for i in range(n)
            ])
            nr = shifted.solve([T.ZERO] * n)
            out.append((v, nr.null_basis or []))
        return out