# -*- coding: utf-8 -*-
"""线性代数机器（架构 4.3）：域上行消元、秩、零空间、方程组求解。

Risch 的线性相关性判定、待定系数法、参数化对数导数判定全靠这一层，
是地基门控的硬条目。矩阵 = 系数表的表（行列表），系数经泛环协议操作；
零空间基与特解全部精确，无浮点。

行列式用 Bareiss 纯整数版（det_bareiss）：整数矩阵上免分式膨胀，
也是 ℚ 矩阵通分后的通道。
"""


def _copy(rows):
    return [list(r) for r in rows]


def echelon(ring, rows, ncols=None):
    """行阶梯化（域上高斯消元）。

    返回 (阶梯矩阵, 主元列号列表)。输入不被修改。
    ncols：主元搜索的列上界（增广系统只消元系数列，不碰增广列）。
    """
    if not ring.is_field:
        from cas.math.domains.base import RingError
        raise RingError("行消元要求域系数")
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
    """零空间基：{x | Ax = 0} 的基向量列表（每个是长度 = 列数的元组）。"""
    m, pivots = echelon(ring, rows)
    ncols = len(m[0]) if m else 0
    free = [c for c in range(ncols) if c not in pivots]
    basis = []
    for f in free:
        x = [ring.from_int(0)] * ncols
        x[f] = ring.from_int(1)
        for ri, pc in enumerate(pivots):
            x[pc] = ring.neg(m[ri][f])      # 主元行：x_pc + Σ m·x_free = 0
        basis.append(tuple(x))
    return basis


def solve_system(ring, rows, b):
    """Ax = b。返回 (特解, 齐次基)；无解返回 None。

    b 是长度 = 行数的序列。增广列消元：若某行主元全零而增广非零则无解。
    """
    aug = [list(r) + [bi] for r, bi in zip(rows, b)]
    ncols = len(rows[0]) if rows else 0
    m, pivots = echelon(ring, aug, ncols=ncols)
    for ri, row in enumerate(m):
        if ri >= len(pivots) and all(ring.is_zero(x) for x in row[:ncols]):
            if not ring.is_zero(row[ncols]):
                return None                  # 0 = 非零：无解
    x0 = [ring.from_int(0)] * ncols
    for ri, pc in enumerate(pivots):
        x0[pc] = m[ri][ncols]
    basis = [v for v in nullspace(ring, rows)]
    return tuple(x0), basis


def det_bareiss(mat):
    """整数矩阵行列式：Bareiss 免分式算法，全程精确整除。

    任一步除不尽说明实现有误（Bareiss 定理保证整除），抛异常。
    空矩阵行列式为 1；非方阵拒答。
    """
    n = len(mat)
    if any(len(r) != n for r in mat):
        raise ValueError("非方阵")
    if n == 0:
        return 1
    m = [list(r) for r in mat]
    sign = 1
    prev = 1
    for k in range(n - 1):
        if m[k][k] == 0:                     # 找非零主元换行
            sw = next((i for i in range(k + 1, n) if m[i][k] != 0), None)
            if sw is None:
                return 0
            m[k], m[sw] = m[sw], m[k]
            sign = -sign
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                num = m[k][k] * m[i][j] - m[i][k] * m[k][j]
                if num % prev != 0:
                    raise ArithmeticError("Bareiss 整除性破坏")
                m[i][j] = num // prev
        prev = m[k][k]
    return sign * m[n - 1][n - 1]
