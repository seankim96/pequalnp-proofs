"""Exact bordered Hessian minors at the 4x4 permanent base point I+J.

Run with Python 3. No external packages, search limit, or random choices.
Coordinates 4*i+j index rows then columns; the gradient border has index 16.
"""
from collections import Counter
from itertools import combinations, permutations
from math import gcd, prod


def bordered_hessian():
    matrix = [[0] * 17 for _ in range(17)]
    constant = 0
    for perm in permutations(range(4)):
        coords = [4 * row + col for row, col in enumerate(perm)]
        values = [1 + int(row == col) for row, col in enumerate(perm)]
        weight = prod(values)
        constant += weight
        for a, i in enumerate(coords):
            matrix[16][i] += weight // values[a]
            matrix[i][16] = matrix[16][i]
            for b, j in enumerate(coords):
                if i != j:
                    matrix[i][j] += weight // (values[a] * values[b])
    assert constant == 65
    assert matrix == list(map(list, zip(*matrix)))
    return matrix


def determinant(matrix):
    """Fraction-free Gaussian elimination with row pivoting."""
    a = [row.copy() for row in matrix]
    sign = previous = 1
    for k in range(len(a) - 1):
        pivot = next((i for i in range(k, len(a)) if a[i][k]), None)
        if pivot is None:
            return 0
        if pivot != k:
            a[k], a[pivot] = a[pivot], a[k]
            sign *= -1
        for i in range(k + 1, len(a)):
            for j in range(k + 1, len(a)):
                numerator = a[i][j] * a[k][k] - a[i][k] * a[k][j]
                a[i][j], remainder = divmod(numerator, previous)
                assert remainder == 0
        previous = a[k][k]
    return sign * a[-1][-1]


def sparse_directions(matrix):
    """Classify maximal pairwise-orthogonal families of two-entry directions."""
    gradient = matrix[-1]
    vectors = []
    for i, j in combinations(range(16), 2):
        if matrix[i][j]:
            continue
        common = gcd(gradient[i], gradient[j])
        vectors.append(((i, gradient[j] // common), (j, -gradient[i] // common)))
    assert len(vectors) == 48
    neighbors = [set() for _ in vectors]
    for i, j in combinations(range(48), 2):
        polar = sum(x * matrix[a][b] * y for a, x in vectors[i] for b, y in vectors[j])
        if polar == 0:
            neighbors[i].add(j)
            neighbors[j].add(i)

    def maximal(chosen, possible, excluded):
        if not possible and not excluded:
            yield frozenset(chosen)
            return
        pivot = max(possible | excluded, key=lambda v: (len(possible & neighbors[v]), -v))
        for v in sorted(possible - neighbors[pivot]):
            yield from maximal(chosen + [v], possible & neighbors[v], excluded & neighbors[v])
            possible.remove(v)
            excluded.add(v)

    families = list(maximal([], set(range(48)), set()))
    sizes = Counter(map(len, families))
    assert sizes == {2: 72, 6: 8}
    axes = [{4 * r + c for c in range(4)} for r in range(4)]
    axes.extend({4 * r + c for r in range(4)} for c in range(4))
    axis_families = {frozenset(i for i, v in enumerate(vectors) if all(a in axis for a, _ in v))
                     for axis in axes}
    assert axis_families == {f for f in families if len(f) == 6}
    print("48 two-entry direction lines: 72 maximal pairs and 8 row/column families of rank 3")


def main():
    matrix = bordered_hessian()
    for n in [12, 13, 14, 15, 16]:
        values = Counter()
        for coordinates in combinations(range(16), n):
            indices = (*coordinates, 16)
            minor = [[matrix[i][j] for j in indices] for i in indices]
            values[determinant(minor)] += 1
        print(f"{n} coordinates: {sum(values.values())} supports, "
              f"{values[0]} singular, {len(values)} distinct determinants, "
              f"range [{min(values)}, {max(values)}]")
    sparse_directions(matrix)
    block = [*range(12), 16]
    assert determinant([[matrix[i][j] for j in block] for i in block]) == 21808934160


if __name__ == "__main__":
    main()
