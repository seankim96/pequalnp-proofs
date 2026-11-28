"""Replay the necessary operand constraints for nine nontrivial ANDs on the 468 negatives.

The formal pattern bound lives in PlaneNineAndOperands. Search the first three
AND gates in topological order, allowing arbitrarily many intervening ORs.
With --symmetry, enumerate each orbit of the first unordered operand pair once.
"""
import argparse
from collections import Counter
from itertools import combinations
from time import monotonic

from order3_prefix_search import test_rows


def symmetries(rows):
    permutations = []
    row_set = set(rows)
    for multiplier in (1, 3, 9):
        for offset in range(13):
            for dual in (False, True):
                sign = -1 if dual else 1
                perm = [13 * ((i // 13) ^ dual) + (sign * (multiplier * (i % 13) + offset)) % 13
                        for i in range(26)]
                images = {sum(1 << perm[i] for i in range(26) if row >> i & 1) for row in rows}
                if images != row_set:
                    raise ValueError("permutation does not preserve the negative family")
                permutations.append(perm)
    return permutations


def first_cases(supports, permutations):
    pairs = combinations(sorted(supports), 2)
    if not permutations:
        for pair in pairs:
            yield pair, 1
        return
    unseen = set(pairs)
    while unseen:
        representative = min(unseen)
        orbit = {tuple(sorted(tuple(sorted(perm[i] for i in support)) for support in representative))
                 for perm in permutations}
        if not orbit <= unseen:
            raise ValueError("first-operand orbits overlap")
        unseen.difference_update(orbit)
        yield representative, len(orbit)


def extend_pool(pool, product):
    # Every OR of raw wires and earlier products either omits the newest
    # product or adds it to a previously available OR. OR cannot lower weight.
    return pool | {value | product for value in pool if (value | product).bit_count() <= 256}


def split_cells(cells, x, y, universe):
    # Select either endpoint, and either Boolean value, at this gate.
    return {cell & value for cell in cells for value in (x, y, universe ^ x, universe ^ y)}


def viable(pool, cells, limit):
    counts = [(cell, cell.bit_count()) for cell in cells]
    return [value for value in pool if 212 <= value.bit_count() <= 256 and
            all(size - limit <= (value & cell).bit_count() <= limit for cell, size in counts)]


def main(use_symmetry):
    start = monotonic()
    rows = [row for row, positive in test_rows() if not positive]
    universe = (1 << len(rows)) - 1
    primary = [sum(1 << j for j, row in enumerate(rows) if row >> i & 1) for i in range(26)]
    min_triple = min((x | y | z).bit_count() for x, y, z in combinations(primary, 3))
    if min_triple <= 256 or any(value.bit_count() >= 212 for value in primary):
        raise ValueError("primary-support reduction does not apply")
    # A true constant exceeds the weight bound; a false constant is included.
    raw = {0, *primary, *(x | y for x, y in combinations(primary, 2))}
    raw = {value for value in raw if value.bit_count() <= 256}
    supports = {(i, j): primary[i] | primary[j] for i, j in combinations(range(26), 2)
                if 212 <= (primary[i] | primary[j]).bit_count() <= 256}
    if len(supports) != len(set(supports.values())):
        raise ValueError("duplicate eligible primary OR")
    permutations = symmetries(rows) if use_symmetry else []
    cases = 0
    first_count = second_count = third_inputs = 0
    histogram = Counter()
    for (left, right), multiplicity in first_cases(supports, permutations):
        cases += 1
        x, y = supports[left], supports[right]
        first = x & y
        # If the AND equals one operand on all negatives, rewiring the gate to
        # this operand preserves those rows and can only increase positive rows.
        # That would give a correct circuit with at most eight nontrivial ANDs.
        if first in (x, y):
            continue
        first_count += multiplicity
        first_cells = split_cells({universe}, x, y, universe)
        first_pool = extend_pool(raw, first)
        eligible = viable(first_pool, first_cells, 128)
        histogram[len(eligible)] += multiplicity
        for u, v in combinations(eligible, 2):
            second = u & v
            if second in (u, v):
                continue
            second_count += multiplicity
            cells = split_cells(first_cells, u, v, universe)
            third_inputs += multiplicity * len(viable(extend_pool(first_pool, second), cells, 64))
    print("negative rows, minimum three-raw OR weight, eligible two-raw ORs:",
          len(rows), min_triple, len(supports))
    print("first representatives, first pairs, second pairs, eligible third operands:",
          cases, first_count, second_count, third_inputs)
    print("first pairs by number of eligible second operands:", dict(sorted(histogram.items())))
    print("seconds:", round(monotonic() - start, 2))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--symmetry", action="store_true", help="use the 78 checked row permutations")
    main(parser.parse_args().symmetry)
