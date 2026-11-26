"""Exhaust the fifth gate after OR(0,1), OR(3,9), AND(15,27), AND(17,26)."""
from collections import Counter
from itertools import combinations, combinations_with_replacement
from order3_case35_third import base_row, choose_family
from order3_prefix_search import test_rows
from order3_case35_or_slices import CUTS


def prefix(row):
    row = base_row(row)
    for left, right, out in [(15, 27, 28), (17, 26, 29)]:
        row |= (((row >> left) & (row >> right)) & 1) << out
    return row


def replay():
    rows = test_rows()
    positives = [prefix(r) for r, y in rows if y]
    negatives = [prefix(r) for r, y in rows if not y]
    columns = [sum(1 << i for i, (r, _) in enumerate(rows) if prefix(r) & (1 << j))
               for j in range(30)]
    pos_mask = (1 << 52) - 1
    missing = Counter()
    slices = Counter()
    cuts = [(1 << (52 + n), mask) for n, mask in CUTS
            if all(col & (1 << (52 + n)) or (col & mask).bit_count() <= 1 for col in columns)]
    for a, b in combinations_with_replacement(range(30), 2):
        for out in (columns[a] & columns[b], columns[a] | columns[b]):
            weight = 1 + (a != b)
            inherited = 0
            for c in columns:
                if not c & ~out:
                    inherited |= c
            missing[out & pos_mask & ~inherited] += weight
            # At most one selected flag may survive on a negative-rejecting wire.
            best = max(19 if out & n else 19-max(0, (out & flags).bit_count()-1)
                       for n, flags in cuts)
            slices[best] += weight
    # All pair witnesses are computed on the actual 30 prefix wires.
    weak = []
    limit = max(m.bit_count() for m in missing)
    for i, j in combinations(range(468), 2):
        union = negatives[i] | negatives[j]
        witnesses = sum(1 << k for k, p in enumerate(positives) if not p & ~union)
        if witnesses.bit_count() <= limit:
            weak.append((i, j, witnesses))
    sizes = []
    for mask in missing:
        graph = [0] * 468
        for i, j, witnesses in weak:
            if not witnesses & ~mask:
                graph[i] |= 1 << j
                graph[j] |= 1 << i
        selected = choose_family(graph)
        assert all(not (graph[i] & (1 << j)) for i, j in combinations(selected, 2))
        sizes.append(len(selected))
    assert sum(missing.values()) == 1800 and min(sizes) >= 257
    print("exception masks", len(missing), "max flags", limit, "retained negatives",
          min(sizes), max(sizes), "positive slice sizes", sorted(slices.items()))


if __name__ == "__main__":
    replay()
