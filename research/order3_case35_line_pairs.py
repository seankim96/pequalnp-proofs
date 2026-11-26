"""Transport the two-line negative separation certificate through all 78 line pairs."""
from itertools import combinations

from order3_case35_third import base_row, choose_family
from order3_case5_orbits import move
from order3_prefix_search import test_rows


def check():
    rows = test_rows()
    pos = [r for r, y in rows if y]
    neg = [r for r, y in rows if not y]
    assert all(p.bit_length() - 14 == i // 4 for i, p in enumerate(pos))
    conflicts = [0] * len(neg)
    for i, j in combinations(range(len(neg)), 2):
        if not any(p & ~(neg[i] | neg[j]) == 0 for p in pos[8:]):
            conflicts[i] |= 1 << j
            conflicts[j] |= 1 << i
    family = choose_family(conflicts)
    assert len(family) == 306
    source = [neg[i] for i in family[:257]]
    pairs = [(i, j, next(k for k in range(8, 52) if pos[k] & ~(a | b) == 0))
             for (i, a), (j, b) in combinations(enumerate(source), 2)]
    # The second permutation moves lines (0,1) into the other affine orbit.
    other = (0, 1, 7, 3, 11, 10, 2, 6, 4, 9, 12, 8, 5,
             13, 24, 20, 15, 23, 14, 19, 16, 21, 22, 25, 18, 17)
    labels = dict(rows)
    seen = set()
    for initial in (tuple(range(26)), other):
        for m in (1, 3, 9):
            for offset in range(13):
                perm = tuple((i // 13) * 13 + (m * (i % 13) + offset) % 13 for i in initial)
                assert sorted(perm) == list(range(26))
                assert all(labels.get(move(r, perm)) == y for r, y in rows)
                lines = tuple(sorted(perm[t] - 13 for t in (13, 14)))
                assert lines not in seen
                seen.add(lines)
                positive = [base_row(move(r, perm)) for r in pos]
                negative = [base_row(move(r, perm)) for r in source]
                blocked = sum(1 << (13 + line) for line in lines)
                assert all(p & blocked == 0 for p in positive[8:])
                # Re-evaluate the *original* baseline OR gates after relabeling.
                assert all(positive[k] & ~(negative[i] | negative[j]) == 0 for i, j, k in pairs)
    assert seen == set(combinations(range(13), 2))
    print(len(seen), "distinct line pairs;", len(pairs), "witnesses per pair;",
          len(seen) * len(pairs), "checks on the 28 original baseline wires")


if __name__ == "__main__":
    check()
