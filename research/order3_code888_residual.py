"""Replay the 125 immediate fifth AND cases outside the nine-flag certificate."""
from collections import Counter
from itertools import combinations

from order3_code888_fifth import start, test_rows
from order3_robust_flag_families import bad_pairs, select


NINE_FLAGS = 0x1604E3
# Within each mask, one positive at a time may be lost.
SINGLETON_GROUPS = (0xF5048FF40F800, 0xAFB700A9031C)


def main():
    tests = [(start(x), y) for x, y in test_rows()]
    positives = [x for x, y in tests if y]
    negatives = [x for x, y in tests if not y]
    positive_rows = sum(1 << i for i, (_, label) in enumerate(tests) if label)
    assert positive_rows == (1 << 52) - 1 and len(negatives) == 468
    columns = [sum((row >> w & 1) << i for i, (row, _) in enumerate(tests)) for w in range(30)]
    residual = [a & b for a in columns for b in columns if (a & b & positive_rows) & ~NINE_FLAGS]
    singletons = [x & positive_rows for x in residual if x not in columns]
    assert len(residual) == 125 and len(residual) - len(singletons) == 31
    assert all(x.bit_count() == 1 for x in singletons)
    assert len(singletons) == 94 and len(set(singletons)) == 43

    buckets = bad_pairs(positives, negatives)
    counts = Counter(singletons)
    seen = set()
    for group in SINGLETON_GROUPS:
        selected = select(buckets, group)
        assert len(selected) >= 257
        for i, j in combinations(selected[:257], 2):
            union = negatives[i] | negatives[j]
            witness = sum(1 << p for p, word in enumerate(positives) if word & ~union == 0)
            assert witness and (witness.bit_count() >= 2 or witness & group == 0)
        active = {x for x in counts if x & group}
        assert seen.isdisjoint(active)
        seen.update(active)
        print(f"{group:#x}: {len(selected)} negatives, {len(active)} flags, "
              f"{sum(counts[x] for x in active)} ordered AND codes")
    assert seen == set(singletons)
    print("31 identity codes on all 520 tests; 94 singleton codes; 65,792 pair checks")


if __name__ == "__main__":
    main()
