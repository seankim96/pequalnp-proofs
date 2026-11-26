"""Replay a nine-AND suffix certificate after code 975, one OR, and one AND."""
from collections import Counter
from functools import cache
from itertools import combinations

from order3_code888_fifth import start, test_rows


def main():
    rows = [start(x) | ((x >> 2 & x >> 15 & 1) << 30) for x, _ in test_rows()]
    positives, negatives = rows[:52], rows[52:]
    assert len(negatives) == 468 and all(y == (i < 52) for i, (_, y) in enumerate(test_rows()))
    cols = tuple(sum(1 << i for i, r in enumerate(rows) if r >> w & 1) for w in range(31))
    positives_mask = (1 << 52) - 1

    @cache
    def exception_mask(signal):
        inherited = 0
        for col in cols:
            if col & ~signal == 0:
                inherited |= col
        return signal & ~inherited & positives_mask

    counts = Counter()
    reading_new = Counter()
    for left in cols:
        for right in cols:
            extended = (*cols, left | right)
            for i, a in enumerate(extended):
                for j, b in enumerate(extended):
                    mask = exception_mask(a & b)
                    counts[mask] += 1
                    if i == 31 or j == 31:
                        reading_new[mask.bit_count()] += 1
    assert sum(counts.values()) == 31**2 * 32**2
    assert max(mask.bit_count() for mask in counts) <= 2

    # A pair fails when every positive witness belongs to the exceptional subset.
    # Store both endpoints of every such pair, grouped by its full witness mask.
    endpoints = {}
    for i, j in combinations(range(468), 2):
        union = negatives[i] | negatives[j]
        mask = sum(1 << k for k, p in enumerate(positives) if p & ~union == 0)
        if mask.bit_count() <= 2:
            low, high = endpoints.get(mask, (0, 0))
            endpoints[mask] = (low | 1 << i, high | 1 << j)
    worst = 468
    worst_mask = None
    for exc in counts:
        lo = hi = 0
        for mask, (low, high) in endpoints.items():
            if mask & ~exc == 0:
                lo |= low
                hi |= high
        survive = 468 - min(lo.bit_count(), hi.bit_count())
        if survive < worst:
            worst, worst_mask = survive, exc
    assert worst >= 257
    distribution = Counter()
    for exc, n in counts.items():
        distribution[exc.bit_count()] += n
    print("ordered cases", sum(counts.values()), "distinct masks", len(counts))
    print("by exceptional positive count", sorted(distribution.items()))
    assert sum(reading_new.values()) == 31**2 * 63
    print("reading the sixth OR", sorted(reading_new.items()))
    print("minimum surviving negatives", worst, "one worst mask", hex(worst_mask))
    # Replay the worst mask independently without endpoint buckets.
    retained = [p for k, p in enumerate(positives) if not worst_mask >> k & 1]
    bad = [(i, j) for i, j in combinations(range(468), 2)
           if not any(p & ~(negatives[i] | negatives[j]) == 0 for p in retained)]
    assert 468 - min(len({i for i, _ in bad}), len({j for _, j in bad})) == worst


if __name__ == "__main__":
    main()
