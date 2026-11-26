"""Run with the compiled plane_raw_deletion_scan.cpp executable as argv[1]."""
import subprocess
import sys
from collections import Counter
from itertools import combinations
from pathlib import Path

from order3_prefix_search import test_rows


def submasks(mask):
    sub = mask
    while True:
        yield sub
        if not sub:
            return
        sub = (sub - 1) & mask


def main(scanner):
    positives = [x for x, y in test_rows() if y]
    negatives = [x for x, y in test_rows() if not y]
    assert len(positives) == 52 and len(negatives) == 468
    weights = Counter()
    ends = {}
    for i, j in combinations(range(468), 2):
        union = negatives[i] | negatives[j]
        witness = sum(1 << k for k, p in enumerate(positives) if not p & ~union)
        weights[witness] += 1
        if witness.bit_count() <= 7:
            low, high = ends.get(witness, (0, 0))
            ends[witness] = low | 1 << i, high | 1 << j
    assert weights[0] == 0 and sum(weights.values()) == 109278
    maxima = [max(n for m, n in weights.items() if m.bit_count() == k) for k in range(1, 6)]
    assert maxima == [18, 4, 3, 2, 1]
    print('per-exact-mask multiplicity maxima for sizes 1..5:', maxima)
    data = ''.join(f'{mask} {n}\n' for mask, n in weights.items())
    for size in (5, 6, 7):
        run = subprocess.run([scanner, str(size)], input=data, capture_output=True, text=True, check=True)
        k, cases, maximum, example, exceptional, aggregate = run.stderr.split()
        worst_mask = int(example, 16)
        # Independent direct pair replay of a maximizing mask, using raw input words.
        allowed = [p for i, p in enumerate(positives) if not worst_mask >> i & 1]
        bad = sum(not any(p & ~(negatives[i] | negatives[j]) == 0 for p in allowed)
                  for i, j in combinations(range(468), 2))
        assert bad == int(maximum) and len(run.stdout.splitlines()) == int(exceptional)
        worst_endpoints = 0
        for line in run.stdout.splitlines():
            mask, count = line.split()
            mask = int(mask, 16)
            low = high = pair_count = 0
            for sub in submasks(mask):
                l, h = ends.get(sub, (0, 0))
                low |= l
                high |= h
                pair_count += weights[sub]
            assert pair_count == int(count) and mask.bit_count() == size
            worst_endpoints = max(worst_endpoints, min(low.bit_count(), high.bit_count()))
        upper = max(min(211, int(maximum)), worst_endpoints)
        print(k, cases, maximum, example, exceptional, aggregate,
              'over-budget endpoint maximum', worst_endpoints, 'guaranteed survivors', 468 - upper)
        assert 468 - upper >= 257


if __name__ == '__main__':
    main(Path(sys.argv[1]).resolve())
