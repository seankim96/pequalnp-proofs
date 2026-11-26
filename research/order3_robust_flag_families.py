"""Reproduce the two negative-row certificates for case 6 after AND(1,13)."""
from order3_and_pair_certificates import prefix
from order3_prefix_search import test_rows

GROUPS = (0xA240D46448500, 0x4CAF2A9AA6800)


def bad_pairs(positives, negatives):
    """For each negative i, bit j marks a pair lacking a surviving positive witness."""
    # Buckets 0..51 hold uniquely witnessed pairs. Bucket 52 holds unwitnessed pairs.
    buckets = [[0] * len(negatives) for _ in range(len(positives) + 1)]
    for j, right in enumerate(negatives):
        for i, left in enumerate(negatives[:j]):
            union = left | right
            witness = len(positives)
            for index, row in enumerate(positives):
                if row & ~union:
                    continue
                if witness != len(positives):
                    break  # At least two witnesses: deleting one flag is harmless.
                witness = index
            else:
                buckets[witness][i] |= 1 << j
                buckets[witness][j] |= 1 << i
    return buckets


def select(buckets, group):
    conflicts = buckets[-1].copy()
    for flag, rows in enumerate(buckets[:-1]):
        if group >> flag & 1:
            conflicts = [a | b for a, b in zip(conflicts, rows)]
    available = (1 << len(conflicts)) - 1
    chosen = []
    while available:
        candidates = (i for i in range(len(conflicts)) if available >> i & 1)
        best = min(candidates, key=lambda i: (conflicts[i] & available).bit_count())
        chosen.append(best)
        available &= ~((1 << best) | conflicts[best])
    return sorted(chosen)


def main():
    rows = test_rows()
    positives = [prefix(r) for r, label in rows if label]
    negatives = [prefix(r) for r, label in rows if not label]
    buckets = bad_pairs(positives, negatives)
    for group, expected in zip(GROUPS, (294, 265)):
        chosen = select(buckets, group)
        assert len(chosen) == expected
        # Independent replay of the exact 257 rows used in Lean.
        for j, right in enumerate(chosen[:257]):
            for left in chosen[:j]:
                union = negatives[right] | negatives[left]
                mask = sum(1 << i for i, p in enumerate(positives) if not (p & ~union))
                assert mask & ~group or mask.bit_count() >= 2
        print(f"group {group:#x}: {len(chosen)} selected; 32,896 witness pairs verified")


if __name__ == "__main__":
    main()
