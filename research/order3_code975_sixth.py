"""Replay the sixth-gate separation calculation after case 6, fourth 888, fifth 975.

The 31 physical operand wires are indexed 0..30. The order of all 520 rows
comes from the existing plane test generator. No SAT solver is used.
"""
from itertools import combinations

from order3_code888_fifth import start, test_rows
from order3_robust_flag_families import bad_pairs, select


GROUPS = (0x1FFFF, 0x1FFFE0000, 0x7FFE00000000, 0xF800000000000)


def main():
    rows = [(start(row) | (((row >> 2) & (row >> 15) & 1) << 30), label)
            for row, label in test_rows()]
    positives = [row for row, label in rows if label]
    negatives = [row for row, label in rows if not label]
    flags = (1 << len(positives)) - 1
    assert (len(positives), len(negatives)) == (52, 468)
    assert sum(1 << i for i, (_, on) in enumerate(rows) if on) == flags

    columns = [sum(1 << i for i, (row, _) in enumerate(rows) if row >> w & 1)
               for w in range(31)]
    counts = [0, 0, 0]
    for left in columns:
        for right in columns:
            wire = left & right
            support = wire & flags
            if wire in columns:
                counts[0] += 1
            elif not support:
                counts[1] += 1
            else:
                assert support.bit_count() == 1
                counts[2] += 1
    assert counts == [61, 788, 112]
    print("ordered sixth ANDs: 61 duplicate columns, 788 further zero-positive, 112 further singleton")

    buckets = bad_pairs(positives, negatives)
    conflicts = buckets[-1]
    assert sum(bits.bit_count() for bits in conflicts) == 2 * 85
    degree_counts = [sum(bits.bit_count() == d for bits in conflicts) for d in range(4)]
    assert degree_counts == [336, 98, 30, 4]
    covered = 0
    for group, expected in zip(GROUPS, (258, 257, 260, 309), strict=True):
        assert not covered & group
        covered |= group
        selected = select(buckets, group)
        assert len(selected) == expected
        for i, j in combinations(selected[:257], 2):
            union = negatives[i] | negatives[j]
            witnesses = sum(1 << k for k, p in enumerate(positives) if p & ~union == 0)
            assert witnesses and (witnesses.bit_count() >= 2 or witnesses & group == 0)
        print(f"{group:#x}: {group.bit_count()} flags, {len(selected)} selected, 32896 pairs")
    assert covered == flags
    print("all 52 single deletions covered; 131584 pair checks")


if __name__ == "__main__":
    main()
