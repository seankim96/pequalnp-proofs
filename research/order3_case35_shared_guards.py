"""Replay the high-positive separation certificate for shared OR guards in case 35."""
import argparse
import json
from itertools import combinations_with_replacement
from pathlib import Path
import re

import numpy as np

from order3_case35_fifth_15_17 import prefix
from order3_prefix_search import CASE35_GUARDS, test_rows


def retain(witnesses):
    bad = witnesses == 0
    np.fill_diagonal(bad, False)
    degree = bad.sum(axis=0).astype(int)
    live = np.ones(len(degree), dtype=bool)
    while degree.max() > 0:
        i = degree.argmax()
        live[i] = False
        degree -= bad[i]
        degree[i] = -len(live) - 1
    assert not bad[np.ix_(live, live)].any()
    return list(map(int, np.nonzero(live)[0]))


def main(all_omissions=False):
    words = [prefix(x) for x, _ in test_rows()]
    fixed = np.array([x | (int(bool(x & 1 << 13 and x & 1 << 26)) << 30)
                        | (int(bool(x & 1 << 13 and x & 1 << 27)) << 31) for x in words],
                     dtype=np.uint64)
    pos, neg = fixed[4:52], fixed[52:]
    assert len(pos) == 48 and len(neg) == 468
    union = np.bitwise_or.outer(neg, neg)
    base = np.zeros(union.shape, dtype=np.uint64)
    for p, x in enumerate(pos):
        base |= ((union & x) == x).astype(np.uint64) << p

    def add_guard(witnesses, a, b):
        mask = 1 << a | 1 << b
        active = sum(1 << p for p, x in enumerate(pos.tolist()) if x & mask)
        on = (neg & mask) != 0
        # Witnesses active on this guard need both endpoints to be active.
        both = np.logical_and.outer(on, on)
        all_bits = np.uint64((1 << 48) - 1)
        return witnesses & np.where(both, all_bits, all_bits ^ np.uint64(active))

    counts = []
    for a, b in combinations_with_replacement(range(32), 2):
        counts.append(len(retain(add_guard(base, a, b))))
    assert len(counts) == 528 and min(counts) >= 257
    print("Single OR guard, 528 separate families, min/max retained:", min(counts), max(counts))
    if all_omissions:
        # Classify each pair by its witness count. Deleting bit i destroys a
        # witness set exactly when it was empty or was the singleton {i}.
        # Reuse the sparse edge lists for the 48 independent greedy searches.
        minimum, maximum, insufficient = 468, 0, []
        for a, b in combinations_with_replacement(range(32), 2):
            m = add_guard(base, a, b)
            singletons = (m != 0) & ((m & (m - np.uint64(1))) == 0)
            ii, jj = np.nonzero(np.triu(singletons, 1))
            lone = m[ii, jj]
            zero = m == 0
            for i in range(48):
                bad = zero.copy()
                take = lone == (1 << i)
                x, y = ii[take], jj[take]
                bad[x, y] = bad[y, x] = True
                kept = retain(~bad)
                if len(kept) < minimum:
                    minimum, worst = len(kept), (a, b, i + 4)
                maximum = max(maximum, len(kept))
                if len(kept) < 257:
                    insufficient.append((a, b, i + 4, len(kept)))
        print('All 25,344 single-root/single-omission trials:', minimum, maximum,
              'first minimum:', worst, 'below 257:', len(insufficient))
        if insufficient:
            print('First locations below 257:', insufficient[:12])
    joint = base
    for a, b in sorted(CASE35_GUARDS):
        joint = add_guard(joint, a, b)
    # Removing one high positive permits one additional exceptional product.
    # Keep the joint-menu and the single OR(2,26) experiments separate.
    for label, matrix in [('17-guard menu', joint), ('OR(2,26)', add_guard(base, 2, 26))]:
        sizes = [len(retain(matrix & np.uint64(((1 << 48) - 1) ^ (1 << i))))
                 for i in range(48)]
        # A common family with at least two distinct witnesses per pair can
        # withstand any one omitted flag without changing the family itself.
        redundant = retain(matrix & (matrix - np.uint64(1)))
        print(label, 'single family with two witnesses per pair:', len(redundant))
        small = [(i + 4, size) for i, size in enumerate(sizes) if size < 257]
        print(label, 'one additional omitted flag, min/max:', min(sizes), max(sizes),
              'below 257:', small)
    # Pack 48 possible single omissions into jointly tolerable blocks. Each
    # block has one reusable family and one bitmask for a kernel certificate.
    one_root = add_guard(base, 2, 26)
    blocks = []
    for flag in range(4, 52):
        bit = 1 << (flag - 4)
        for j, (omitted, _) in enumerate(blocks):
            mask = omitted | bit
            kept = retain(one_root & np.uint64(((1 << 48) - 1) ^ mask))
            if len(kept) >= 257:
                blocks[j] = mask, kept
                break
        else:
            kept = retain(one_root & np.uint64(((1 << 48) - 1) ^ bit))
            assert len(kept) >= 257
            blocks.append((bit, kept))
    assert sum(mask for mask, _ in blocks) == (1 << 48) - 1
    print('OR(2,26) omission blocks (flag mask, retained count):',
          [(hex(mask << 4), len(kept)) for mask, kept in blocks])
    # A partition into cliques of the bad-pair graph is an upper certificate:
    # a compatible family can use at most one endpoint per part.
    matrix = add_guard(base, 2, 23) & np.uint64(((1 << 48) - 1) ^ (1 << (10 - 4)))
    bad_pairs = matrix == 0
    np.fill_diagonal(bad_pairs, False)
    certificate = Path(__file__).with_name('results') / 'case35-guard-2-23-omit-10.json'
    evidence = json.loads(certificate.read_text())
    assert evidence['root'] == [2, 23] and evidence['omitted_high_flag'] == 10
    compatible = evidence['compatible_rows']
    classes = evidence['incompatible_partition']
    assert len(set(compatible)) == len(compatible) == len(classes) == 244
    assert all(0 <= i < 468 for i in compatible)
    assert not bad_pairs[np.ix_(compatible, compatible)].any()
    assert sorted(j for group in classes for j in group) == list(range(468))
    assert all(bad_pairs[i,j] for group in classes for i in group for j in group if i != j)
    print('OR(2,23) omitting flag 10: exact compatible-family maximum 244')
    keep = retain(joint)
    assert len(keep) == 260
    removed = ((1 << 468) - 1) ^ sum(1 << j for j in keep)
    src = Path(__file__).resolve().parents[1] / 'lean/PEqualNP/Research/PlaneCase35SharedGuardBudget.lean'
    match = re.search(r'private def removed : Nat := (0x[0-9a-f]+)', src.read_text())
    assert match and removed == int(match[1], 16)
    print("17 simultaneous guards, retained:", len(keep), "verified negative pairs:", len(keep)*(len(keep)-1)//2)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--all-omissions', action='store_true',
                        help='also replay every single root with every one of 48 omissions')
    main(parser.parse_args().all_omissions)
