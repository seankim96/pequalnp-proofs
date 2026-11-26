"""Exact pair-separation replay for third gates after OR(0,1), OR(3,9)."""
from collections import Counter
from functools import lru_cache
from itertools import combinations, combinations_with_replacement, product
from math import comb

from order3_prefix_search import representatives, test_rows


def base_row(raw):
    return raw | (((raw | raw >> 1) & 1) << 26) | ((((raw >> 3) | (raw >> 9)) & 1) << 27)


def choose_family(neighbors):
    available = (1 << len(neighbors)) - 1
    selected = []
    while available:
        candidates = (i for i in range(len(neighbors)) if (available >> i) & 1)
        v = min(candidates, key=lambda i: (available & neighbors[i]).bit_count())
        selected.append(v)
        available &= ~((1 << v) | neighbors[v])
    return sorted(selected)


def check():
    assert representatives()[35] == ((False, 0, 1), (False, 3, 9))
    tests = [(base_row(row), expected) for row, expected in test_rows()]
    positives = [r for r, label in tests if label]
    negatives = [r for r, label in tests if not label]
    all_flags = (1 << len(positives)) - 1
    columns = [sum(1 << i for i, (r, _) in enumerate(tests) if (r >> j) & 1)
               for j in range(28)]
    # Duplicate columns retain the old witnesses on all rows. For other ANDs
    # retain witnesses on which the new gate is zero.
    masks = Counter()
    duplicate = 0
    for a, b in product(columns, repeat=2):
        out = a & b
        if out in columns:
            duplicate += 1
            masks[0] += 1
        else:
            masks[out & all_flags] += 1
    bound = max(mask.bit_count() for mask in masks)
    weak = []
    for i, j in combinations(range(len(negatives)), 2):
        union = negatives[i] | negatives[j]
        flags = sum(1 << k for k, row in enumerate(positives) if (row & ~union) == 0)
        if flags.bit_count() <= bound:
            weak.append((i, j, flags))
    neg_family_sizes = {}
    for mask in masks:
        conflicts = [0] * len(negatives)
        for i, j, flags in weak:
            if (flags & ~mask) == 0:
                conflicts[i] |= 1 << j
                conflicts[j] |= 1 << i
        selected = choose_family(conflicts)
        assert all((conflicts[i] >> j) & 1 == 0 for i, j in combinations(selected, 2))
        neg_family_sizes[mask] = len(selected)

    # Any AND preserves a negative witness dominating the intersection
    # of the two extended positive rows.
    conflicts = [0] * len(positives)
    for i, j in combinations(range(len(positives)), 2):
        common = positives[i] & positives[j]
        if not any((common & ~r) == 0 for r in negatives):
            conflicts[i] |= 1 << j
            conflicts[j] |= 1 << i
    pos_family = choose_family(conflicts)
    print("ordered third ANDs", sum(masks.values()), "duplicates", duplicate,
          "positive exclusion sizes", [(k, sum(v for m, v in masks.items() if m.bit_count() == k))
                                      for k in range(bound + 1)])
    print("exclusion masks", len(masks), "negative family sizes",
          min(neg_family_sizes.values()), max(neg_family_sizes.values()),
          "positive family", len(pos_family))
    assert min(neg_family_sizes.values()) >= 257 and len(pos_family) >= 33
    return masks, neg_family_sizes, pos_family


def check_fourth():
    tests = [(base_row(row), flag) for row, flag in test_rows()]
    pos = [r for r, flag in tests if flag]
    neg = [r for r, flag in tests if not flag]
    flags = (1 << len(pos)) - 1
    columns = [sum(1 << i for i, (r, _) in enumerate(tests) if r >> k & 1) for k in range(28)]

    @lru_cache(maxsize=None)
    def exceptions(signal):
        inherited = 0
        for baseline in columns:
            if (baseline & ~signal) == 0:
                inherited |= baseline
        return (signal & flags) & ~inherited

    def outputs(wires):
        for a, b in combinations_with_replacement(range(len(wires)), 2):
            weight = 1 if a == b else 2
            yield wires[a] & wires[b], weight, ("AND", a, b)
            yield wires[a] | wires[b], weight, ("OR", a, b)

    # Keep multiplicities for physical wire selections, even when two signals coincide.
    third_counts = Counter()
    third_example = {}
    for signal, weight, gate in outputs(columns):
        third_counts[signal] += weight
        third_example.setdefault(signal, gate)
    distribution = Counter()
    example = {}
    for third, count in third_counts.items():
        first_mask = exceptions(third)
        for fourth, weight, gate in outputs([*columns, third]):
            removed = first_mask | exceptions(fourth)
            distribution[removed] += weight * count
            example.setdefault(removed, (third_example[third], gate))
    assert sum(distribution.values()) == (2 * 28**2) * (2 * 29**2)

    max_size = max(mask.bit_count() for mask in distribution)
    high, low = {}, {}
    multiplicity = Counter()
    for i, j in combinations(range(len(neg)), 2):
        union = neg[i] | neg[j]
        mask = sum(1 << k for k, r in enumerate(pos) if (r & ~union) == 0)
        if mask.bit_count() <= 5:
            multiplicity[mask] += 1
        if mask.bit_count() <= max_size:
            high[mask] = high.get(mask, 0) | (1 << j)
            low[mask] = low.get(mask, 0) | (1 << i)
    maxima = [max((count for mask, count in multiplicity.items() if mask.bit_count() == k),
                  default=0) for k in range(6)]
    assert maxima == [0, 18, 4, 3, 2, 1]
    # For any five excluded flags, at most this many pairs lose all witnesses.
    # Discard one endpoint per failed pair to leave a separated family.
    loss = sum(comb(5, k) * maximum for k, maximum in enumerate(maxima))
    assert loss == 171
    print("uniform five-flag deletion: at most", loss, "bad pairs, at least", len(neg) - loss, "rows")
    sizes = {}
    for removed in distribution:
        sub = removed
        hi = lo = 0
        while True:
            hi |= high.get(sub, 0)
            lo |= low.get(sub, 0)
            if sub == 0:
                break
            sub = (sub - 1) & removed
        discarded = min((hi, lo), key=int.bit_count)
        sizes[removed] = (len(neg) - discarded.bit_count(), discarded)

    worst = min(sizes, key=lambda m: (sizes[m][0], m))
    size, discarded = sizes[worst]
    assert size >= 257
    selected = [i for i in range(len(neg)) if not (discarded >> i) & 1][:257]
    # Recompute the two physical gate outputs for the extremal example, then verify
    # positive containment on every one of the 32,896 pairs without exclusion masks.
    def extend(row):
        for index, (op, a, b) in enumerate(example[worst], start=28):
            x, y = (row >> a) & 1, (row >> b) & 1
            row |= ((x & y) if op == "AND" else (x | y)) << index
        return row
    p_ext = [extend(r) for r in pos]
    n_ext = [extend(neg[i]) for i in selected]
    for x, y in combinations(n_ext, 2):
        assert any((p & ~(x | y)) == 0 for p in p_ext)
    print("ordered third/fourth gates", sum(distribution.values()), "exception masks", len(distribution))
    print("exception sizes", [(k, sum(v for m, v in distribution.items() if m.bit_count() == k))
                               for k in range(max_size + 1)])
    print("minimum retained negatives", size, "worst mask", hex(worst), "example", example[worst])
    print("independently checked 32896 pairs on the extremal 30-wire prefix")


if __name__ == "__main__":
    check()
    check_fourth()
