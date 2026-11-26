"""Enumerate fifth/sixth exceptions relative to the actual 30 case-35 wires."""
from collections import Counter
from functools import cache
from itertools import combinations, combinations_with_replacement
from math import comb

from order3_case35_fifth_15_17 import prefix
from order3_prefix_search import test_rows


def gates(wires):
    outputs = Counter()
    for i, j in combinations_with_replacement(range(len(wires)), 2):
        x, y = wires[i], wires[j]
        ordered = 1 + (i != j)
        outputs[x & y] += ordered
        outputs[x | y] += ordered
    return outputs


def replay():
    rows = test_rows()
    pos = [prefix(r) for r, y in rows if y]
    neg = [prefix(r) for r, y in rows if not y]
    cols = [sum(1 << i for i, (r, _) in enumerate(rows) if prefix(r) >> j & 1)
            for j in range(30)]
    pm = (1 << len(pos)) - 1

    @cache
    def missing(signal):
        inherited = 0
        for parent in cols:
            if not parent & ~signal:
                inherited |= parent
        return signal & pm & ~inherited

    weights = Counter()
    for f, count in gates(cols).items():
        for g, more in gates([*cols, f]).items():
            m = missing(g)
            if not f & ~g:
                m &= ~f
            weights[missing(f) | m] += count * more
    assert sum(weights.values()) == 1800 * 1922
    by_size = Counter()
    for m, count in weights.items():
        by_size[m.bit_count()] += count
    print('ordered extensions by number of exceptional flags:', sorted(by_size.items()))
    limit = max(by_size)
    higher = {}
    for i, j in combinations(range(468), 2):
        u = neg[i] | neg[j]
        witness = sum(1 << p for p, w in enumerate(pos) if not w & ~u)
        if witness.bit_count() <= limit:
            higher[witness] = higher.get(witness, 0) | (1 << j)
    caps = [max((v.bit_count() for m, v in higher.items() if m.bit_count() == k), default=0)
            for k in range(limit + 1)]
    print('endpoint caps for exact witness masks:', caps)
    print('uniform discard bound from caps:', sum(comb(limit, k)*b for k, b in enumerate(caps)))
    worst = 0
    for mask in weights:
        sub = mask
        lost = 0
        while True:
            lost |= higher.get(sub, 0)
            if not sub:
                break
            sub = (sub-1) & mask
        worst = max(worst, lost.bit_count())
    assert 468-worst >= 257
    print('distinct exception masks:', len(weights), 'maximum discarded:', worst,
          'minimum retained:', 468-worst)


if __name__ == '__main__':
    replay()
