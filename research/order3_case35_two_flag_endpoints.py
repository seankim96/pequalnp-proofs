"""Bound discarded negatives for every possible pair of exceptional positives."""
from collections import Counter
from itertools import combinations

from order3_case35_fifth_15_17 import prefix
from order3_prefix_search import test_rows


def replay():
    rows = test_rows()
    pos = [prefix(row) for row, label in rows if label]
    neg = [prefix(row) for row, label in rows if not label]
    assert len(pos) == 52 and len(neg) == 468
    # An OR always inherits a positive from a parent. For an AND we can also
    # use a parent when the AND equals that parent on all 520 tests.
    cols = [sum(1 << i for i, (r, _) in enumerate(rows) if prefix(r) >> j & 1)
            for j in range(30)]
    cases = Counter()
    for x in cols:
        for y in cols:
            signal = x & y
            if signal == x or signal == y:
                cases['equals a parent'] += 1
            else:
                count = (signal & ((1 << 52) - 1)).bit_count()
                assert count <= 2
                cases[count] += 1
    print('ordered fifth ANDs equal to a parent on all rows:', cases['equals a parent'])
    print('other fifth ANDs with 0, 1, 2 positive rows:', [cases[k] for k in range(3)])
    higher = {}
    for a, b in combinations(range(len(neg)), 2):
        union = neg[a] | neg[b]
        flags = 0
        for p, w in enumerate(pos):
            if not w & ~union:
                flags |= 1 << p
                if flags.bit_count() > 2:
                    break
        if flags.bit_count() <= 2:
            higher[flags] = higher.get(flags, 0) | (1 << b)
    costs = [max(h.bit_count() for m, h in higher.items() if m.bit_count() == k)
             for k in range(3)]
    print('max higher endpoints at witness-mask sizes 0, 1, 2:', costs)
    worst = 0
    pairs = []
    for a, b in combinations(range(52), 2):
        x, y = 1 << a, 1 << b
        dropped = (higher.get(0, 0) | higher.get(x, 0) | higher.get(y, 0)
                   | higher.get(x | y, 0)).bit_count()
        if dropped > worst:
            worst, pairs = dropped, []
        if dropped == worst:
            pairs.append((a, b))
    assert 468 - worst >= 257
    print('maximum discarded over all 1326 two-flag masks:', worst)
    print('minimum retained:', 468 - worst, 'first worst pair:', pairs[0])


if __name__ == '__main__':
    replay()
