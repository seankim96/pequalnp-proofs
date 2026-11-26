"""Check the next case with the two four-exception ANDs fixed in either order."""
from collections import Counter
from itertools import combinations

from order3_case35_fifth_15_17 import prefix
from order3_prefix_search import test_rows


def replay():
    rows = test_rows()
    positive = [prefix(r) for r, yes in rows if yes]
    negative = [prefix(r) for r, yes in rows if not yes]
    cols = [sum(1 << i for i, (r, _) in enumerate(rows) if prefix(r) >> j & 1)
            for j in range(30)]
    x, y = cols[13] & cols[26], cols[13] & cols[27]
    positives = (1 << 52) - 1
    assert x & positives == 3 and y & positives == 12
    outside = positives ^ 15
    sizes = Counter()
    for first, second in ((x, y), (y, x)):
        pool = cols + [first, second]
        for a in pool:
            for b in pool:
                for wire in (a & b, a | b):
                    missing = wire & outside
                    for parent in cols:
                        if not parent & ~wire:
                            missing &= ~parent
                    sizes[missing.bit_count()] += 1
    assert sizes == {0: 3856, 1: 240}
    higher = {}
    for i, j in combinations(range(468), 2):
        union = negative[i] | negative[j]
        witnesses = sum(1 << p for p in range(4, 52) if not positive[p] & ~union)
        if witnesses.bit_count() <= 2:
            higher[witnesses] = higher.get(witnesses, 0) | (1 << j)
    permanent = higher.get(0, 0)
    single = [permanent | higher.get(1 << p, 0) for p in range(4, 52)]
    one_loss = max(m.bit_count() for m in single)
    two_loss = max((single[p-4] | single[q-4] | higher.get((1 << p) | (1 << q), 0)).bit_count()
                   for p, q in combinations(range(4, 52), 2))
    assert 468 - two_loss >= 257
    print(f"Ordered seventh-gate choices by further exceptions: {dict(sorted(sizes.items()))}.")
    print(f"Omitting flags 0–3 costs {permanent.bit_count()} higher endpoints.")
    print(f"With one or two further omitted flags: at worst {one_loss} or {two_loss} lost, "
          f"leaving {468-one_loss} or {468-two_loss} negatives.")


if __name__ == "__main__":
    replay()
