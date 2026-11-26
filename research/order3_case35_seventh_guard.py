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
    sparse_pairs = []
    for i, j in combinations(range(468), 2):
        union = negative[i] | negative[j]
        witnesses = sum(1 << p for p in range(4, 52) if not positive[p] & ~union)
        if witnesses.bit_count() <= 5:
            sparse_pairs.append((i, j, witnesses))
            higher[witnesses] = higher.get(witnesses, 0) | (1 << j)
    permanent = higher.get(0, 0)
    print(f"Ordered seventh-gate choices by further exceptions: {dict(sorted(sizes.items()))}.")
    print(f"Omitting flags 0–3 costs {permanent.bit_count()} higher endpoints.")
    previous = {0: permanent}
    for k in range(1, 6):
        current = {}
        loss, worst, checked = -1, 0, 0
        below_threshold = []
        for flags in combinations(range(4, 52), k):
            mask = sum(1 << p for p in flags)
            endpoints = higher.get(mask, 0)
            # Every proper subset of mask is contained in an immediate predecessor.
            for p in flags:
                endpoints |= previous[mask ^ (1 << p)]
            if k < 5:
                current[mask] = endpoints
            checked += 1
            size = endpoints.bit_count()
            if len(negative) - size < 257:
                below_threshold.append(mask)
            if size > loss:
                loss, worst = size, mask
        if k <= 4:
            assert len(negative) - loss >= 257
        example = [p for p in range(4, 52) if worst >> p & 1]
        print(f"{k} further flags, {checked} masks: at most {loss} lost, "
              f"at least {len(negative)-loss} retained; worst example {example}.")
        if below_threshold:
            print(f"Higher-endpoint selection leaves fewer than 257 rows on {len(below_threshold)} masks.")
            losses = []
            for mask in below_threshold:
                # Each edge needs one endpoint removed. The higher-endpoint rule is optional.
                bad = [(i, j) for i, j, w in sparse_pairs if w & ~mask == 0]
                removed = set()
                while bad:
                    degree = Counter(i for edge in bad for i in edge)
                    vertex = min(degree, key=lambda i: (-degree[i], i))
                    removed.add(vertex)
                    bad = [(i, j) for i, j in bad if i != vertex and j != vertex]
                assert all(w & ~mask or i in removed or j in removed for i, j, w in sparse_pairs)
                losses.append(len(removed))
            assert min(len(negative) - n for n in losses) >= 257
            print("Greedy vertex-cover sizes for these masks:", losses)
        previous = current


if __name__ == "__main__":
    replay()
