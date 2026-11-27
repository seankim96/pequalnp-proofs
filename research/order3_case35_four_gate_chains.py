"""Classify four binary-gate wiring shapes by inclusion chains of their nontrivial DNF terms."""
from collections import Counter
from itertools import combinations, combinations_with_replacement, permutations, product
from math import prod

from order3_case35_fifth_15_17 import prefix
from order3_prefix_search import test_rows


from order3_chain_cover import chain_cover, minimal


def canonical_products(terms):
    atoms = [i for i in range(8) if any(m & (1 << i) for m in terms)]
    lists = [[k for k, i in enumerate(atoms) if m & (1 << i)] for m in terms]
    return min(tuple(sorted(sum(1 << perm[k] for k in t) for t in lists))
               for perm in permutations(range(len(atoms))))


def check_hard_products(shapes):
    # The canonical masks describe K(2,2) plus an independent edge, K(2,3),
    # and K(2,3) minus an edge. All their nontrivial terms are pairs.
    assert shapes == {(3, 5, 10, 12, 48): 24, (3, 5, 9, 18, 20, 24): 48,
                      (3, 5, 9, 18, 20): 24}
    rows = test_rows()
    base = [prefix(x) for x, _ in rows]
    fixed = [v | (int(bool(v >> 13 & 1 and v >> 26 & 1)) << 30)
               | (int(bool(v >> 13 & 1 and v >> 27 & 1)) << 31) for v in base]
    wires = [sum(1 << i for i, v in enumerate(fixed) if v >> k & 1) for k in range(32)]
    high = (1 << 52) - 16
    # A comparable product equals its smaller wire on all tests. Charge an
    # incomparable product only at the high positive where both wires are active.
    labels = [[0 if not (a & ~b and b & ~a) else a & b & high for b in wires] for a in wires]
    edges = {m for row in labels for m in row}
    assert all(m.bit_count() <= 1 for m in edges)
    rectangles, triples = set(), set()
    anchor_counts = Counter()
    for a, b in combinations_with_replacement(range(32), 2):
        columns = {labels[a][c] | labels[b][c] for c in range(32)}
        doubles = [m for m in columns if m.bit_count() == 2]
        if doubles:
            anchors = [i for i in range(52) if any(m >> i & 1 for m in doubles)]
            size = next(k for k in (1, 2) if any(
                all(m & sum(1 << i for i in group) for m in doubles)
                for group in combinations(anchors, k)))
        else:
            size = 0
        anchor_counts[size] += 1
        for x, y in combinations_with_replacement(columns, 2):
            if (x | y).bit_count() == 4:
                rectangles.add(x | y)
        for x, y, z in combinations_with_replacement(columns, 3):
            mask = x | y | z
            assert mask.bit_count() <= 5
            if mask.bit_count() == 5:
                triples.add(mask)
    assert anchor_counts == {0: 368, 1: 124, 2: 36}
    five = {r | e for r in rectangles for e in edges if (r | e).bit_count() == 5}
    assert len(rectangles) == 18 and len(five) == 792 and len(triples) == 180 and triples <= five
    # Removing an edge from K(2,3) only shrinks the charged set.
    bins = {}
    positives, negatives = base[4:52], base[52:]
    for i, j in combinations(range(468), 2):
        union = negatives[i] | negatives[j]
        m = sum(1 << q for q, v in enumerate(positives) if v & ~union == 0)
        if m.bit_count() <= 5:
            bins[m] = bins.get(m, 0) | (1 << j)
    worst = 0
    for physical in five:
        m = sub = physical >> 4
        dropped = bins.get(0, 0)
        while sub:
            dropped |= bins.get(sub, 0)
            sub = (sub - 1) & m
        worst = max(worst, dropped.bit_count())
    assert worst == 191
    print("Anchor sizes for all 528 pairs of base wires:", sorted(anchor_counts.items()))
    print("Remaining shapes:", dict(sorted(shapes.items())))
    print("792 five-flag omission sets, at least", 468-worst, "retained negatives")


def replay():
    values = [sum(1 << row for row in range(256) if row & mask == mask)
              for mask in range(256)]
    distribution = Counter()
    shapes = 0
    hard = Counter()

    def visit(forms, signals, used):
        nonlocal shapes
        k = len(forms)
        if k == 4:
            shapes += 1
            cover = chain_cover(sorted(used))
            distribution[len(cover)] += 1
            if len(cover) > 4:
                hard[canonical_products(used)] += 1
            return
        for a, b in product(range(k + 1), repeat=2):
            # Selector zero reads a fresh formal input. A positive selector reads an earlier gate.
            x = forms[a-1] if a else {1 << (2*k)}
            y = forms[b-1] if b else {1 << (2*k+1)}
            u = signals[a-1] if a else values[1 << (2*k)]
            v = signals[b-1] if b else values[1 << (2*k+1)]
            for op in ('OR', 'AND'):
                if op == 'OR':
                    z, w = minimal(set(x) | set(y)), u | v
                else:
                    z, w = minimal({p | q for p in x for q in y}), u & v
                computed = 0
                for term in z:
                    computed |= values[term]
                assert computed == w
                visit(forms + [z], signals + [w], used | {t for t in z if t.bit_count() > 1})

    visit([], [], set())
    assert shapes == prod(2*k*k for k in range(1, 5)) == 9216
    assert distribution == {0: 1509, 1: 3408, 2: 3042, 3: 700, 4: 461, 5: 48, 6: 48}
    print('Exact chain count : number of wiring shapes', sorted(distribution.items()))
    print('Shapes with a four-chain certificate:', sum(v for k, v in distribution.items() if k <= 4))

    check_hard_products(hard)


if __name__ == '__main__':
    replay()
