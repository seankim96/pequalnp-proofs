"""Compress the small exact-mask multiplicity premises using the three stage-0 symmetries."""
import re
from collections import Counter
from itertools import combinations
from pathlib import Path

from order3_case5_orbits import move
from order3_prefix_search import test_rows


def orbit(seed, maps, action):
    visited = {seed}
    todo = [seed]
    while todo:
        x = todo.pop()
        for g in maps:
            y = action(x, g)
            if y not in visited:
                visited.add(y)
                todo.append(y)
    return visited


def main():
    src = Path(__file__).parents[1] / 'lean/PEqualNP/Research/OrderThreePlanePrefixData.lean'
    section = src.read_text().split('def stage0 : Stage := {')[1].split('representatives :=')[0]
    generators = [[int(x) for x in line.split(', ')] for line in re.findall(r'#\[([0-9, ]+)\]', section)]
    assert len(generators) == 3 and all(sorted(g) == list(range(26)) for g in generators)
    pos, neg = [[x for x, y in test_rows() if y == v] for v in (True, False)]
    def induced(rows):
        index = {x: i for i, x in enumerate(rows)}
        permutations = [[index[move(x, g)] for x in rows] for g in generators]
        assert all(sorted(g) == list(range(len(rows))) for g in permutations)
        return permutations
    on_pos, on_neg = induced(pos), induced(neg)

    def witness(a, b):
        return sum(1 << k for k, p in enumerate(pos) if not p & ~(neg[a] | neg[b]))

    remaining = set(combinations(range(468), 2))
    mask_class = {}
    totals = Counter()
    direct = Counter()
    sizes = {}
    pair_orbits = 0
    while remaining:
        a, b = min(remaining)
        pairs = orbit((a, b), on_neg, lambda t, g: tuple(sorted((g[t[0]], g[t[1]]))))
        assert pairs <= remaining
        remaining -= pairs
        pair_orbits += 1
        mask = witness(a, b)
        if mask not in mask_class:
            masks = orbit(mask, on_pos, move)
            representative = min(masks)
            mask_class.update(dict.fromkeys(masks, representative))
            sizes[representative] = len(masks)
        rep = mask_class[mask]
        totals[rep] += len(pairs)
        for i, j in pairs:
            current = witness(i, j)
            assert mask_class[current] == rep
            direct[current] += 1
    row_orbit = orbit(0, on_neg, lambda i, g: g[i])
    assert len(row_orbit) == 468
    anchored = Counter(mask_class[witness(0, b)] for b in range(1, 468))
    assert all(468 * anchored[rep] == 2 * total for rep, total in totals.items())
    print('pair orbits', pair_orbits, 'witness-mask orbits', len(totals))
    for rep in sorted(totals, key=lambda r: (r.bit_count(), r)):
        n, remainder = divmod(totals[rep], sizes[rep])
        assert remainder == 0
        assert all(direct[m] == n for m in mask_class if mask_class[m] == rep)
        if rep.bit_count() <= 5:
            print(rep.bit_count(), hex(rep), sizes[rep], totals[rep], n, anchored[rep])


if __name__ == '__main__':
    main()
