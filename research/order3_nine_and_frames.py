"""Find short representatives for the exhaustive nine-AND calculation.

Outputs a JSON certificate of the 20 first-gate and 15 two-gate orbits.
For each representative, a third column would have to split every stored
two-coordinate fiber into pieces of size at most 64.
"""
from itertools import chain, combinations, permutations
import json

from order3_nine_and_operands import extend_pool, split_cells, viable
from order3_prefix_search import DIFFERENCES, test_rows


def frames_and_dualities():
    neighbors = [set() for _ in range(26)]
    for i in range(13):
        for j in range(13, 26):
            if (i - j) % 13 in DIFFERENCES:
                neighbors[i].add(j)
                neighbors[j].add(i)
    intersect = {}
    for i in range(26):
        for j in range(26):
            if i != j and (i < 13) == (j < 13):
                common, = neighbors[i] & neighbors[j]
                intersect[i, j] = common

    frames = (q for q in permutations(range(13), 4) if all(
        c not in neighbors[intersect[a, b]] for a, b, c in combinations(q, 3)))
    source = next(frames)
    known = set(source)
    steps = []
    while len(known) < 26:
        before = len(known)
        for i, j in combinations(sorted(known), 2):
            v = intersect.get((i, j))
            if v is not None and v not in known:
                known.add(v)
                steps.append((v, i, j))
        if len(known) == before:
            raise ValueError("frame construction stalled")

    for frame in chain([source], frames):
        perm = [None] * 26
        for i, j in zip(source, frame, strict=True):
            perm[i] = j
        for v, i, j in steps:
            perm[v] = intersect[perm[i], perm[j]]
        if len(set(perm)) != 26 or any(perm[j] not in neighbors[perm[i]]
                                       for i in range(26) for j in neighbors[i]):
            raise ValueError("invalid incidence map")
        yield tuple(perm)
        yield tuple(13 * (1 - i // 13) + (-i) % 13 for i in perm)


def row_images(perm, rows):
    halves = ({r % 8192 for r in rows}, {r // 8192 for r in rows})
    table = [{h: sum(1 << perm[i + 13 * side] for i in range(13) if h >> i & 1)
              for h in masks} for side, masks in enumerate(halves)]
    return [table[0][r % 8192] | table[1][r // 8192] for r in rows]


def first_image(pair, perm):
    return tuple(sorted(tuple(sorted(perm[i] for i in support)) for support in pair))


def certificate():
    rows = [r for r, positive in test_rows() if not positive]
    positions = {r: j for j, r in enumerate(rows)}
    universe = (1 << len(rows)) - 1
    primary = [sum(1 << j for j, r in enumerate(rows) if r >> i & 1) for i in range(26)]
    terms = [([], 0), *[([i], x) for i, x in enumerate(primary)]]
    terms.extend(([i, j], primary[i] | primary[j]) for i, j in combinations(range(26), 2))
    raw = {v for _, v in terms if v.bit_count() <= 256}
    eligible = {tuple(s): v for s, v in terms if 212 <= v.bit_count() <= 256}
    maps = list(frames_and_dualities())
    if len(set(maps)) != 11232 or any(set(row_images(g, rows)) != positions.keys() for g in maps):
        raise ValueError("the incidence maps must also preserve all negatives")
    unseen = set(combinations(sorted(eligible), 2))
    result = []
    while unseen:
        pair = min(unseen)
        orbit = {first_image(pair, g) for g in maps}
        if not orbit <= unseen:
            raise ValueError("overlapping first orbits")
        unseen.difference_update(orbit)
        x, y = (eligible[s] for s in pair)
        first = x & y
        pool = extend_pool(raw, first)
        cells = split_cells({universe}, x, y, universe)
        vs = sorted(viable(pool, cells, 128))
        entry = dict(first=pair, multiplicity=len(orbit), eligible_operands=len(vs), second=[])
        result.append(entry)
        if len(vs) < 2:
            continue

        # Index 26 denotes the first AND output. Each tuple is an OR support.
        names = {}
        for support, v in terms:
            names.setdefault(v, support)
            names.setdefault(v | first, [*support, 26])
        lookup = {v: i for i, v in enumerate(vs)}
        action = []
        for g in maps:
            if first_image(pair, g) != pair:
                continue
            dest = [positions[r] for r in row_images(g, rows)]
            action.append([lookup[sum(1 << dest[k] for k in range(len(rows)) if v >> k & 1)]
                           for v in vs])
        branches = {(i, j) for i, j in combinations(range(len(vs)), 2)
                    if vs[i] & vs[j] not in (vs[i], vs[j])}
        while branches:
            i, j = min(branches)
            second_orbit = {tuple(sorted((p[i], p[j]))) for p in action}
            if not second_orbit <= branches:
                raise ValueError("overlapping second orbits")
            branches.difference_update(second_orbit)
            u, v = vs[i], vs[j]
            if viable(extend_pool(pool, u & v), split_cells(cells, u, v, universe), 64):
                raise ValueError("a possible third operand survived")
            entry["second"].append(dict(inputs=[names[u], names[v]],
                                        multiplicity=len(orbit) * len(second_orbit)))
    return result


if __name__ == "__main__":
    print(json.dumps(certificate(), indent=2))
