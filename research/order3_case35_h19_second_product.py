"""Replay the second ordinary AND exclusion at case 35's exceptional h=19 order."""
from collections import Counter
import gzip
from itertools import combinations, combinations_with_replacement
import json

from order3_case35_colored_trace import witness_graph
from order3_case35_first_or import packing
from order3_case35_star_packings import ROOT, PREFIX13, POINT7, columns
from order3_case35_two_or_preloads import clique
from order3_prefix_search import test_rows


def read_ledger(name):
    with gzip.open(ROOT / f"case35-h19-exception-{name}.json.gz", "rt") as stream:
        return json.load(stream)


def seven_probe_floor(pool, graph, packs, constants, guard_off):
    rows = [j for j, flags in packs]
    k = len(rows)
    clique(graph, rows)
    if not 96 < k <= 128:
        raise ValueError("seven probes with no paid-output dependencies required")
    width = 0
    for entry in packs:
        packing(pool, entry)
        width += len(entry[1])
    if len(constants) != len(pool):
        raise ValueError("missing initial wire")
    for column, group in zip(pool, constants):
        clique(graph, group)
        if len(group) <= 64 or len({(column >> (52+j)) & 1 for j in group}) != 1:
            raise ValueError("starting wire is not constant on a 65-clique")
    clique(graph, guard_off)
    if len(guard_off) <= 64 or any((pool[32] >> (52+j)) & 1 for j in guard_off):
        raise ValueError("guard mask needs a 65-clique of false rows")
    # Both orientations use distinct OR outputs. Each orientation observes
    # k distinct seven-bit words and must pay at least their lightest weight.
    lightest = sum(sorted(word.bit_count() for word in range(128))[:k])
    return (width + 2*lightest + k-1)//k - 1


def replay():
    prefix = PREFIX13 + POINT7 + ((False, 14, 18), (True, 1, 43))
    pool = list(columns(prefix, test_rows()))
    if len(pool) != 45:
        raise ValueError("wrong prefix")
    pairs = combinations_with_replacement((i for i in range(45) if i != 32), 2)
    counts = Counter(hex(pool[a] & pool[b]) for a,b in pairs)
    large = read_ledger("next-and")
    residual = read_ledger("density")
    small = {row[0]: row[1:] for row in residual}
    colors = read_ledger("colorings")
    if (len(small) != len(residual) or set(large) & set(small) or
            set(large) | set(small) != set(counts) or set(colors) != set(small)):
        raise ValueError("incomplete or duplicate product coverage")
    floors = Counter()
    for word in counts:
        inputs = pool + [int(word, 16)]
        graph = witness_graph(inputs)
        if word in large:
            clique(graph, large[word])
            if len(large[word]) < 129:
                raise ValueError("seven bits can separate up to 128 rows")
        else:
            coloring = colors[word]
            if len(coloring) != 468 or any(not 0 <= c < 128 for c in coloring):
                raise ValueError("invalid 128-color assignment")
            for i,j in combinations(range(468), 2):
                if coloring[i] == coloring[j] and graph[i,j]:
                    raise ValueError("edge has equal colors")
            packs, constants, guard_off, recorded = small[word]
            floor = seven_probe_floor(inputs, graph, packs, constants, guard_off)
            if floor != recorded or floor <= 19:
                raise ValueError("insufficient OR floor")
            floors[floor] += 1
    print("physical pairs", sum(counts.values()), "distinct products",len(counts))
    print("129-cliques",len(large),"pairs covered",sum(counts[w] for w in large))
    print("128-colorable graphs",len(colors),"OR floors",dict(floors))
    print("remaining possible next ordinary AND products",0)


if __name__ == "__main__":
    replay()
