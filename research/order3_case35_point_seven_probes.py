"""Replay the eight-paid-AND density bound for the point-seven 17-gate prefix."""
from functools import lru_cache
from itertools import combinations
import json

from order3_case35_colored_trace import witness_graph
from order3_case35_first_or import packing
from order3_case35_star_packings import ROOT
from order3_case35_two_or_preloads import clique


@lru_cache(None)
def forest_weight(k, drop_one=True):
    """For each paid-output probe choose its earlier parent. Ignore one extra root bit."""
    def visit(i, words, roots):
        if i == 8:
            masks = [roots]
            if drop_one:
                masks = [roots ^ (1 << bit) for bit in range(8) if roots >> bit & 1]
            return min(sum(sorted((w & mask).bit_count() for w in words)[:k]) for mask in masks)
        best = visit(i+1, words, roots | (1 << i))
        for parent in range(i):
            subset = [w for w in words if not ((w >> i) & 1) or (w >> parent) & 1]
            if len(subset) >= k:
                best = min(best, visit(i+1, subset, roots))
        return best
    return visit(0, list(range(256)), 0)


def replay(pool, cert=None):
    if cert is None:
        cert = json.loads((ROOT / "case35-point-seven-probe-pairs.json").read_text())
    graph = witness_graph(pool)
    K = [j for j,_ in cert["packs"]]
    k = len(K)
    clique(graph,K)
    if not 128 < k <= 256:
        raise ValueError("eight probes must all be independent")
    width = 0
    for item in cert["packs"]:
        packing(pool,item)
        width += len(item[1])
    guard = pool[32]
    off = cert["guard"]
    clique(graph,off)
    if len(off) <= 64 or any(guard >> (52+j) & 1 for j in off):
        raise ValueError("need at least 65 pairwise incompatible guard-false negatives")
    blocked = set()
    for i, group in cert["constants"]:
        if not 0 <= i < len(pool):
            raise ValueError("invalid input wire")
        clique(graph,group)
        if len(group)<129 or len({pool[i] >> (52+j) & 1 for j in group}) != 1:
            raise ValueError("missing constant-probe certificate")
        blocked.add(i)
    exceptional = set()
    for i,c in enumerate(pool):
        ones = sum(c >> (52+j) & 1 for j in K)
        if i not in blocked and max(ones,k-ones)<129:
            exceptional.add(i)
    # At most one receiver may select a guard-AND result on the >64 guard-false
    # family. Its two possible input ports get distinct synthetic vertices.
    if len(off)<129:
        exceptional.update([len(pool),len(pool)+1])
    edges = set()
    for a,b,group in cert["incompatible"]:
        clique(graph,group)
        if not (a in exceptional and b in exceptional and a<b and len(group)>=65):
            raise ValueError("invalid pair of exceptional ports")
        for i in (a,b):
            if i>=len(pool):
                if any(guard >> (52+j) & 1 for j in group):
                    raise ValueError("mask port not forced to zero")
            elif len({pool[i] >> (52+j) & 1 for j in group})!=1:
                raise ValueError("port is not constant on the family")
        edges.add((a,b))
    # Two constant bits in different gates allow at most 64 codewords.
    # An incompatibility edge therefore forces its ports into the same gate.
    at_most_two = all(sum(edge in edges for edge in combinations(triple, 2)) >= 2
                      for triple in combinations(sorted(exceptional), 3))
    # An exceptional port loses at most its true entries, and each bit has
    # at most 128 ones among distinct eight-bit words.
    weight = {}
    for i in exceptional:
        column = pool[i] if i < len(pool) else guard
        weight[i] = min(128, sum(column >> (52+j) & 1 for j in K))
    # Each selected vertex can be forced into the same two-port receiver as
    # at most one other vertex. Maximize loss over all sets of degree <= 1.
    neighbors = {v: {b if v == a else a for a,b in edges if v in (a,b)}
                 for v in exceptional}
    worst = 0
    def visit(chosen, candidates, total):
        nonlocal worst
        worst = max(worst, total)
        while candidates and total + sum(weight[v] for v in candidates) > worst:
            v, *candidates = candidates
            links = neighbors[v] & chosen
            if len(links) <= 1 and all(not (neighbors[u] & chosen) for u in links):
                visit(chosen | {v}, candidates, total + weight[v])
    visit(set(), sorted(exceptional, key=weight.get, reverse=True), 0)
    true_entries = 2 * forest_weight(k, False) - worst
    if at_most_two:
        # Orient the two complete traces so each has at most one exceptional
        # operand. The free-root calculation charges only distinct OR outputs.
        true_entries = max(true_entries, 2 * forest_weight(k))
    result = (width + true_entries + k-1)//k - 1
    return k, width, len(exceptional), len(edges), true_entries, result


def sweep():
    from collections import Counter
    from order3_prefix_search import test_rows
    from order3_case35_star_packings import columns, PREFIX13, POINT7, records, leaf_floor
    rows = test_rows()
    base = columns(PREFIX13, rows)
    by_prefix = dict(records(base))
    if len(by_prefix) != 390:
        raise ValueError("expected 390 distinct OR trees")
    remaining = set()
    after_three = Counter()
    for ops, width in by_prefix.items():
        floor = max(width - 1, leaf_floor(base, ops))
        after_three[floor] += 1
        if floor < 19:
            remaining.add(ops)
    extra = json.loads((ROOT / "case35-star-completion-probes.json").read_text())
    for center, gates, cert in extra:
        ops = tuple((False,a,b) for a,b in gates)
        if ops not in remaining:
            raise ValueError("unexpected completion")
        arms = {v for pair in gates for v in pair if v < 26}
        if not 0 <= center < 26 or arms != {i for i in range(26) if
            (i < 13) != (center < 13) and base[i] & base[center] & ((1<<52)-1)}:
            raise ValueError("completion must AND the tree with its common center")
        pool = columns(PREFIX13 + ops + ((True,center,41),), rows)
        stats = replay(pool, cert)
        floor = max(by_prefix[ops]-1, leaf_floor(base, ops))
        if 8 + stats[-1] <= 26 or 9 + floor <= 26:
            raise ValueError("insufficient floor at h=22")
        print("center",center,gates,"eight-paid ledger",stats)
        remaining.remove(ops)
    if remaining:
        raise ValueError("incomplete star sweep")
    print("unconditional suffix OR floors after tree",dict(after_three))
    print("point seven eight-paid ledger",replay(columns(PREFIX13 + POINT7, rows)))


if __name__ == "__main__":
    sweep()
