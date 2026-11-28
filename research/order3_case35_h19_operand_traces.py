"""Check seven-bit repeated-source traces and eight-bit disjoint-source traces."""
from collections import Counter
from functools import lru_cache
import gzip
from itertools import combinations
import json

from order3_case35_colored_trace import witness_graph
from order3_case35_first_or import packing
from order3_case35_h19_exceptional_floor import pairings
from order3_case35_h19_first_or import parent_pool
from order3_case35_h19_fixed_second_or_fibers import replay as frontier
from order3_case35_h19_or4_44 import prune_sources
from order3_case35_star_packings import ROOT
from order3_case35_two_or_preloads import clique


def partitions(n, smallest=1):
    if n == 0:
        yield ()
    for size in range(smallest, n+1):
        for tail in partitions(n-size, size):
            yield (size, *tail)


@lru_cache(None)
def min_or_weight(k, drop):
    best = None
    for lengths in partitions(8):
        roots, edges = [], []
        first = 0
        for size in lengths:
            roots.append(first)
            edges.extend((i,i+1) for i in range(first, first+size-1))
            first += size
        words = [x for x in range(256) if all(not (x >> j & 1) or x >> i & 1 for i,j in edges)]
        if len(words) < k:
            continue
        for unpaid in combinations(roots, min(drop,len(roots))):
            mask = sum(1 << r for r in roots if r not in unpaid)
            weight = sum(sorted((x & mask).bit_count() for x in words)[:k])
            best = weight if best is None else min(best, weight)
    return best


def exceptional_limit(q, graph, fixed, limit):
    # Two abstract mask ports suffice: selecting masked operands at two
    # different receivers would force two bits to zero on >64 negatives.
    ports = range(len(q)+2)
    forbidden = set()
    edges = set()
    for choice, rows in fixed:
        choice = tuple(choice)
        if (choice != tuple(sorted(set(choice))) or not set(choice) <= set(ports)
                or not 2 <= len(choice) <= 8 or len(rows) <= 2**(8-len(choice))):
            raise ValueError("invalid simultaneous fixed bits")
        clique(graph, rows)
        for i in choice:
            if i < len(q):
                if len({q[i] >> (52+j) & 1 for j in rows}) != 1:
                    raise ValueError("nonconstant source")
            elif any(q[32] >> (52+j) & 1 for j in rows):
                raise ValueError("mask not forced false")
        forbidden.add(choice)
        if len(choice)==2:
            edges.add(choice)

    def search(chosen, start):
        if len(chosen) == limit+1:
            bad = [s for n in range(2,len(chosen)+1) for s in combinations(chosen,n) if s in forbidden]
            for blocks in pairings(chosen):
                if not any(all(len(set(group).intersection(s))<=1 for group in blocks) for s in bad):
                    raise ValueError("too many exceptional ports may occur")
            return
        for i in range(start,len(ports)):
            group = chosen+(i,)
            # Each forced edge needs a common receiver, which has only two ports.
            if all(sum(tuple(sorted((a,b))) in edges for b in group if a!=b)<=1 for a in group):
                search(group,i+1)
    search((),0)


def replay():
    remaining = frontier()
    base = list(parent_pool())
    floors = Counter()
    seen = set()
    with gzip.open(ROOT / "case35-h19-operand-traces.json.gz","rt") as f:
        encoded, records = json.load(f)
        bank = [[i for i in range(bits.bit_length()) if bits >> i & 1]
                for bits in (int(s,16) for s in encoded)]
        for ah,ph,tests,off,blocked,fixed,limit in records:
            tests = [(j,bank[t]) for j,t in tests]
            off = bank[off]
            blocked = [bank[t] for t in blocked]
            fixed = [(s,bank[t]) for s,t in fixed]
            a,p = int(ah,16),int(ph,16)
            if (a,p) not in remaining or (a,p) in seen:
                raise ValueError("unexpected preload pair")
            seen.add((a,p))
            q = prune_sources([*base,a,base[14] | base[18],p])
            graph = witness_graph(q)
            K = [j for j,fs in tests]
            k = len(K)
            clique(graph,K)
            clique(graph,off)
            if not 96 < k <= 128 or len(off)<=64 or any(q[32] >> (52+j) & 1 for j in off):
                raise ValueError("invalid seven-bit or guard family")
            for t in tests:
                packing(q,t)
            width = sum(len(fs) for _,fs in tests)
            if len(blocked)!=len(q):
                raise ValueError("missing raw-source check")
            for c,rows in zip(q,blocked):
                clique(graph,rows)
                if len(rows)<=64 or len({c >> (52+j) & 1 for j in rows})!=1:
                    raise ValueError("unblocked raw source in repeated-source trace")
            one = sum(sorted((x & 63).bit_count() for x in range(128))[:k])
            repeated = (width+2*one+k-1)//k-1
            exceptional_limit(q,graph,fixed,limit)
            weight = min_or_weight(k,limit//2)+min_or_weight(k,(limit+1)//2)
            distinct = (width+weight+k-1)//k-1
            floors[repeated,distinct] += 1
            if min(repeated,distinct)>18:
                remaining.remove((a,p))
    print("repeated/distinct OR floors", sorted(floors.items()), "remaining", len(remaining))
    return remaining


if __name__ == "__main__":
    replay()
