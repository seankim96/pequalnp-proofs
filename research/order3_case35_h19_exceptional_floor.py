"""Recheck the eight-AND OR floor by bounding the number of exceptional ports."""
import gzip
from itertools import combinations
import json

from order3_case35_colored_trace import witness_graph
from order3_case35_h19_or4_44 import initial, prune_sources
from order3_case35_point_seven_probes import replay as check_pairs
from order3_case35_star_packings import ROOT
from order3_case35_two_or_preloads import clique


def pairings(ports):
    """Every partition into one- and two-port receiver blocks."""
    if not ports:
        yield ()
        return
    a, *others = ports
    for tail in pairings(others):
        yield ((a,), *tail)
    for j, b in enumerate(others):
        for tail in pairings(others[:j] + others[j+1:]):
            yield ((a,b), *tail)


def lightest(k, dropped):
    """Worst lightest-root weight over matchings of paid-output implications."""
    bounds = []
    for m in range(3):
        children = {2+j for j in range(m)}
        roots = sorted(set(range(8))-children)
        words = [x for x in range(256) if all(not ((x >> (2+j)) & 1)
                                               or (x >> j) & 1 for j in range(m))]
        best = min(sum(sorted((x & sum(1 << r for r in roots if r not in free)).bit_count()
                              for x in words)[:k]) for free in combinations(roots,dropped))
        bounds.append(best)
    return bounds


def replay_bound(pool, cert, fibers):
    k, width, _, _, _, original = check_pairs(pool, cert, unique_paid_outputs=True)
    graph = witness_graph(pool)
    K = [j for j,_ in cert["packs"]]
    blocked = {i for i,_ in cert["constants"]}
    ex = []
    for i, col in enumerate(pool):
        a = sum(col >> (52+j) & 1 for j in K)
        if i not in blocked and max(a,k-a) <= 128:
            ex.append(i)
    if len(cert["guard"]) < 129:
        ex.extend((len(pool),len(pool)+1))
    pairs = {(a,b) for a,b,_ in cert["incompatible"]}
    forbidden = set()
    for ports, rows in fibers:
        ports = tuple(ports)
        if (ports != tuple(sorted(set(ports))) or not set(ports) <= set(ex)
                or not 2 <= len(ports) <= 5 or len(rows) <= 2**(8-len(ports))):
            raise ValueError("invalid fixed-bit fiber")
        clique(graph,rows)
        for i in ports:
            if i < len(pool):
                if len({pool[i] >> (52+j) & 1 for j in rows}) != 1:
                    raise ValueError("source varies on witness rows")
            elif any(pool[32] >> (52+j) & 1 for j in rows):
                raise ValueError("guard may allow a nonzero probe")
        forbidden.add(ports)
    # If five ports occurred, their receiver partition must avoid every
    # fixed-bit contradiction whose ports can be chosen simultaneously.
    checked = 0
    for five in combinations(ex,5):
        local = [p for p in combinations(five,2) if p in pairs]
        if any(sum(i in p for p in local)>1 for i in five):
            continue
        checked += 1
        bad = [s for n in range(2,6) for s in combinations(five,n) if s in forbidden]
        for part in pairings(five):
            if any(p not in part for p in local):
                continue
            if not any(all(len(set(block).intersection(s))<=1 for block in part) for s in bad):
                raise ValueError("five exceptional operands still feasible")
    # Orient <=4 ports across the two traces, balancing the singletons.
    # At most two roots in either trace can then be exceptional.
    bounds = lightest(k,2)
    floor = (width + 2*min(bounds) + k-1)//k - 1
    return k,width,len(ex),checked,bounds,original,floor


def replay():
    with gzip.open(ROOT / "case35-h19-exceptional-fibers.json.gz","rt") as stream:
        cert,fibers=json.load(stream)
    pool=prune_sources(list(initial()[:-1]))
    stats=replay_bound(pool,cert,fibers)
    if stats[-1] <= 19:
        raise ValueError("exceptional prefix is not excluded")
    print("clique, packing width, candidate ports, five-port sets, root weights, old/new floor",stats)
    return stats


if __name__ == "__main__":
    replay()
