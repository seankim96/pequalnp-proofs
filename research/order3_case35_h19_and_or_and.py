"""Check AND, OR, AND orders after the 17 fixed gates of case 35 (h=19)."""
from collections import Counter
from concurrent.futures import ProcessPoolExecutor
from functools import lru_cache
import gzip
from itertools import combinations_with_replacement
import json

from order3_case35_colored_trace import witness_graph
from order3_case35_first_or import packing
from order3_case35_h19_exceptional_floor import replay_bound
from order3_case35_h19_first_or import parent_pool
from order3_case35_h19_operand_traces import exceptional_limit, min_or_weight
from order3_case35_h19_or4_44 import prune_sources
from order3_case35_point_seven_or_order import guard_unions
from order3_case35_star_packings import ROOT
from order3_case35_star_preloads import dominates, eight_paid_floor
from order3_case35_two_or_preloads import clique


@lru_cache(None)
def repeated_weight(k):
    # Six charged bits and one uncharged bit. The Lean complementary-trace
    # bound allows any threshold; the kth smallest weight attains equality.
    histogram = Counter((word & 63).bit_count() for word in range(128))
    return max(k*t - sum(n*max(0,t-w) for w,n in histogram.items()) for t in range(7))


def check_record(record):
    a, p, cert, extra = record
    q = prune_sources([*parent_pool(), a, p])
    tests, off = cert["packs"], cert["guard"]
    rows = [j for j, _ in tests]
    if extra is None:
        floor = eight_paid_floor(q[:-1],q[-1],rows,off,dict(tests),unique_paid_outputs=True)
    else:
        fibers, blocked, limit = extra
        if len(rows)>128 and limit<=4:
            floor = replay_bound(q,cert,fibers)[-1]
        else:
            graph = witness_graph(q)
            clique(graph,rows)
            clique(graph,off)
            if (len(rows)<=96 or len(off)<=64 or any(q[32] >> (52+j) & 1 for j in off)
                    or cert["constants"]):
                raise ValueError("invalid operand trace prerequisites")
            for test in tests:
                packing(q,test)
            fixed = [(s,group) for s,group in fibers]
            fixed.extend(((i,j),group) for i,j,group in cert["incompatible"])
            exceptional_limit(q,graph,fixed,limit)
            k = len(rows)
            width = sum(len(fs) for _,fs in tests)
            weight = min_or_weight(k,limit//2) + min_or_weight(k,(limit+1)//2)
            if k<=128:
                if len(blocked)!=len(q):
                    raise ValueError("unchecked starting probe")
                for value,group in zip(q,blocked):
                    clique(graph,group)
                    if len(group)<=64 or len({value >> (52+j) & 1 for j in group})!=1:
                        raise ValueError("invalid constant-source family")
                weight = min(weight,2*repeated_weight(k))
            floor = (width+weight+k-1)//k-1
    if floor<=19:
        raise ValueError("two preloaded columns could still fit nineteen ORs")
    return a,p,floor


def records(path):
    with gzip.open(path,"rt") as stream:
        groups, rows = json.load(stream)
    bank = [[i for i in range(s.bit_length()) if s >> i & 1] for s in map(lambda v:int(v,16),groups)]
    for ah,ph,tests,off,extra in rows:
        cert = dict(packs=[(j,bank[v]) for j,v in tests],guard=bank[off])
        if extra is not None:
            pairs, constants, fibers, blocked, limit = extra
            cert.update(incompatible=[(i,j,bank[v]) for i,j,v in pairs],
                        constants=[(i,bank[v]) for i,v in constants])
            extra = [(s,bank[v]) for s,v in fibers], [bank[v] for v in blocked], limit
        yield int(ah,16), int(ph,16), cert, extra


def coverage(checked):
    base = list(parent_pool())
    guard = base[32]
    anchor = base[1] & base[14]
    known_union = base[14] | base[18]
    free = {0,*base,*(w & guard for w in base)}
    pairs = {a & b for a,b in combinations_with_replacement(base,2)}
    first = {v for v in pairs if not any(dominates(w,v) for w in free)}
    old = free | pairs | {p & guard for p in pairs}
    supplies = [(v,w,v & guard,w & guard) for v,w in checked]

    @lru_cache(None)
    def certificates(value):
        mask = 0
        for i,cols in enumerate(supplies):
            if any(dominates(c,value) for c in cols):
                mask |= 1<<i
        return mask

    @lru_cache(None)
    def old_product(v):
        return any(dominates(w,v) for w in old)

    @lru_cache(None)
    def new_product(x,v):
        return not (old_product(v) or dominates(x,v) or dominates(x & guard,v))

    @lru_cache(None)
    def candidates(x):
        if dominates(known_union,x) or dominates(known_union & guard,x):
            return frozenset()
        return frozenset(p for w in base if new_product(x,p := w & x))

    initial = set(guard_unions(base))
    counts = Counter()
    all_unions, open_unions, pending = set(),set(),set()
    for a in sorted(first):
        a_certs = certificates(a)
        reads_a = {v|w for v in (a,a & guard) for w in free|{a,a & guard}}
        for x in guard_unions([*base,a]):
            all_unions.add(x)
            products = candidates(x)
            if (not dominates(known_union,x) and not dominates(known_union & guard,x)
                    and new_product(x,p := a & x)):
                products = products | {p}
            remaining = {p for p in products if not (a_certs & certificates(p))}
            for key,active in [('all',True),('anchor',a==anchor),('dependent',x in reads_a)]:
                if active:
                    counts[key,'total'] += 1
                    counts[key,'open'] += bool(remaining)
            if remaining:
                open_unions.add(x)
                pending.update((a,x,p) for p in remaining)
    print("first products",len(first),"distinct OR values",len(all_unions),
          "fully excluded OR values",len(all_unions-open_unions))
    print("initial-source OR values",len(initial),"fully excluded",len(initial-open_unions))
    for key in ('all','anchor','dependent'):
        print(key,"prefix pairs",counts[key,'total'],"remaining",counts[key,'open'])
    missed = {a for a,x,p in pending}
    print("fully excluded first products",len(first-missed),"of",len(first))
    print("remaining triples",len(pending))
    return pending


def replay():
    checked = {}
    path = ROOT / "case35-h19-and-or-and.json.gz"
    with ProcessPoolExecutor(max_workers=5) as workers:
        for a,p,k in workers.map(check_record,records(path),chunksize=3):
            if (a,p) in checked:
                raise ValueError("duplicate preload record")
            checked[a,p] = k
    print("checked two-source floors",sorted(Counter(checked.values()).items()),flush=True)
    return coverage(checked)


if __name__ == "__main__":
    replay()
