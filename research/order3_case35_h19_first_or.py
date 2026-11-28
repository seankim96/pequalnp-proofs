"""Classify a first ordinary AND immediately after at most one OR at h=19."""
from concurrent.futures import ProcessPoolExecutor
import gzip
from itertools import combinations_with_replacement
import json

from order3_case35_h19_exceptional_floor import replay_bound
from order3_case35_h19_or4_44 import initial, prune_sources
from order3_case35_point_seven_or_order import guard_unions
from order3_case35_star_packings import ROOT
from order3_case35_star_preloads import classify, dominates, eight_paid_floor


def parent_pool():
    # initial() ends in OR(14,18), AND(1,43), OR(4,44).
    return initial()[:-3]


def verify_one(record):
    x, v, tests, off, claimed = record
    base = parent_pool()
    added = [v] if x is None else [x,v]
    pool = prune_sources([*base,*added])
    floor = eight_paid_floor(pool[:-1],pool[-1],[j for j,_ in tests],off,
                             dict(tests),unique_paid_outputs=True)
    if floor != claimed or floor <= (20 if x is None else 19):
        raise ValueError("insufficient prepaid OR floor")
    return x,v


def classify_frontier(singles,paired):
    base = parent_pool()
    _, floors, _ = classify(list(base))
    if min(floors) <= 20:
        raise ValueError("initial source pair may fit the budget")
    guard=base[32]
    initial_pairs={a & b for a,b in combinations_with_replacement(base,2)}
    free=set(base)|initial_pairs|{0}
    free.update(v & guard for v in tuple(free))
    unions=guard_unions(base)
    products={x & w for x in unions for w in base}
    if not singles <= products:
        raise ValueError("unrecognized single-product record")
    hard={v for v in products if not any(dominates(u,v) for u in free)}
    unknown={v for v in hard if not any(dominates(u,v) for u in singles)}
    remaining=set()
    for x in unions:
        open_here={v for w in base if (v := w & x) in unknown
                   and not dominates(x,v) and not dominates(x & guard,v)}
        for u in paired.get(x,set()):
            if u not in products:
                raise ValueError("unexpected pair-certificate product")
            open_here={v for v in open_here if not dominates(u,v)}
        remaining.update((x,v) for v in open_here)
    if not set(paired) <= set(unions):
        raise ValueError("unknown first OR")
    print("OR values",len(unions),"product values",len(products),
          "products surviving initial dominance",len(hard))
    print("unresolved OR/product pairs",len(remaining),
          "first ORs admitting an unexcluded next AND",len({x for x,_ in remaining}))
    return remaining


def replay():
    with gzip.open(ROOT / "case35-h19-first-or-floors.json.gz","rt") as f:
        bank,rows,strong=json.load(f)
    records=[(int(x,16) if x else None,int(v,16),[(j,bank[k]) for j,k in tests],
              bank[off],floor) for x,v,tests,off,floor in rows]
    with ProcessPoolExecutor(max_workers=4) as workers:
        good=set(workers.map(verify_one,records,chunksize=4))
    if len(good)!=len(rows):
        raise ValueError("duplicate floor")
    for x,v,cert,fibers in strong:
        x=int(x,16) if x else None
        v=int(v,16)
        pool=prune_sources([*parent_pool(),*([x] if x is not None else []),v])
        stats=replay_bound(pool,cert,fibers)
        if stats[-1] <= (19 if x is not None else 20) or (x,v) in good:
            raise ValueError("weak or duplicate fiber exclusion")
        good.add((x,v))
    singles={v for x,v in good if x is None}
    paired={}
    for x,v in good:
        if x is not None:
            paired.setdefault(x,set()).add(v)
    print("ordinary density certificates",len(rows),"five-port certificates",len(strong))
    return classify_frontier(singles,paired)


if __name__ == "__main__":
    replay()
