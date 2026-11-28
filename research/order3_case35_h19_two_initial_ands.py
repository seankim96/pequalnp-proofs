"""Test two initial ordinary ANDs in case 35's ten-AND, nineteen-OR split."""
from concurrent.futures import ProcessPoolExecutor
import gzip
from itertools import combinations, combinations_with_replacement
import json

from order3_case35_h19_exceptional_floor import replay_bound
from order3_case35_h19_first_or import parent_pool
from order3_case35_h19_or4_44 import prune_sources
from order3_case35_star_packings import ROOT
from order3_case35_star_preloads import classify, dominates, eight_paid_floor


def verify(record):
    a,b,tests,off,k=record
    pool=prune_sources([*parent_pool(),a,b])
    floor=eight_paid_floor(pool[:-1],pool[-1],[j for j,_ in tests],off,
                           dict(tests),unique_paid_outputs=True)
    if floor != k or floor <= 19:
        raise ValueError("two initial ordinary ANDs may fit the budget")
    return a,b


def replay():
    base=parent_pool()
    _,floors,_=classify(list(base))
    if min(floors)<=19:
        raise ValueError("a single prepaid source product can suffice")
    guard=base[32]
    free={0,*base,*(u & guard for u in base)}
    pairs={a & b for a,b in combinations_with_replacement(base,2)}
    useful={v for v in pairs if not any(dominates(w,v) for w in free)}
    tops=sorted(v for v in useful if not any(u!=v and dominates(u,v) for u in useful))
    supply=free | set(tops) | {w & guard for w in tops}
    triples={v & w for v in pairs for w in base}
    if any(not any(dominates(u,v) for u in supply) for v in triples):
        raise ValueError("a dependent AND needs an additional preload type")
    needed=set(combinations(tops,2))
    with gzip.open(ROOT / "case35-h19-two-initial-and-floors.json.gz","rt") as f:
        bank,rows,strong=json.load(f)
    tests=([int(a,16),int(b,16),[(j,bank[k]) for j,k in packs],bank[off],score]
           for a,b,packs,off,score in rows)
    with ProcessPoolExecutor(max_workers=4) as workers:
        for pair in workers.map(verify,tests,chunksize=4):
            needed.remove(pair)
    for a,b,c,fibers in strong:
        a,b=int(a,16),int(b,16)
        stats=replay_bound(prune_sources([*base,a,b]),c,fibers)
        if stats[-1]<=19:
            raise ValueError("fiber certificate does not exceed nineteen ORs")
        needed.remove((a,b))
    print("useful pairs",len(useful),"maximal pairs",len(tops),"triple values",len(triples))
    print("distinct two-preload cases",len(tops)*(len(tops)-1)//2,
          "ordinary floors",len(rows),"fiber floors",len(strong),"unexcluded",len(needed))
    return needed


if __name__ == "__main__":
    replay()
