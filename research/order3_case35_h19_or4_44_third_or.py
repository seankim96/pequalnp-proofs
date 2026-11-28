"""Check third OR choices after OR(4,44) and an extension by wire 8, 11 or 12."""
from collections import defaultdict
from concurrent.futures import ProcessPoolExecutor
import gzip
import json

from order3_case35_h19_or4_44 import initial, prune_sources, replay as second_ors
from order3_case35_point_seven_or_order import guard_unions
from order3_case35_star_packings import ROOT
from order3_case35_star_preloads import dominates, eight_paid_floor


def verify(record):
    i,word,tests,off,claimed,prune = record
    if i not in (8,11,12) or not prune:
        raise ValueError("unexpected branch")
    base = initial()
    value = int(word,16)
    z = base[i] | base[-1]
    pool = prune_sources([*base,z,value])
    floor = eight_paid_floor(pool[:-1],pool[-1],[j for j,_ in tests],off,
                             dict(tests),unique_paid_outputs=True)
    if floor != claimed or floor <= 16:
        raise ValueError("insufficient floor at the third OR")
    return i,value


def residual_third_ors(base, remaining, checked):
    banned = set(guard_unions(base)) - remaining
    result = {}
    for i in (8,11,12):
        z = base[-1] | base[i]
        domain = set(guard_unions((*base,z)))
        if not checked[i] <= domain:
            raise ValueError("third OR absent from domain")
        unresolved = {v for v in domain-banned if not any(dominates(w,v) for w in checked[i])}
        # Other certified pairs can supply both required columns. Either
        # supplied value may feed either original slot, with a free guard mask.
        for j, witnesses in checked.items():
            if j == i:
                continue
            other = base[-1] | base[j]
            for w in witnesses:
                candidates = (other, w, other & base[32], w & base[32])
                if any(dominates(u,z) for u in candidates):
                    unresolved = {v for v in unresolved if not any(dominates(u,v) for u in candidates)}
        result[i] = unresolved
        print("Y OR",i,"third ORs",len(domain),"new certificates",len(checked[i]),
              "unexcluded",len(unresolved))
    return result


def replay():
    base = initial()
    remaining = second_ors()
    with gzip.open(ROOT / "case35-h19-or4-44-third-or.json.gz","rt") as f:
        groups,entries=json.load(f)
    records = ([i,v,[(j,groups[p]) for j,p in tests],groups[off],floor,mode]
               for i,v,tests,off,floor,mode in entries)
    checked = defaultdict(set)
    with ProcessPoolExecutor(max_workers=4) as workers:
        for i,v in workers.map(verify,records,chunksize=4):
            if v in checked[i]:
                raise ValueError("duplicate third OR")
            checked[i].add(v)
    return residual_third_ors(base, remaining, checked)


if __name__ == "__main__":
    replay()
