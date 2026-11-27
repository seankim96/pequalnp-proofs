"""Find and independently replay OR preload certificates on later point-seven branches."""
import argparse
from functools import lru_cache
from itertools import combinations_with_replacement
import json
from pathlib import Path


from order3_case35_first_or import packing
from order3_case35_point_seven_or_order import excluded_unions, guard_unions
from order3_case35_star_packings import PREFIX13, POINT7, columns
from order3_prefix_search import test_rows


def packing_bank(base, width, samples, seed):
    import numpy as np
    from scipy.optimize import Bounds, LinearConstraint, milp
    random = np.random.default_rng(seed)
    entries = []
    for j in range(468):
        constraints = LinearConstraint(np.array([[int(wire >> f & 1) for f in range(52)]
            for wire in base if not wire >> (52+j) & 1]), -np.inf, 1)
        found = set()
        for iteration in range(samples+1):
            objective = np.ones(52) if iteration == 0 else 100 + random.random(52)
            solution = milp(-objective, integrality=np.ones(52), bounds=Bounds(0,1),
                            constraints=constraints, options={"time_limit": 3})
            if solution.x is None:
                continue
            flags = tuple(np.flatnonzero(solution.x > 0.5).tolist()[:width])
            # A search miss supplies no constraint on the circuits.
            if len(flags) < width:
                break
            packing(base, (j,flags))
            found.add(flags)
        entries.extend((j,flags) for flags in sorted(found))
    return entries


def search(base, tests):
    # Each bit indexes one previously verified negative/flag packing.
    full = (1 << len(tests))-1
    flag_bits = [0]*52
    negative_bits = {}
    for i,(j,flags) in enumerate(tests):
        bit = 1 << i
        negative_bits[j] = negative_bits.get(j,0) | bit
        for f in flags:
            flag_bits[f] |= bit

    @lru_cache(maxsize=None)
    def masks(column):
        flags = column & ((1 << 52)-1)
        hits = multiple = 0
        while flags:
            one = flags & -flags
            flags ^= one
            selected = flag_bits[one.bit_length()-1]
            multiple |= hits & selected
            hits |= selected
        negative_on = sum(bits for j,bits in negative_bits.items() if column >> (52+j) & 1)
        return hits & ~negative_on, full & ~(multiple & ~negative_on)

    pivots = []
    for p in range(52):
        starting = set()
        for w in base:
            if w >> p & 1:
                starting |= {w} | {w & old for old in starting}
        pivots.append((p,starting))
    pivots.sort(key=lambda entry: len(entry[1]))
    records = []
    for index,value in enumerate(guard_unions(base)):
        valid = masks(value)[1]
        if not valid:
            continue
        for p,starting in pivots:
            candidates = starting
            if value >> p & 1:
                candidates = starting | {value} | {v & value for v in starting}
            killers = [valid & ~masks(v)[0] for v in candidates]
            if 0 in killers:
                continue
            used = []
            while killers:
                shortest = min(killers,key=int.bit_count)
                bit = shortest & -shortest
                used.append(bit.bit_length()-1)
                killers = [w for w in killers if not w & bit]
            records.append((index,p,used))
            break
    used = sorted({i for _,_,ids in records for i in ids})
    mapping = {old:new for new,old in enumerate(used)}
    return {"tests": [tests[i] for i in used],
            "witnesses": [[index,p,[mapping[i] for i in ids]] for index,p,ids in records]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--union", nargs=2, type=int, action="append", default=[],
                        help="append a known OR by starting or previous union wire index")
    parser.add_argument("--samples", type=int, default=90, help="extra packing proposals per negative")
    parser.add_argument("--seed", type=int, default=2304)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    base = columns(PREFIX13+POINT7,test_rows())
    width = 19 - len(args.union)
    if args.samples < 0 or width < 1:
        parser.error("expected nonnegative sample budget and positive target width")
    for a,b in args.union:
        if not 0 <= min(a,b) <= max(a,b) < len(base):
            parser.error("invalid union operands")
        base.append(base[a] | base[b])
    data = search(base,packing_bank(base,width,args.samples,args.seed))
    args.out.write_text(json.dumps(data,separators=(",",":"))+"\n")
    forbidden = excluded_unions(tuple(base),str(args.out.resolve()),width)
    remaining = set(guard_unions(base))-forbidden
    print("width",width,"excluded",len(forbidden),"unresolved",len(remaining))
    print("unresolved raw pairs",[(a,b) for a,b in combinations_with_replacement(range(len(base)),2)
                                  if (base[a] | base[b]) in remaining])


if __name__ == "__main__":
    main()
