"""List unresolved third-OR columns for a first union at the h=20 point-seven prefix."""
import argparse
from functools import lru_cache
import gzip
import json

from order3_case35_point_seven_paired import exclusions
from order3_case35_point_seven_shared_unions import (
    ROOT, cross_bank_exclusions, exclude_two_three, excluded_unions,
    extended_third_bank, first_survivors, guard_unions, pairs, proved, search,
    stage, verify_union_data,
)
from order3_case35_star_packings import PREFIX13, POINT7, columns
from order3_prefix_search import test_rows


def frontier(base, a, b, extra_excluded=()):
    closed = proved(base) | {exclude_two_three(base)} | cross_bank_exclusions(base) | exclusions(base)
    closed = closed.union(extra_excluded)
    x = base[a] | base[b]
    if x not in first_survivors(base) - closed:
        return []
    forbidden = excluded_unions(base, "case35-point-seven-first-or.json", 19) | closed
    with gzip.open(ROOT / "case35-point-seven-paired-search.json.gz", "rt") as stream:
        ledger = json.load(stream)
    bank = sorted(set(extended_third_bank()) | {(j,tuple(f)) for j,f in ledger["tests"]})
    tests = [(j,f,sum(1 << i for i in f)) for j,f in bank]
    extended = base + (x,)
    seconds = stage(extended,18) - forbidden - set(extended)
    result = []
    for y in sorted(seconds):
        inputs = extended + (y,)
        valid = [(j,f) for j,f,mask in tests if all(
            w >> (52+j) & 1 or (w & mask).bit_count() <= 1 for w in (x,y))]
        rejected = verify_union_data(inputs,search(inputs,valid),17)
        remaining = sorted(set(guard_unions(inputs)) - rejected - forbidden - set(inputs))
        # A guard-masked operand need not have a raw-pair representation.
        # Keep the exact 520-bit value even when the list of raw pairs is empty.
        raw = {}
        for i,k in pairs(range(len(inputs))):
            raw.setdefault(inputs[i] | inputs[k], []).append([i,k])
        result.append({
            "second": hex(y),
            "second_raw_pairs": [[i,k] for i,k in pairs(range(len(extended))) if extended[i] | extended[k] == y],
            "third": [{"column": hex(z), "raw_pairs": raw.get(z, [])} for z in remaining],
        })
    return result


@lru_cache(maxsize=1)
def fourth_exclusion(base):
    """Exclude OR(4,19) by covering the first paid gate versus the fourth OR."""
    return _exclude_before_fourth(base, (4,19), (), "case35-point-seven-fourth-search.json.gz", 4)


@lru_cache(maxsize=1)
def five_exclusion(base):
    """Exclude first OR(4,5), replaying all ten surviving three-OR prefixes."""
    return _exclude_before_fourth(base, (4,5), (fourth_exclusion(base),),
                                  "case35-point-seven-4-5-fourth-search.json.gz", 10)


@lru_cache(maxsize=1)
def fourteen_exclusion(base):
    """Verify the six remaining third outputs for first OR(4,14)."""
    prior = (fourth_exclusion(base), five_exclusion(base))
    return _exclude_before_fourth(base, (4,14), prior,
                                  "case35-point-seven-4-14-fourth-search.json.gz", 6)


def _exclude_before_fourth(base, first, prior, filename, count):
    from order3_case35_star_preloads import eight_paid_floor
    from order3_case35_point_seven_or_order import after_one, dominates

    x = base[first[0]] | base[first[1]]
    after_one(base,x)
    pending = set()
    for row in frontier(base,*first,prior):
        y = int(row["second"],16)
        if y not in first_survivors(base):
            raise ValueError("unexpected second union")
        after_one(base,y)
        if not any(dominates(v & x,x & y) or dominates(v & y,x & y) for v in base):
            raise ValueError("uncovered paid cross after two unions")
        pending.update((y,int(t["column"],16)) for t in row["third"])
    if len(pending) != count:
        raise ValueError("unexpected third-OR frontier")
    with gzip.open(ROOT / filename,"rt") as f:
        records = json.load(f)
    for record in records:
        if len(record) == 5:  # Original ledger encoded Z as initial[k] OR Y.
            a,b,i,preloads,cert = record
            j = len(base) + 1
        else:
            a,b,i,j,preloads,cert = record
        if not (0 <= a <= b < len(base) and 0 <= i <= j < len(base) + 2):
            raise ValueError("invalid initial operand")
        y = base[a] | base[b]
        extended = base + (x,y)
        z = extended[i] | extended[j]
        pending.remove((y,z))
        pool = base + (x,y,z)
        # Apart from guard masking, operands now strip to a wire in pool.
        # An initial/initial, X/initial, Y/initial or X/Y paid output has
        # already been excluded without requiring it to precede the third OR.
        fixed = {0,*pool,*(v & base[32] for v in pool),*(u & v for u,v in pairs(pool[:-1]))}
        uncovered = {i for i,v in enumerate(pool) if not any(dominates(t,v & z) for t in fixed)}
        for i,mode,rows,off in preloads:
            if mode != 0 or i not in uncovered:
                raise ValueError("unexpected paid-product record")
            floor = eight_paid_floor(list(base),pool[i] & z,[j for j,_ in rows],off,
                                     dict(rows),unique_paid_outputs=True)
            if floor <= 19:
                raise ValueError("paid product fits the OR budget")
            uncovered.remove(i)
        if uncovered:
            raise ValueError("open paid product after three ORs")
        if verify_union_data(pool,cert,16) != set(guard_unions(pool)):
            raise ValueError("open fourth OR before first paid gate")
    if pending:
        raise ValueError("missing third union")
    return x


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("a", type=int)
    parser.add_argument("b", type=int)
    args = parser.parse_args()
    base = tuple(columns(PREFIX13 + POINT7,test_rows()))
    if not 0 <= args.a <= args.b < len(base):
        parser.error("expected ordered initial wire indices from 0 to 42")
    print(json.dumps(frontier(base,args.a,args.b,(fourth_exclusion(base),five_exclusion(base),fourteen_exclusion(base))),indent=2))
