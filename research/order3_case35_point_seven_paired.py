"""Certify first-OR exclusions using paid crosses and targeted third-union packings."""
from functools import lru_cache
import gzip
import json

from order3_case35_point_seven_shared_unions import (
    ROOT, after_one, cross_bank_exclusions, dominates, eight_paid_floor,
    exclude_two_three, excluded_unions, extended_third_bank, first_survivors,
    guard_unions, proved, search, stage, verify_union_data,
)


@lru_cache(maxsize=1)
def exclusions(base):
    with gzip.open(ROOT / "case35-point-seven-paired-search.json.gz", "rt") as stream:
        records = json.load(stream)
    prior = proved(base) | {exclude_two_three(base)} | cross_bank_exclusions(base)
    forbidden = prior | excluded_unions(base, "case35-point-seven-first-or.json", 19)
    bank = sorted(set(extended_third_bank()) | {(j, tuple(f)) for j,f in records["tests"]})
    tests = [(j,f,sum(1 << i for i in f)) for j,f in bank]
    result = set()
    for a,b,count,crosses in records["first"]:
        if not 0 <= a <= b < len(base):
            raise ValueError("invalid first-OR pair")
        x = base[a] | base[b]
        if x not in first_survivors(base) or x in prior or x in result:
            raise ValueError("first OR already covered or outside the census")
        after_one(base,x)
        ext = base + (x,)
        seconds = stage(ext,18) - forbidden - set(ext)
        if len(seconds) != count:
            raise ValueError("second-OR domain differs from the ledger")
        prepaid = set()
        for u,v,c,d,mode,rows,off in crosses:
            if (u,v) != (a,b) or not 0 <= c <= d < len(base) or mode not in (0,3):
                raise ValueError("invalid cross certificate")
            y = base[c] | base[d]
            if y not in seconds or y in prepaid:
                raise ValueError("unexpected second union")
            initial = list(base) if mode == 0 else [*base,x,y]
            floor = eight_paid_floor(initial,x & y,[j for j,_ in rows],off,dict(rows),
                                     unique_paid_outputs=True)
            if floor <= 19-mode.bit_count():
                raise ValueError("paid intersection still fits the OR budget")
            prepaid.add(y)
        for y in seconds:
            if y not in first_survivors(base):
                raise ValueError("second union has no initial-pair reduction")
            after_one(base,y)
            if y not in prepaid and not any(dominates(v & x,x & y) or
                                            dominates(v & y,x & y) for v in base):
                raise ValueError("a paid cross is still possible")
            inputs = ext + (y,)
            eligible = [(j,f) for j,f,mask in tests if all(
                v >> (52+j) & 1 or (v & mask).bit_count() <= 1 for v in (x,y))]
            certificate = search(inputs,eligible)
            excluded = verify_union_data(inputs,certificate,17)
            if set(guard_unions(inputs)) - excluded - forbidden - set(inputs):
                raise ValueError("a third OR is still possible")
        result.add(x)
    return frozenset(result)


if __name__ == "__main__":
    from order3_case35_star_packings import PREFIX13, POINT7, columns
    from order3_prefix_search import test_rows

    base = tuple(columns(PREFIX13 + POINT7, test_rows()))
    old = proved(base) | {exclude_two_three(base)} | cross_bank_exclusions(base)
    new = exclusions(base)
    print("new excluded first-OR values", len(new))
    print("remaining first-OR values", len(first_survivors(base) - old - new))
