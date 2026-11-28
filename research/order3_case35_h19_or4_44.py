"""Replay the second OR bounds after Y = OR(4,44) at the case-35 h=19 boundary."""
from collections import Counter
from concurrent.futures import ProcessPoolExecutor
from functools import lru_cache
import gzip
import json

from order3_case35_h19_second_or import replay as surviving_first_ors
from order3_case35_point_seven_or_order import guard_unions
from order3_case35_star_packings import ROOT, PREFIX13, POINT7, columns
from order3_case35_star_preloads import dominates, eight_paid_floor
from order3_prefix_search import test_rows


@lru_cache(maxsize=1)
def initial():
    return tuple(columns(PREFIX13 + POINT7 + (
        (False,14,18), (True,1,43), (False,4,44)), test_rows()))


def prune_sources(pool):
    """Sequentially replace a dominated source; preserve the guard at index 32."""
    wires = list(pool)
    for i, value in enumerate(wires):
        if i == 32:
            continue
        if any(i != j and (dominates(w, value) or dominates(w & wires[32], value))
               for j,w in enumerate(wires)):
            # A circuit on the new pool can reconstruct a dominating signal
            # via the surviving source and at most one free guard AND.
            wires[i] = 0
    return wires


def verify(record):
    word, tests, off, recorded, pruned = record
    value = int(word,16)
    pool = [*initial(),value]
    if pruned:
        pool = prune_sources(pool)
    floor = eight_paid_floor(pool[:-1],pool[-1],[j for j,_ in tests],off,
                             dict(tests),unique_paid_outputs=True)
    if floor != recorded or floor <= 17:
        raise ValueError("second OR still fits the budget")
    return value, floor


def replay():
    remaining = surviving_first_ors()
    inputs = initial()
    old = set(guard_unions(inputs[:-1]))
    if inputs[-1] not in remaining:
        raise ValueError("first OR does not belong to the parent frontier")
    domain = set(guard_unions(inputs))
    # The old ORs excluded by replacement or by prepaying their output
    # remain excluded at the next slot: the first OR can still be computed
    # with its original inputs and charged to the residual gate budget.
    prior = old - remaining
    with gzip.open(ROOT / "case35-h19-or4-44-second-or.json.gz","rt") as f:
        groups, entries = json.load(f)
    records = ([word,[(j,groups[flags]) for j,flags in tests],groups[off],floor,pruned]
               for word,tests,off,floor,pruned in entries)
    with ProcessPoolExecutor(max_workers=4) as workers:
        verified = dict(workers.map(verify,records,chunksize=5))
    if len(verified) != len(entries) or not set(verified) <= domain:
        raise ValueError("duplicate certificate or invalid OR")
    excluded = prior | {v for v in domain if any(dominates(u,v) for u in verified)}
    print("OR(4,44) second OR domain",len(domain),"certificates",len(verified),
          "floors",dict(Counter(verified.values())))
    print("excluded",len(excluded),"unexcluded",len(domain-excluded))
    return domain-excluded


if __name__ == "__main__":
    replay()
