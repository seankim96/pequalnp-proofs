"""Replay the partial AND, OR(14,18), AND search at the (10,19) split."""
from collections import Counter
from concurrent.futures import ProcessPoolExecutor
import gzip
from itertools import combinations_with_replacement
import json

from order3_case35_h19_first_or import parent_pool
from order3_case35_h19_or4_44 import prune_sources
from order3_case35_star_packings import ROOT
from order3_case35_star_preloads import dominates, eight_paid_floor


def verify(record):
    a, product, tests, off, score = record
    base = list(parent_pool())
    pool = prune_sources([*base, a, base[14] | base[18], product])
    floor = eight_paid_floor(pool[:-1], pool[-1], [j for j, _ in tests],
                             off, dict(tests), unique_paid_outputs=True)
    if floor != score or floor <= 18:
        raise ValueError("insufficient floor after paying one OR and two ANDs")
    return a, product


def replay():
    base = list(parent_pool())
    guard = base[32]
    union = base[14] | base[18]
    free = {0, *base, *(w & guard for w in base)}
    products = {a & b for a, b in combinations_with_replacement(base, 2)}
    useful = {p for p in products if not any(dominates(w, p) for w in free)}
    maximal = {p for p in useful if not any(q != p and dominates(q, p) for q in useful)}
    old = free | products | {w & guard for w in products}
    pending = set()
    for a in maximal:
        supplied = old | {a, a & guard, union, union & guard}
        for source in [*base, a, union]:
            product = union & source
            if not any(dominates(w, product) for w in supplied):
                pending.add((a, product))
    with gzip.open(ROOT / "case35-h19-fixed-second-or-floors.json.gz", "rt") as f:
        bank, records, _ = json.load(f)
    tests = ((int(a,16), int(p,16), [(j,bank[i]) for j,i in packs], bank[off], score)
             for a,p,packs,off,score in records)
    print("additional preload pairs", len(pending), flush=True)
    with ProcessPoolExecutor(max_workers=4) as workers:
        for pair in workers.map(verify, tests):
            pending.remove(pair)
    print("excluded by checked floor", len(records), "remaining", len(pending))
    print("floors", sorted(Counter(row[-1] for row in records).items()))
    return pending


if __name__ == "__main__":
    replay()
