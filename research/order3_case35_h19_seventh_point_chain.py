"""Seventh non-guard AND after two point extensions of the OR(5,10) branch."""
import argparse
from collections import Counter
from concurrent.futures import ProcessPoolExecutor
from functools import lru_cache
from pathlib import Path

from order3_case35_h19_sixth_after_third import (
    SEED, checked_parent, dominates, guard_unions, parent_pool, relevant, supply_test, verify,
)

# The fifth OR attaches one fresh point to the fourth OR.
PARTNERS = (1, 2, 3, 4, 6, 7, 8, 9, 11, 12)


def census(checked, partner):
    wires = parent_pool()
    guard = wires[32]
    a = wires[3] & wires[15]
    x = wires[12] | wires[42]
    y = wires[5] | wires[10]
    z = wires[0] | y
    w = wires[partner] | z
    # guard_unions obtains the guard from physical wire index 32.
    ordered = [*wires, a, x, y, z, w]
    values = guard_unions(ordered)
    old = set(ordered)
    free = old | {s & guard for s in old}
    supplied = supply_test(checked, partner=10)

    @lru_cache(None)
    def available(product):
        return supplied(product) or any(dominates(s, product) for s in free)

    residual = set()
    pairs = 0
    for v in values:
        # The preceding sixth-position exclusion allows us to require that
        # the seventh AND actually reads V, up to freely moving guard masks.
        for product in {v & u for u in old}:
            if not available(product) and not any(dominates(s, product) for s in (v, v & guard)):
                residual.add(product)
                pairs += 1
    return len(values), pairs, residual


SEVENTH = (
    ("case35-h19-seventh-chain-47-00.json.gz", "3828f63be5a30407db1e60a5e558cfc921eb8992ae6c546b2033bd4d2d287cb0"),
    ("case35-h19-seventh-chain-47-01.json.gz", "c11b714773ddc5ad6752bfe9d6e937152f000bc42b0ea8fca46de28fbcf42df3"),
)


def replay(partners, parent_cache=None):
    baseline = checked_parent(parent_cache)
    with ProcessPoolExecutor(max_workers=4) as pool:
        seed = list(pool.map(verify, relevant(SEED), chunksize=4))
        new = list(pool.map(verify, relevant(SEVENTH), chunksize=4))
    checked = baseline + seed + new
    print("new OR floors", sorted(Counter(k for _, _, k in new).items()))
    for i in partners:
        values, pairs, missing = census(checked, i)
        print("fifth OR partner", i, "sixth OR columns", values, "residual pairs", pairs)
        if missing:
            raise ValueError(f"found {len(missing)} remaining products for partner {i}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--partner", type=int, choices=PARTNERS, action="append")
    parser.add_argument("--parent-cache", type=Path)
    args = parser.parse_args()
    replay(args.partner or PARTNERS, args.parent_cache)
