"""Case 35 with 19 guard reads: test a sixth ordinary AND after a fixed third OR."""
import argparse
from collections import Counter
from concurrent.futures import ProcessPoolExecutor
from functools import lru_cache
from hashlib import sha256
from itertools import combinations_with_replacement
import json
from pathlib import Path

from order3_case35_h19_fifth_gate import (
    FOURTH_LEDGER, LEDGERS, FIFTH, dominates, guard_unions, parent_pool, relevant, verify,
)
from order3_case35_h19_fifth_after_first_or import INDEPENDENT, DEPENDENT
from order3_case35_h19_sixth_gate import SIXTH


def products(partner=10):
    base = parent_pool()
    guard = base[32]
    a, x = base[3] & base[15], base[12] | base[42]
    values = guard_unions([*base, a, x, base[5] | base[partner]])
    masked = {v: v & guard for v in values}
    needed = set()
    for y, z in combinations_with_replacement(values, 2):
        p = y & z
        # If an operand or its mask already supplies the intersection, the
        # paid AND can be deleted. Its consumers can use the stronger wire.
        if not any(dominates(w,p) for w in (y,z,masked[y],masked[z])):
            needed.add(p)
    return len(values), needed


def supply_test(checked, partner=10):
    base = parent_pool()
    g = base[32]
    a, x = base[3] & base[15], base[12] | base[42]
    old = set(base) | {a,x,base[5] | base[partner]}
    replacements = {w for c,d,k in checked if k >= 20
                    and any(dominates(s,a) for s in (c,d,c & g,d & g))
                    for w in (c,d,c & g,d & g)}
    if not replacements:
        raise ValueError("no certified pool supplies the first AND")
    replacements |= old | {w & g for w in old}
    positive = (1 << 52) - 1

    @lru_cache(None)
    def negative_requirements(flags):
        return [w >> 52 for w in replacements if flags & ~w == 0]

    @lru_cache(None)
    def covered(p):
        return any(n & ~(p >> 52) == 0 for n in negative_requirements(p & positive))

    return covered


def unexcluded(products, checked, partner=10):
    covered = supply_test(checked, partner)
    return {p for p in products if not covered(p)}


def dependent_frontier(checked, partner=10):
    base = parent_pool()
    g = base[32]
    a, x = base[3] & base[15], base[12] | base[42]
    old = set(base) | {a,x,base[5] | base[partner]}
    free = old | {w & g for w in old}
    covered = supply_test(checked, partner)

    @lru_cache(None)
    def old_products(z):
        # Normalized AND of Z with any wire older than the two variable ORs, ignoring a final mask.
        return {p for v in old if (p := z & v) != z and not covered(p)
                and not dominates(z,p) and not dominates(z & g,p)}

    pairs = 0
    remaining_triples = 0
    residual = set()
    for y in guard_unions([*base,a,x,base[5] | base[partner]]):
        yg = y & g
        choices = {u | v for u in (y,yg) for v in free | {y,yg}}
        pairs += len(choices)
        for z in choices:
            candidates = old_products(z)
            p = y & z
            if not covered(p) and not dominates(z,p) and not dominates(z & g,p):
                candidates = candidates | {p}
            missing = {q for q in candidates if not dominates(y,q) and not dominates(yg,q)}
            residual.update(missing)
            remaining_triples += len(missing)
    return pairs, remaining_triples, residual


def parent_pools():
    ledgers = [*LEDGERS, FOURTH_LEDGER, *FIFTH, *INDEPENDENT, *DEPENDENT, *SIXTH]
    with ProcessPoolExecutor(max_workers=4) as workers:
        return list(workers.map(verify, relevant(ledgers), chunksize=4))


def serialize_pools(pools):
    return json.dumps([[hex(c),hex(d),k] for c,d,k in sorted(map(tuple, pools))],
                      separators=(",", ":")).encode()


SEED = (('case35-h19-third-five-ten-47-00.json.gz', '64d6164ab88b90082c6da00d5f300424d41ef407c9ecd9eb352878e2173d82a8'), ('case35-h19-third-five-ten-47-01.json.gz', '72cdb2b7bcb34eb8842a682683d97684862c35cd9c8437bbd6d3c11306e34d50'))
FAMILY = ()
PARTNERS = (10,)


def checked_parent(cache):
    digest = "a290e9e3510dc2be9a03aec957fae394b8d013562fa78ccd291aaa9b1c1ff0c9"
    if cache and cache.exists():
        data = cache.read_bytes()
        if sha256(data).hexdigest() != digest:
            raise ValueError("unexpected parent replay cache")
        return [(int(c, 16), int(d, 16), k) for c, d, k in json.loads(data)]
    pools = parent_pools()
    data = serialize_pools(pools)
    if sha256(data).hexdigest() != digest:
        raise ValueError("inherited replay differs from the recorded parent")
    if cache:
        cache.write_bytes(data)
    return pools


def replay(partners, parent_cache=None, write_frontier=None):
    parent = checked_parent(parent_cache)
    manifest = SEED if partners == [10] else (*SEED, *FAMILY)
    with ProcessPoolExecutor(max_workers=4) as workers:
        added = list(workers.map(verify, relevant(manifest), chunksize=4))
    checked = parent + added
    print("checked parent pools", len(parent), "new OR floors", sorted(Counter(k for _, _, k in added).items()))
    frontier = {}
    for partner in partners:
        n, candidates = products(partner)
        left = unexcluded(candidates, checked, partner)
        pairs, triples, dependent = dependent_frontier(checked, partner)
        print("partner", partner, "OR values", n, "independent pairs", n * (n + 1) // 2,
              "independent residual", len(left), "dependent pairs", pairs,
              "dependent residual triples", triples, flush=True)
        frontier[partner] = {k: [hex(p) for p in sorted(v)] for k, v in
                             (("independent", left), ("dependent", dependent))}
    if write_frontier:
        write_frontier.write_text(json.dumps(frontier, sort_keys=True))
    if any(values for entry in frontier.values() for values in entry.values()):
        raise ValueError("the recorded sixth-gate exclusions did not replay")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--partner", type=int, choices=PARTNERS, action="append")
    parser.add_argument("--parent-cache", type=Path, help="reuse or create a digest-checked inherited replay")
    parser.add_argument("--write-frontier", type=Path)
    options = parser.parse_args()
    replay(options.partner or list(PARTNERS), options.parent_cache, options.write_frontier)
