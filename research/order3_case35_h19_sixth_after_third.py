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


def third_column(base, point, partner, mask=0):
    """Use bit 0 for a guarded left input and bit 1 for a guarded right input."""
    left = base[point] & base[32] if mask & 1 else base[point]
    right = base[partner] & base[32] if mask & 2 else base[partner]
    return left | right


def products(partner=10, point=5, mask=0):
    base = parent_pool()
    guard = base[32]
    a, x = base[3] & base[15], base[12] | base[42]
    values = guard_unions([*base, a, x, third_column(base, point, partner, mask)])
    masked = {v: v & guard for v in values}
    needed = set()
    for y, z in combinations_with_replacement(values, 2):
        p = y & z
        # If an operand or its mask already supplies the intersection, the
        # paid AND can be deleted. Its consumers can use the stronger wire.
        if not any(dominates(w,p) for w in (y,z,masked[y],masked[z])):
            needed.add(p)
    return len(values), needed


def supply_test(checked, partner=10, point=5, mask=0):
    base = parent_pool()
    g = base[32]
    a, x = base[3] & base[15], base[12] | base[42]
    old = set(base) | {a,x,third_column(base, point, partner, mask)}
    replacements = {w for c,d,k in checked if k >= 20
                    and any(dominates(s,a) for s in (c,d,c & g,d & g))
                    for w in (c,d,c & g,d & g)}
    if not replacements:
        raise ValueError("no certified pool supplies the first AND")
    replacements |= old | {w & g for w in old}
    positive = (1 << 52) - 1

    # A dominating column must contain every required positive bit. Looking
    # up donors of the rarest required flag preserves the full search.
    by_flag = [[w for w in replacements if w & (1 << bit)] for bit in range(52)]

    @lru_cache(None)
    def negative_requirements(flags):
        candidates = replacements
        if flags:
            groups = (by_flag[bit] for bit in range(52) if flags & (1 << bit))
            candidates = min(groups, key=len)
        masks = {w >> 52 for w in candidates if flags & ~w == 0}
        return sorted(masks, key=int.bit_count)

    @lru_cache(None)
    def covered(p):
        return any(n & ~(p >> 52) == 0 for n in negative_requirements(p & positive))

    return covered


def unexcluded(products, checked, partner=10, point=5, mask=0):
    covered = supply_test(checked, partner, point, mask)
    return {p for p in products if not covered(p)}


def dependent_frontier(checked, partner=10, point=5, mask=0):
    base = parent_pool()
    g = base[32]
    a, x = base[3] & base[15], base[12] | base[42]
    old = set(base) | {a,x,third_column(base, point, partner, mask)}
    free = old | {w & g for w in old}
    covered = supply_test(checked, partner, point, mask)

    @lru_cache(None)
    def old_products(z):
        # Normalized AND of Z with any wire older than the two variable ORs, ignoring a final mask.
        return {p for v in old if (p := z & v) != z and not covered(p)
                and not dominates(z,p) and not dominates(z & g,p)}

    pairs = 0
    remaining_triples = 0
    residual = set()
    for y in guard_unions([*base,a,x,third_column(base, point, partner, mask)]):
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


SEED = (
    ("case35-h19-third-five-ten-47-00.json.gz", "64d6164ab88b90082c6da00d5f300424d41ef407c9ecd9eb352878e2173d82a8"),
    ("case35-h19-third-five-ten-47-01.json.gz", "72cdb2b7bcb34eb8842a682683d97684862c35cd9c8437bbd6d3c11306e34d50"),
)
DENSE = (
    ("case35-h19-next-dense-47-00.json.gz", "135cb7153dd09fe48ec16dd635b196f78f41f103ea516ebb2bad6ae04ef5359d"),
)
FAMILY = (
    ("case35-h19-point-five-47-00.json.gz", "3d8df25f4f6fb4775452352e2c3bda743cd028d2162c0531ba94b89e60b850c4"),
    ("case35-h19-point-five-47-01.json.gz", "34855f4ae59381a57098d9a857f0def726605554c71c8e99a8cde8fcbe9e95e7"),
    ("case35-h19-point-five-47-02.json.gz", "a6bc16f8ae79d8c468b50cf5bab3a66dc2296883e13e6660d340146ee695d402"),
    ("case35-h19-point-five-47-03.json.gz", "f900aa15c175703c9b14a0787ab4d3e39996f1b279c7ec99687595932878987f"),
    ("case35-h19-point-five-47-04.json.gz", "4ed35e1ac82ba85e79e4b0a45b5c1112804a4f74358086458ef58d1e8d172895"),
    ("case35-h19-point-five-47-05.json.gz", "93ae792d7de28f87136da8ba13c8d473f8ea078cc2e52433aa1ad6af1ee8fc1b"),
    ("case35-h19-point-five-47-06.json.gz", "e8be67ef62ab2fd9c099bd5a579d73437f9e5109c617ee9d55fe70f77c11977b"),
    ("case35-h19-point-five-47-07.json.gz", "1c694864047f3e742dfcffb0755ea68193dd615d4c60ff212dc3d476525b147c"),
    ("case35-h19-point-five-47-08.json.gz", "225740c48ebdd1f2358e54848fb77e9107a588b8d2a20ea8685d74fc6068d71d"),
    ("case35-h19-point-five-47-09.json.gz", "2d6f9db4d2f23e98faa4b601130cb1ce4444d5994fd3017e811beb3d036128e9"),
)
PARTNERS = (0, 1, 2, 3, 4, 6, 7, 8, 9, 10, 11, 12)


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


def replay(partners, parent_cache=None, write_frontier=None, explore_pair=None):
    point = 5
    if explore_pair is not None:
        point, target = explore_pair
        partners = [target]
    parent = checked_parent(parent_cache)
    manifest = SEED if partners == [10] and point == 5 else (*SEED, *FAMILY)
    if explore_pair is not None:
        manifest = (*manifest, *DENSE)
    with ProcessPoolExecutor(max_workers=4) as workers:
        added = list(workers.map(verify, relevant(manifest), chunksize=4))
    checked = parent + added
    print("checked parent pools", len(parent), "new OR floors", sorted(Counter(k for _, _, k in added).items()))
    frontier = {}
    for partner in partners:
        n, candidates = products(partner, point)
        left = unexcluded(candidates, checked, partner, point)
        pairs, triples, dependent = dependent_frontier(checked, partner, point)
        print("third OR", (point, partner), "OR values", n, "independent pairs", n * (n + 1) // 2,
              "independent residual", len(left), "dependent pairs", pairs,
              "dependent residual triples", triples, "distinct dependent products", len(dependent), flush=True)
        frontier[partner] = {k: [hex(p) for p in sorted(v)] for k, v in
                             (("independent", left), ("dependent", dependent))}
    if explore_pair is not None:
        if write_frontier:
            write_frontier.write_text(json.dumps(frontier[target], separators=(",", ":")))
        return
    if write_frontier:
        write_frontier.write_text(json.dumps(frontier, sort_keys=True))
    if any(values for entry in frontier.values() for values in entry.values()):
        raise ValueError("the recorded sixth-gate exclusions did not replay")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group()
    group.add_argument("--explore-pair", type=int, choices=range(13), nargs=2,
                       help="enumerate a third point-pair OR and save any open products")
    group.add_argument("--partner", type=int, choices=PARTNERS, action="append")
    parser.add_argument("--parent-cache", type=Path, help="reuse or create a digest-checked inherited replay")
    parser.add_argument("--write-frontier", type=Path)
    options = parser.parse_args()
    replay(options.partner or list(PARTNERS), options.parent_cache, options.write_frontier, options.explore_pair)
