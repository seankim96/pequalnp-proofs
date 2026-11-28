"""Independent and dependent OR branches for a fifth-gate AND following AND(3,15), OR(12,42)."""
from collections import Counter
from concurrent.futures import ProcessPoolExecutor
from functools import lru_cache
from itertools import combinations_with_replacement

from order3_case35_h19_fifth_gate import checked_pools, dominates, guard_unions, parent_pool, relevant, verify


def products():
    base = parent_pool()
    guard = base[32]
    a, x = base[3] & base[15], base[12] | base[42]
    values = guard_unions([*base,a,x])
    masked = {v:v & guard for v in values}
    needed = set()
    for y,z in combinations_with_replacement(values,2):
        p = y & z
        # If an operand or its mask already supplies the intersection, the
        # paid AND can be deleted. Its consumers can use the stronger wire.
        if not any(dominates(w,p) for w in (y,z,masked[y],masked[z])):
            needed.add(p)
    return len(values), needed


def supply_test(checked):
    base = parent_pool()
    g = base[32]
    a, x = base[3] & base[15], base[12] | base[42]
    old = set(base) | {a,x}
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


def unexcluded(products, checked):
    covered = supply_test(checked)
    return {p for p in products if not covered(p)}


def dependent_frontier(checked):
    base = parent_pool()
    g = base[32]
    a, x = base[3] & base[15], base[12] | base[42]
    old = set(base) | {a,x}
    free = old | {w & g for w in old}
    covered = supply_test(checked)

    @lru_cache(None)
    def old_products(z):
        # Normalized AND of Z with any wire older than Y, ignoring a final mask.
        return {p for v in old if (p := z & v) != z and not covered(p)
                and not dominates(z,p) and not dominates(z & g,p)}

    pairs = 0
    remaining_triples = 0
    residual = set()
    for y in guard_unions([*base,a,x]):
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


INDEPENDENT = (
    ("case35-h19-independent-46-00.json.gz", "f55a99ef44461e5adac69ed776ca7458bd23547cd1470d0cfb362450e7efb684"),
    ("case35-h19-independent-46-01.json.gz", "e2ba44630a66c9a9d22cb76358eb9bfe3e89d384623a05ef5835c451338fdc41"),
    ("case35-h19-independent-46-02.json.gz", "4f47b05be2f115626bf497cc42b7102464ff3176998fb43477a47e08408d2688"),
    ("case35-h19-independent-46-03.json.gz", "6f22a5bcda0ddaeb9b4c5b8f04346a02957236a0cfd3601b2d75bd001447ba84"),
    ("case35-h19-independent-46-04.json.gz", "a7d649c20b91ffd4f1d011d83070f304892fa1c425f7c3a7166435f4092b424c"),
    ("case35-h19-independent-46-05.json.gz", "5f63ed17fa5ae01f612059efebe2352a4fece9a08f0121dfe4d68a5ca62a00db"),
    ("case35-h19-independent-46-06.json.gz", "f15f75d6ab633bb72fa4bde097364538a080e21d6b5004141a2cd45d033fe3aa"),
    ("case35-h19-independent-46-07.json.gz", "58104e55a8ee223f55ddcaba36e188d4a633fab95ea48aad22328466e5ac4584"),
    ("case35-h19-independent-46-08.json.gz", "8af329a74ef2a0c91973711705588c9251d53cdd38591f0dcf40d7e47f9dbd4f"),
    ("case35-h19-independent-46-09.json.gz", "27ea1960e2dd04dccf98320d087066ce9392363698369296e948faf70d534cf6"),
)

DEPENDENT = (
    ("case35-h19-dependent-46-00.json.gz", "b8382eeedaaacbb49a8f6b5889760ab3c42c0114139a5fa2528555cc8d3febbc"),
    ("case35-h19-dependent-46-01.json.gz", "21944a8dc32ac2f29e2c4091afdcbfd408d69b23ce51a7100dd1d646cf1b1a03"),
)

def replay():
    inherited, fifth = checked_pools()
    previous = inherited + fifth
    n, needed = products()
    left = unexcluded(needed, previous)
    with ProcessPoolExecutor(max_workers=4) as pool:
        checked = list(pool.map(verify, relevant(INDEPENDENT), chunksize=3))
        further = list(pool.map(verify, relevant(DEPENDENT), chunksize=3))
    pending = unexcluded(left, checked)
    pairs, intermediate, old_products = dependent_frontier(previous + checked)
    _, remaining, new_products = dependent_frontier(previous + checked + further)
    print("dependent OR pairs, surviving (Y,Z,P) triples",pairs,intermediate,"to",remaining)
    print("dependent residual products",len(old_products),"to",len(new_products))
    print("dependent additional floors",sorted(Counter(k for _,_,k in further).items()))
    print("independent OR values, unordered pairs including repetitions",n,n*(n+1)//2)
    print("distinct products after deleting redundant gates",len(needed))
    print("unexcluded product columns",len(left),"to",len(pending))
    print("additional OR floors",sorted(Counter(k for _,_,k in checked).items()))
    return pending, new_products


if __name__ == "__main__":
    import argparse
    import json
    from pathlib import Path
    parser = argparse.ArgumentParser()
    parser.add_argument("--write-frontier",type=Path)
    args = parser.parse_args()
    pending, dependent = replay()
    if args.write_frontier:
        args.write_frontier.write_text(json.dumps({"independent":[hex(p) for p in sorted(pending)],
                                                  "dependent":[hex(p) for p in sorted(dependent)]}))
