"""Fifth non-guard gate after AND(3,15), OR(12,42), OR(5,10) in case 35."""
from collections import Counter
from concurrent.futures import ProcessPoolExecutor
from functools import lru_cache
from hashlib import sha256

from order3_case35_h19_guard_envelopes import (
    FOURTH_LEDGER, LEDGERS, ROOT, dominates, guard_unions, parent_pool, records, verify,
)


def frontier(checked):
    base = parent_pool()
    g = base[32]
    a = base[3] & base[15]
    x = base[12] | base[42]
    y = base[5] | base[10]
    old = set(base) | {a,x,y}
    free = old | {v & g for v in old}
    suppliers = {w for c,d,k in checked if k >= 20
                 and any(dominates(s,a) for s in (c,d,c & g,d & g))
                 for w in (c,d,c & g,d & g)}
    if not suppliers:
        raise ValueError("no certified pool supplies A")

    sources = suppliers | free

    @lru_cache(None)
    def covered(p):
        return any(dominates(w,p) for w in sources)

    independent = set(guard_unions([*base,a,x]))
    dependent = {v | w for v in (y,y & g) for w in free}
    pending = set()
    for z in independent | dependent:
        # If Z does not use Y, both later ORs must be used by the AND.
        # Otherwise moving the unused OR later contradicts the parent checkpoint.
        products = {y & z} if z in independent else set()
        if z in dependent:
            products.update(z & w for w in old | {z})
        pending.update((z,p) for p in products
                       if not covered(p) and not dominates(z,p) and not dominates(z & g,p))
    return (len(independent),len(dependent),len(independent | dependent)), pending


def relevant(ledgers):
    base = parent_pool()
    a, g = base[3] & base[15], base[32]
    for name, digest in ledgers:
        path = ROOT / name
        if sha256(path.read_bytes()).hexdigest() != digest:
            raise ValueError(f"unexpected ledger {name}")
        for record in records(path):
            c,d = record[:2]
            if any(dominates(w,a) for w in (c,d,c & g,d & g)):
                yield record


FIFTH = (('case35-h19-fifth-46-00.json.gz', '0c742b8947c9878062b1d10a7447c13f386b814a954e1e532455d9c56441df39'),)


def checked_pools():
    with ProcessPoolExecutor(max_workers=4) as workers:
        previous = list(workers.map(verify, relevant([*LEDGERS, FOURTH_LEDGER]), chunksize=3))
        added = list(workers.map(verify, relevant(FIFTH), chunksize=3))
    return previous, added


if __name__ == "__main__":
    previous, added = checked_pools()
    shape, before = frontier(previous)
    _, after = frontier(previous + added)
    print("independent, dependent, distinct fourth OR values",shape)
    print("remaining (Z,P) pairs",len(before),"to",len(after))
    print("additional OR floors",sorted(Counter(k for _,_,k in added).items()))
    if not before or after:
        raise ValueError("the fifth-gate exclusion did not replay")
