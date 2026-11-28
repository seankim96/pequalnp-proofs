"""Replay two-preload tests with either 18 or 19 remaining OR gates."""
import argparse
from collections import Counter
from concurrent.futures import ProcessPoolExecutor
from functools import lru_cache
import gzip
from hashlib import sha256
import json

from order3_case35_h19_and_or_and import check_record, coverage, records, replay as replay_parent
from order3_case35_h19_first_or import parent_pool
from order3_case35_h19_or4_44 import prune_sources
from order3_case35_star_packings import ROOT
from order3_case35_star_preloads import dominates, eight_paid_floor

PARENT_SHA256 = "388dec23fa1d9232e41f30f85c5807c9c5ab82fb9655fed561a224dafaa18d25"


LEDGERS = (
    ("case35-h19-support-sweep-00.json.gz", "4125e430dd4036d3d7d9ae8e98ba44fa997eb2a92d1ac8f6c331fd82257f4f7f"),
    ("case35-h19-support-sweep-01.json.gz", "ca24908ec5295be03fa8a0f489eb396ba27401e4ba2a9280704132d19f404c2c"),
    ("case35-h19-support-sweep-02.json.gz", "30821cfc765f47188a6638cdc2d62edb3b67c9e799497ab64b6b89c93b3d2f03"),
)


def sweep_records():
    for filename, digest in LEDGERS:
        path = ROOT / filename
        if sha256(path.read_bytes()).hexdigest() != digest:
            raise ValueError(f"unexpected witness data in {filename}")
        yield from records(path)


def parent_frontier(recheck):
    path = ROOT / "case35-h19-and-or-and.json.gz"
    if sha256(path.read_bytes()).hexdigest() != PARENT_SHA256:
        raise ValueError("unexpected parent ledger")
    if recheck:
        return replay_parent()
    with gzip.open(path, "rt") as stream:
        _, rows = json.load(stream)
    return coverage({(int(a,16), int(p,16)) for a, p, *_ in rows})


def verify(record):
    c, d, certificate, extra = record
    if min(c,d) < 0 or max(c,d).bit_length() > 520:
        raise ValueError("invalid synthetic column record")
    if extra is not None:
        return check_record(record)
    pool = prune_sources([*parent_pool(), c, d])
    tests = certificate["packs"]
    lower = eight_paid_floor(pool[:-1], pool[-1], [j for j,_ in tests],
                             certificate["guard"], dict(tests), unique_paid_outputs=True)
    if lower < 19:
        raise ValueError("floor too small even when all three gates are prepaid")
    return c, d, lower


def filter_frontier(pending, certificates):
    # Bit i names a checked relaxed pool. Either slot or its guard mask
    # may supply any of the saved gates, including more than one of them.
    guard = parent_pool()[32]
    pos = (1 << 52) - 1
    pure = {}
    signed = []
    rebuild = 0
    for i, (c, d, floor) in enumerate(certificates):
        bit = 1 << i
        if floor > 19:
            rebuild |= bit
        for u in {c, d, c & guard, d & guard}:
            if u >> 52:
                signed.append((u, bit))
            else:
                pure[u] = pure.get(u, 0) | bit

    @lru_cache(None)
    def pure_supplies(flags):
        mask = 0
        for u, bits in pure.items():
            if not flags & ~u:
                mask |= bits
        return mask

    @lru_cache(None)
    def supplies(v):
        mask = pure_supplies(v & pos)
        for u, bit in signed:
            if dominates(u, v):
                mask |= bit
        return mask

    left = set()
    rebuilt = prepaid = overlap = 0
    for a, x, p in pending:
        pair = supplies(a) & supplies(p)
        two = bool(pair & rebuild)
        three = bool(pair & supplies(x))
        rebuilt += two
        prepaid += three
        overlap += two and three
        if not (two or three):
            left.add((a,x,p))
    print("two paid ANDs removed", rebuilt, "all three operations removed", prepaid,
          "overlap", overlap)
    return left


def check_target(previous, checked):
    base = parent_pool()
    target = base[26] & base[41]
    products = {p for a,_,p in previous if a == target}
    maxima = {p for p in products if not any(u != p and dominates(u,p) for u in products)}
    floors = {p:k for a,p,k in checked if a == target and p in maxima}
    if len(products) != 725 or len(maxima) != 324 or floors.keys() != maxima:
        raise ValueError("incomplete AND(26,41) maximal-product tests")
    if min(floors.values()) <= 19 or any(not any(dominates(u,p) for u in maxima) for p in products):
        raise ValueError("target has an uncovered third product")
    print("AND(26,41) maximal-product OR floors", sorted(Counter(floors.values()).items()))


def replay(recheck=False):
    previous = parent_frontier(recheck)
    if len(previous) != 55915:
        raise ValueError("incorrect parent ground set")
    with ProcessPoolExecutor(max_workers=5) as workers:
        checked = list(workers.map(verify, sweep_records(),
                                   chunksize=3))
    if len({(c,d) for c,d,_ in checked}) != len(checked):
        raise ValueError("duplicate preload pair")
    print("verified OR floors", sorted(Counter(k for _,_,k in checked).items()), flush=True)
    check_target(previous, checked)
    remaining = filter_frontier(previous, checked)
    pair_count = len({(a,x) for a,x,_ in remaining})
    base = parent_pool()
    target = base[26] & base[41]
    print("unexcluded (A,X,P)", len(remaining), "unexcluded (A,X)", pair_count)
    positive = (1 << 52) - 1
    print("unexcluded middle OR support sizes",
          sorted(Counter((x & positive).bit_count() for _,x,_ in remaining).items()))
    print("unexcluded third-product support sizes",
          sorted(Counter((p & positive).bit_count() for _,_,p in remaining).items()))
    print("excluded first products", 65 - len({a for a,_,_ in remaining}), "of 65")
    print("AND(26,41) triples", sum(a == target for a,_,_ in previous),
          "to", sum(a == target for a,_,_ in remaining))
    return remaining


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--recheck-parent", action="store_true")
    replay(parser.parse_args().recheck_parent)
