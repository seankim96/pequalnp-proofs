"""Verify the remaining case-35 AND–OR–AND triples from checkpoint 81bd8904."""
import argparse
from collections import Counter
from concurrent.futures import ProcessPoolExecutor
from hashlib import sha256
from functools import lru_cache
import json
from pathlib import Path

from order3_case35_h19_support_sweep import (
    ROOT, filter_frontier, parent_pool, records, replay as replay_parent, verify,
)

from order3_case35_point_seven_or_order import guard_unions
from order3_case35_star_preloads import dominates

POS = (1 << 52) - 1
NEG = ((1 << 468) - 1) << 52
FRONTIER_DIGEST = "9d1ceab21e357928450dd7b14387ee1acaf4fa68f4387cc75e1ca0f43efd041f"


def least_preload(columns, guard):
    """Join positive bits and meet negative requirements only where a read is active."""
    positive, negative = 0, NEG
    for value in columns:
        positive |= value & POS
        can_mask = not (value & POS & ~guard)
        negative &= value | (~guard if can_mask else 0)
    return positive | negative


def serialize(rows):
    return json.dumps([[hex(v) for v in row] for row in sorted(rows)],
                      separators=(",", ":")).encode()


def ground_set(cache=None):
    if cache is None:
        serialized = serialize(replay_parent())
    else:
        serialized = Path(cache).read_bytes()
    if sha256(serialized).hexdigest() != FRONTIER_DIGEST:
        raise ValueError("unexpected parent frontier")
    return {tuple(int(s,16) for s in row) for row in json.loads(serialized)}


LEDGERS = (
    ("case35-h19-guard-envelope-00.json.gz", "06c5c16d710382a213a466bd64f05b55766421eb3845381076673c9f9a69ecb6"),
    ("case35-h19-guard-envelope-01.json.gz", "7ba97c9a9f919b36fa9acc303a206e25e816e7381a1a65670e14d93a6f1cc59f"),
    ("case35-h19-guard-envelope-02.json.gz", "d3542f254ccb969d3b0f8ba72a65ae38a91e24e1278aa5172d2c8b825d6279da"),
)


def sweep_records():
    for filename, digest in LEDGERS:
        path = ROOT / filename
        if sha256(path.read_bytes()).hexdigest() != digest:
            raise ValueError(f"corrupt ledger {filename}")
        yield from records(path)


def envelope_frontier(rows, checked):
    guard = parent_pool()[32]
    longer_budget = sum(1 << i for i,(_,_,floor) in enumerate(checked) if floor >= 20)

    @lru_cache(None)
    def suppliers(value):
        # The Lean least-preload theorem makes the optional guard choice
        # equivalent to a single signed comparison against this envelope.
        required = least_preload([value], guard)
        return sum(1 << i for i,(c,d,_) in enumerate(checked)
                   if dominates(c, required) or dominates(d, required))

    remaining = set()
    for a,x,p in rows:
        both = suppliers(a) & suppliers(p)
        if not (both & (longer_budget | suppliers(x))):
            remaining.add((a,x,p))
    return remaining


def summarize(before, checked):
    if len({(c,d) for c,d,_ in checked}) != len(checked):
        raise ValueError("repeated certificate")
    after = envelope_frontier(before, checked)
    if after != filter_frontier(before, checked):
        raise ValueError("least-envelope and direct masked-read enumerations disagree")
    base = parent_pool()
    target = base[3] & base[15]
    products = {p for a,_,p in before if a == target}
    maximal = {p for p in products if not any(u != p and dominates(u,p) for u in products)}
    target_floors = {d:k for c,d,k in checked if c == target and d in maximal}
    if len(products) != 151 or len(maximal) != 109 or target_floors.keys() != maximal:
        raise ValueError("missing AND(3,15) maximal-product witness")
    if min(target_floors.values()) < 20:
        raise ValueError("AND(3,15) target fits the lower-bound relaxation")
    print("AND(3,15) maximal-product floors", sorted(Counter(target_floors.values()).items()))
    print("OR floors", sorted(Counter(k for _,_,k in checked).items()))
    print("AND(3,15)", sum(a == target for a,_,_ in before),
          "to", sum(a == target for a,_,_ in after))
    print("remaining triples", len(after), "middle-OR pairs",
          len({(a,x) for a,x,_ in after}))
    return after


FOURTH_LEDGER = ('case35-h19-guard-fourth.json.gz', '78ea65b3c8cf2e5556815410f6fbf50b8bf1a2ae672f8557e1a75c0d66409b7f')


def fourth_frontier(checked):
    """The fourth non-guard gate is AND, following A, X, and a second OR Y."""
    base = parent_pool()
    guard = base[32]
    a = base[3] & base[15]
    x = base[12] | base[42]
    suppliers = {c for u,v,k in checked if k >= 20
                 and any(dominates(z,a) or dominates(z & guard,a) for z in (u,v))
                 for c in (u,v,u & guard,v & guard)}
    if not suppliers:
        raise ValueError("no two-preload certificate covers the first AND")

    @lru_cache(None)
    def certified(p):
        return any(dominates(c,p) for c in suppliers)

    # If Y does not read X, the next AND must read both ORs. A mask on
    # either operand just masks the intersection and is free in the relaxation.
    independent = set(guard_unions([*base,a]))
    open_independent = {y for y in independent if not certified(x & y)}

    # If Y does read X, the next AND must read Y. Its other input may be
    # an old column or a guarded read thereof, or Y itself.
    old = set(base) | {a,x}
    free = old | {v & guard for v in old}
    dependent = {u | v for u in (x,x & guard) for v in free}

    @lru_cache(None)
    def old_supplies(p):
        return any(dominates(w,p) for w in free)

    open_dependent = set()
    for y in dependent:
        for v in old | {y}:
            p = y & v
            if not (certified(p) or old_supplies(p) or dominates(y,p) or dominates(y & guard,p)):
                open_dependent.add((y,p))
    print("second OR values: independent, reading X, union",
          len(independent), len(dependent), len(independent | dependent))
    print("remaining independent values, dependent (Y,P) pairs",
          len(open_independent), len(open_dependent))
    return open_independent, open_dependent


def replay(cache=None):
    before = ground_set(cache)
    with ProcessPoolExecutor(max_workers=4) as workers:
        checked = list(workers.map(verify, sweep_records(), chunksize=4))
        name, digest = FOURTH_LEDGER
        if sha256((ROOT / name).read_bytes()).hexdigest() != digest:
            raise ValueError("unexpected fourth-gate ledger")
        extra = list(workers.map(verify, records(ROOT / name), chunksize=4))
    pending = summarize(before, checked)
    if pending:
        raise ValueError("AND–OR–AND order still has surviving triples")
    print("additional fourth-gate floors",sorted(Counter(k for _,_,k in extra).items()))
    independent, dependent = fourth_frontier([*checked,*extra])
    if independent or dependent:
        raise ValueError("fixed AND(3,15), OR(12,42) prefix still admits a fourth AND")
    return pending


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--parent-cache", help="canonical JSON returned by the parent enumeration")
    parser.add_argument("--write-frontier", type=Path, help="write sorted unexcluded triples as JSON")
    args = parser.parse_args()
    pending = replay(args.parent_cache)
    output = serialize(pending)
    print("remaining SHA-256", sha256(output).hexdigest())
    if args.write_frontier:
        args.write_frontier.write_bytes(output)
