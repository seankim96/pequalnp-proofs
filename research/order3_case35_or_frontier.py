"""List unresolved third-OR columns for a first union at the h=20 point-seven prefix."""
import argparse
from functools import lru_cache
import gzip
import json

from order3_case35_point_seven_paired import exclusions
from order3_case35_point_seven_shared_unions import (
    ROOT, cross_bank_exclusions, exclude_two_three, excluded_unions,
    extended_third_bank, first_survivors, guard_unions, pairs, proved, search,
    stage, verify_union_data,
)
from order3_case35_star_packings import PREFIX13, POINT7, columns
from order3_prefix_search import test_rows


def frontier(base, a, b, extra_excluded=()):
    closed = proved(base) | {exclude_two_three(base)} | cross_bank_exclusions(base) | exclusions(base)
    closed = closed.union(extra_excluded)
    x = base[a] | base[b]
    if x not in first_survivors(base) - closed:
        return []
    forbidden = excluded_unions(base, "case35-point-seven-first-or.json", 19) | closed
    with gzip.open(ROOT / "case35-point-seven-paired-search.json.gz", "rt") as stream:
        ledger = json.load(stream)
    bank = sorted(set(extended_third_bank()) | {(j,tuple(f)) for j,f in ledger["tests"]})
    tests = [(j,f,sum(1 << i for i in f)) for j,f in bank]
    extended = base + (x,)
    seconds = stage(extended,18) - forbidden - set(extended)
    result = []
    for y in sorted(seconds):
        inputs = extended + (y,)
        valid = [(j,f) for j,f,mask in tests if all(
            w >> (52+j) & 1 or (w & mask).bit_count() <= 1 for w in (x,y))]
        rejected = verify_union_data(inputs,search(inputs,valid),17)
        remaining = sorted(set(guard_unions(inputs)) - rejected - forbidden - set(inputs))
        # A guard-masked operand need not have a raw-pair representation.
        # Keep the exact 520-bit value even when the list of raw pairs is empty.
        raw = {}
        for i,k in pairs(range(len(inputs))):
            raw.setdefault(inputs[i] | inputs[k], []).append([i,k])
        result.append({
            "second": hex(y),
            "second_raw_pairs": [[i,k] for i,k in pairs(range(len(extended))) if extended[i] | extended[k] == y],
            "third": [{"column": hex(z), "raw_pairs": raw.get(z, [])} for z in remaining],
        })
    return result


@lru_cache(maxsize=1)
def fourth_exclusion(base):
    """Exclude OR(4,19) by covering the first paid gate versus the fourth OR."""
    return _exclude_before_fourth(base, (4,19), (), "case35-point-seven-fourth-search.json.gz", 4)


@lru_cache(maxsize=1)
def five_exclusion(base):
    """Exclude first OR(4,5), replaying all ten surviving three-OR prefixes."""
    return _exclude_before_fourth(base, (4,5), (fourth_exclusion(base),),
                                  "case35-point-seven-4-5-fourth-search.json.gz", 10)


@lru_cache(maxsize=1)
def fourteen_exclusion(base):
    """Verify the six remaining third outputs for first OR(4,14)."""
    prior = (fourth_exclusion(base), five_exclusion(base))
    return _exclude_before_fourth(base, (4,14), prior,
                                  "case35-point-seven-4-14-fourth-search.json.gz", 6)


@lru_cache(maxsize=1)
def five_nineteen_exclusion(base):
    """Cover the six outstanding triples with first union OR(5,19)."""
    prior = (fourth_exclusion(base), five_exclusion(base), fourteen_exclusion(base))
    return _exclude_before_fourth(base, (5,19), prior,
                                  "case35-point-seven-5-19-fourth-search.json.gz", 6)


@lru_cache(maxsize=1)
def eleven_twenty_one_exclusion(base):
    prior = (fourth_exclusion(base), five_exclusion(base), fourteen_exclusion(base),
             five_nineteen_exclusion(base))
    return _exclude_before_fourth(base, (11,21), prior,
                                  "case35-point-seven-11-21-fourth-search.json.gz", 4)


@lru_cache(maxsize=1)
def eight_sixteen_exclusion(base):
    prior = (fourth_exclusion(base), five_exclusion(base), fourteen_exclusion(base),
             five_nineteen_exclusion(base), eleven_twenty_one_exclusion(base))
    return _exclude_before_fourth(base, (8,16), prior, "case35-point-seven-8-16-search.json.gz", 0)


@lru_cache(maxsize=1)
def eight_twenty_five_exclusion(base):
    prior = (fourth_exclusion(base), five_exclusion(base), fourteen_exclusion(base),
             five_nineteen_exclusion(base), eleven_twenty_one_exclusion(base),
             eight_sixteen_exclusion(base))
    return _exclude_before_fourth(base, (8,25), prior, "case35-point-seven-8-25-search.json.gz", 14)


@lru_cache(maxsize=1)
def twelve_twenty_two_exclusion(base):
    prior = (fourth_exclusion(base), five_exclusion(base), fourteen_exclusion(base),
             five_nineteen_exclusion(base), eleven_twenty_one_exclusion(base),
             eight_sixteen_exclusion(base), eight_twenty_five_exclusion(base))
    return _exclude_before_fourth(base, (12,22), prior, "case35-point-seven-12-22-search.json.gz", 4)


@lru_cache(maxsize=1)
def fourth_stage_exclusions(base):
    """Replay additional two-OR exclusions independently against the same prior bank."""
    prior = (fourth_exclusion(base), five_exclusion(base), fourteen_exclusion(base),
             five_nineteen_exclusion(base), eleven_twenty_one_exclusion(base),
             eight_sixteen_exclusion(base), eight_twenty_five_exclusion(base),
             twelve_twenty_two_exclusion(base))
    records = json.loads((ROOT / "case35-point-seven-empty-thirds.json").read_text())
    closed = set(prior)
    for a,b,seconds in records:
        if not (0 <= a <= b < len(base) and seconds > 0):
            raise ValueError("invalid first-OR record")
        x = _exclude_before_fourth(base, (a,b), prior, None, 0, seconds)
        if x in closed:
            raise ValueError("repeated first-OR exclusion")
        closed.add(x)
    return frozenset(closed)


@lru_cache(maxsize=1)
def latest_exclusions(base):
    prior = fourth_stage_exclusions(base)
    first = _exclude_before_fourth(base, (4,8), prior, "case35-point-seven-4-8-search.json.gz", 18)
    prior = prior | {first}
    four_ten = _exclude_before_fourth(base, (4,10), prior, "case35-point-seven-4-10-search.json.gz", 28)
    prior = prior | {four_ten}
    with gzip.open(ROOT / "case35-crossed-empty-thirds.json.gz", "rt") as stream:
        entries = json.load(stream)
    extra = set()
    for a, b, seconds, crosses in entries:
        if not (0 <= a <= b < len(base) and seconds > 0):
            raise ValueError("invalid empty-third entry")
        x = _exclude_before_fourth(base, (a,b), prior, None, 0, seconds,
                                   cross_records=crosses)
        if x in extra:
            raise ValueError("repeated first union")
        extra.add(x)
    prior = prior | extra
    ten_fifteen = _exclude_before_fourth(base, (10,15), prior, "case35-point-seven-10-15-search.json.gz", 4)
    prior = prior | {ten_fifteen}
    eleven_fourteen = _exclude_before_fourth(base, (11,14), prior, "case35-point-seven-11-14-search.json.gz", 4)
    return prior | {eleven_fourteen}


def _exclude_before_fourth(base, first, prior, filename, count, expected_seconds=None, *, cross_records=()):
    from order3_case35_star_preloads import eight_paid_floor
    from order3_case35_point_seven_or_order import after_one, dominates

    x = base[first[0]] | base[first[1]]
    after_one(base,x)
    ledger = {"triples": [], "crosses": cross_records}
    if filename is not None:
        with gzip.open(ROOT / filename, "rt") as stream:
            ledger = json.load(stream)
    records = ledger if isinstance(ledger, list) else ledger["triples"]
    crosses = set()
    for a,b,c,d,mode,tests,off in ([] if isinstance(ledger, list) else ledger["crosses"]):
        if (a,b) != first or not (0 <= c <= d < len(base)) or mode != 0:
            raise ValueError("invalid two-OR cross")
        y = base[c] | base[d]
        floor = eight_paid_floor(list(base), x & y, [j for j,_ in tests], off,
                                 dict(tests), unique_paid_outputs=True)
        if floor <= 19 or y in crosses:
            raise ValueError("invalid cross exclusion")
        crosses.add(y)
    pending = set()
    rows = frontier(base,*first,prior)
    if expected_seconds is not None and len(rows) != expected_seconds:
        raise ValueError("unexpected second-OR count")
    for row in rows:
        y = int(row["second"],16)
        if y not in first_survivors(base):
            raise ValueError("unexpected second union")
        after_one(base,y)
        if not any(dominates(v & x,x & y) or dominates(v & y,x & y) for v in base):
            if y not in crosses:
                raise ValueError("uncovered paid cross after two unions")
            crosses.remove(y)
        pending.update((y,int(t["column"],16)) for t in row["third"])
    if crosses or len(pending) != count:
        raise ValueError("unexpected third-OR frontier")
    for record in records:
        if len(record) == 5:  # Original ledger encoded Z as initial[k] OR Y.
            a,b,i,preloads,cert = record
            j = len(base) + 1
        else:
            a,b,i,j,preloads,cert = record
        if not (0 <= a <= b < len(base) and 0 <= i <= j < len(base) + 2):
            raise ValueError("invalid initial operand")
        y = base[a] | base[b]
        extended = base + (x,y)
        z = extended[i] | extended[j]
        pending.remove((y,z))
        pool = base + (x,y,z)
        # Apart from guard masking, operands now strip to a wire in pool.
        # An initial/initial, X/initial, Y/initial or X/Y paid output has
        # already been excluded without requiring it to precede the third OR.
        fixed = {0,*pool,*(v & base[32] for v in pool),*(u & v for u,v in pairs(pool[:-1]))}
        uncovered = {i for i,v in enumerate(pool) if not any(dominates(t,v & z) for t in fixed)}
        for i,mode,rows,off in preloads:
            if mode != 0 or i not in uncovered:
                raise ValueError("unexpected paid-product record")
            floor = eight_paid_floor(list(base),pool[i] & z,[j for j,_ in rows],off,
                                     dict(rows),unique_paid_outputs=True)
            if floor <= 19:
                raise ValueError("paid product fits the OR budget")
            uncovered.remove(i)
        if uncovered:
            raise ValueError("open paid product after three ORs")
        if verify_union_data(pool,cert,16) != set(guard_unions(pool)):
            raise ValueError("open fourth OR before first paid gate")
    if pending:
        raise ValueError("missing third union")
    return x


def replay_four_ten_probe(base):
    """Fourth-union and product-dominance tests for one (4,10) continuation."""
    from order3_case35_point_seven_shared_unions import dominates

    x, y, z = base[4] | base[10], base[13] | base[42], base[12] | base[14]
    pool = base + (x, y, z)
    earlier = {0, *pool, *(v & base[32] for v in pool), *(a & b for a, b in pairs(pool[:-1]))}
    if not all(any(dominates(t, v & z) for t in earlier) for v in pool):
        raise ValueError("open product involving third OR")
    if not any(dominates(v & x, x & y) or dominates(v & y, x & y) for v in base):
        raise ValueError("open product crossing the first two ORs")
    with gzip.open(ROOT / "case35-point-seven-4-10-13-42-12-14.json.gz", "rt") as f:
        excluded = verify_union_data(pool, json.load(f), 16)
    if excluded != set(guard_unions(pool)):
        raise ValueError("open fourth OR in (4,10) probe")
    return len(excluded)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("a", type=int)
    parser.add_argument("b", type=int)
    args = parser.parse_args()
    base = tuple(columns(PREFIX13 + POINT7,test_rows()))
    if not 0 <= args.a <= args.b < len(base):
        parser.error("expected ordered initial wire indices from 0 to 42")
    print(json.dumps(frontier(base,args.a,args.b,latest_exclusions(base)),indent=2))
