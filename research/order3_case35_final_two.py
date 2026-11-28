"""Finish the two first-OR cases that can use their own output in the second OR."""
import gzip
import json

from order3_case35_point_seven_or_order import (
    after_one, dominates, excluded_unions, first_survivors, guard_unions, pairs, verify_union_data,
)
from order3_case35_point_seven_shared_unions import ROOT, stage
from order3_case35_star_preloads import eight_paid_floor


def replay_final_two(base, closed):
    with gzip.open(ROOT / "case35-point-seven-final-two.json.gz", "rt") as stream:
        records = json.load(stream)
    remaining = first_survivors(base) - closed
    if len(remaining) != 2:
        raise ValueError("expected two unexcluded first columns")
    # Use exactly the same prior for both cases. Neither exclusion can use the other.
    forbidden = closed | excluded_unions(base, "case35-point-seven-first-or.json", 19)
    certified = set()
    for record in records:
        a, b = record["first"]
        if not 0 <= a <= b < len(base):
            raise ValueError("invalid first OR")
        x = base[a] | base[b]
        if x not in remaining or x in certified:
            raise ValueError("unexpected first column")
        after_one(base, x)
        extended = base + (x,)
        seconds = set(stage(extended, 18) - forbidden - verify_union_data(extended, record["second"], 18))
        for index, paid, third in record["continuations"]:
            if not 0 <= index < len(base):
                raise ValueError("invalid second OR")
            y = x | base[index]
            if y not in seconds:
                raise ValueError("unexpected second column")
            seconds.remove(y)
            pool = extended + (y,)
            # Old products can be moved before Y, where after_one already
            # excludes them. Free copies, including guard-masked copies, may
            # also dominate a proposed paid output on the 520 test rows.
            earlier = {0, *pool, *(v & base[32] for v in pool), *(u & v for u, v in pairs(extended))}
            live = {i for i, v in enumerate(pool) if not any(dominates(t, v & y) for t in earlier)}
            for i, mode, tests, guard_off in paid:
                if i not in live or mode != 0:
                    raise ValueError("unexpected paid intersection")
                floor = eight_paid_floor(list(base), pool[i] & y, [j for j, _ in tests],
                                         guard_off, dict(tests), unique_paid_outputs=True)
                if floor <= 19:
                    raise ValueError("paid intersection fits the residual OR budget")
                live.remove(i)
            if live:
                raise ValueError("a regular AND can still precede the third OR")
            if set(guard_unions(pool)) - verify_union_data(pool, third, 17) - forbidden:
                raise ValueError("uncovered third OR")
        if seconds:
            raise ValueError("missing second-OR continuation")
        certified.add(x)
    if certified != remaining:
        raise ValueError("incomplete final first-OR census")
    return frozenset(certified)
