"""Initial regular ANDs with nine regular ANDs and twenty ORs after gate 17."""
from collections import Counter
from itertools import combinations_with_replacement
import gzip
import json

from order3_case35_point_seven_or_order import (
    dominates, first_survivors, old_replacements, one_preload,
)
from order3_case35_star_packings import POINT7, PREFIX13, ROOT, columns
from order3_case35_star_preloads import classify, eight_paid_floor
from order3_prefix_search import test_rows


def refined_exclusions(base):
    with gzip.open(ROOT / "case35-point-seven-h19-one-or-refined.json.gz", "rt") as stream:
        records = json.load(stream)
    rejected = set()
    for a, b, i, mode, tests, off in records:
        if not (0 <= a <= b < len(base) and 0 <= i < len(base) and mode == 0):
            raise ValueError("invalid one-OR refinement")
        x = base[a] | base[b]
        floor = eight_paid_floor(list(base), x & base[i], [j for j, _ in tests], off,
                                 dict(tests), unique_paid_outputs=True)
        if floor <= 20 or (x, i) in rejected:
            raise ValueError("unverified or repeated one-OR refinement")
        rejected.add((x, i))
    return rejected


def main():
    base = tuple(columns(PREFIX13 + POINT7, test_rows()))
    _, floors, _ = classify(list(base))
    if min(floors) <= 20:
        raise ValueError("an initial ordinary AND fits the twenty-OR budget")
    print("Initial operand pairs by OR floor after removing one ordinary AND:", dict(sorted(floors.items())))
    raw = {}
    for i, j in combinations_with_replacement(range(len(base)), 2):
        raw.setdefault(base[i] | base[j], (i, j))
    histogram = Counter()
    # Restrict attention to the known 230-column subfamily. The full initial
    # OR domain at the twenty-OR budget may include other columns.
    prior = old_replacements(base)
    rejected = refined_exclusions(base)
    for x in sorted(first_survivors(base)):
        fixed = (*prior, x, x & base[32])
        unresolved = []
        for i, wire in enumerate(base):
            product = x & wire
            if any(dominates(u, product) for u in fixed):
                continue
            floor = one_preload(base, None, product)
            if floor >= 21:
                continue
            # Giving X to the residual circuit removes the first OR as well.
            prepaid_floor = one_preload(base, x, product)
            if prepaid_floor < 20:
                unresolved.append((i, floor, prepaid_floor))
        survivors = []
        for i, floor, prepaid_floor in unresolved:
            if (x, i) in rejected:
                rejected.remove((x, i))
            else:
                survivors.append((i, floor, prepaid_floor))
        unresolved = survivors
        histogram[len(unresolved)] += 1
        if unresolved:
            print("First OR, open (operand, AND-only floor, OR-plus-AND floor):",
                  raw.get(x, hex(x)), unresolved, flush=True)
    if rejected:
        raise ValueError("refinement does not match an open case")
    print("First columns by unresolved regular-AND operand count:", dict(sorted(histogram.items())))


if __name__ == "__main__":
    main()
