"""Verify matching CNF upper and lower certificates on the 520 case-35 tests."""
import gzip
import json
from itertools import combinations
from pathlib import Path

from order3_case35_star_packings import POINT7, PREFIX13
from order3_prefix_search import test_rows


def signatures(depth):
    masks = []
    for row, _ in test_rows():
        wires = [bool(row >> i & 1) for i in range(26)]
        for is_and, a, b in (PREFIX13 + POINT7)[:depth]:
            wires.append((wires[a] and wires[b]) if is_and else (wires[a] or wires[b]))
        bits = sum(int(v) << i for i, v in enumerate(wires))
        masks.append(bits | ((bits if wires[32] else 0) << len(wires)))
    return masks[:52], masks[52:]


def replay(depth, record):
    positive, negative = signatures(depth)
    clauses = [int(s, 16) for s in record["clauses"]]
    family = record["negatives"]
    pivots = record["positives"]
    if not (len(set(family)) == len(family) == len(clauses)):
        raise ValueError("upper and lower counts differ")
    if not (all(0 <= j < 468 for j in family) and all(0 <= p < 52 for p in pivots)):
        raise ValueError("invalid test index")
    if not all(0 < c < 1 << (2 * (26 + depth)) for c in clauses):
        raise ValueError("invalid source in clause")
    if not all(all(c & p for p in positive) for c in clauses):
        raise ValueError("positive rejected")
    if not all(any(not c & n for c in clauses) for n in negative):
        raise ValueError("negative accepted")
    for j, k in combinations(family, 2):
        # A clause dark at j and k misses every pivot contained in their union.
        union = negative[j] | negative[k]
        if not any(not positive[p] & ~union for p in pivots):
            raise ValueError(f"unseparated negatives {j}, {k}")
    return len(clauses)


if __name__ == "__main__":
    path = Path(__file__).with_name("results") / "case35-clause-covers.json.gz"
    with gzip.open(path, "rt") as f:
        records = json.load(f)
    for depth in range(7, 18):
        count = replay(depth, records[str(depth)])
        print(depth, "gates in prefix;", count, "CNF clauses;",
              (count - 1).bit_length(), "further paid ANDs necessary")
