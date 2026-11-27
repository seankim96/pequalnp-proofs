"""Verify residual CNF bounds for one paid AND with up to one preceding OR."""
from collections import Counter
import gzip
from itertools import combinations_with_replacement
import json
from pathlib import Path

import numpy as np

from order3_case35_clause_cover import signatures

ROOT = Path(__file__).with_name("results")
POS = (1 << 52) - 1


def read(name):
    with gzip.open(ROOT / name, "rt") as stream:
        return json.load(stream)


def pair_witnesses(sources):
    # Bit p survives iff all sources true on p are true on at least one of j,k.
    pairs = np.full((468, 468), POS, dtype=np.uint64)
    for src in sources:
        dark = np.array([not (src >> (52 + j) & 1) for j in range(468)])
        pairs[dark[:, None] & dark[None, :]] &= ~np.uint64(src & POS)
    return pairs


def added_witnesses(value, guard, negatives, left, right, old):
    pbits = np.uint64(value & POS)
    gbits = np.uint64(guard & POS)
    neg = np.array([bool(value >> (52 + j) & 1) for j in negatives])
    masked = neg & np.array([bool(guard >> (52 + j) & 1) for j in negatives])
    lost = (np.where(neg[left] | neg[right], np.uint64(0), pbits)
            | np.where(masked[left] | masked[right], np.uint64(0), pbits & gbits))
    return old & ~lost


def packing_size(value, guard, family, indices, old):
    left, right = indices
    flags = added_witnesses(value, guard, family, left, right, old)
    broken = np.flatnonzero(flags == 0)
    remaining = len(family)
    while broken.size:
        counts = np.bincount(np.r_[left[broken], right[broken]], minlength=len(family))
        pivot = counts.argmax()
        broken = broken[(left[broken] != pivot) & (right[broken] != pivot)]
        remaining -= 1
    return remaining


def exact(value, record, columns, pairs):
    family = record["negative_family"]
    clauses = [int(c, 16) for c in record["clauses"]]
    assert len(set(family)) == len(family) == len(clauses) and all(0 <= j < 468 for j in family)
    left, right = np.triu_indices(len(family), 1)
    rows = np.array(family)
    flags = added_witnesses(value, columns[32], family, left, right, pairs[rows[left], rows[right]])
    assert np.all(flags != 0)
    pool = columns + [value, value & columns[32]]
    output = (1 << 520) - 1
    for c in clauses:
        assert 0 <= c < 1 << len(pool)
        clause = 0
        for i, col in enumerate(pool):
            if c >> i & 1:
                clause |= col
        output &= clause
    assert output == POS
    return len(clauses)


def main():
    positive, negative = signatures(17)
    sig = positive + negative
    columns = [sum(((row >> i) & 1) << j for j, row in enumerate(sig)) for i in range(86)]
    guard = columns[32]
    family = read("case35-clause-covers.json.gz")["17"]["negatives"]
    pairs = pair_witnesses(columns)
    # Enumerate each unordered pair of positions in the packing once.
    left, right = np.triu_indices(len(family), 1)
    rows = np.array(family)
    old = pairs[rows[left], rows[right]]
    assert np.all(old != 0) and len(family) == 160
    extra = {int(k, 16): v for k, v in read("case35-clause-preloads.json.gz").items()}
    source = set(columns)
    raw = {a & b for a, b in combinations_with_replacement(source, 2)}
    unions = {a | b for a, b in combinations_with_replacement(source, 2)}
    products = {a & u for a in source for u in unions}
    # A masked OR is the OR of masked sources. Using the OR twice gives an
    # already available clause, so it supplies no additional paid product.
    exact_counts = Counter()
    minimum = 160
    used = set()
    for value in products:
        if value in extra:
            bound = exact(value, extra[value], columns, pairs)
            used.add(value)
        else:
            bound = packing_size(value, guard, family, (left, right), old)
        if value in raw:
            # Ignoring the extra wire gives the original 160-clause upper bound.
            assert value in extra or bound == 160
            exact_counts[bound] += 1
        minimum = min(minimum, bound)
    for key, record in json.loads((ROOT / "case35-two-or-star-clauses.json").read_text()).items():
        center, a, b, c = map(int, key.split("-"))
        star = columns[center] & (columns[a] | columns[b] | columns[c])
        print("Two-OR star", key, "exact residual CNF size", exact(star, record, columns, pairs))
    witness = columns[3] & (columns[16] | columns[20])
    assert used == set(extra) and len(extra[witness]["clauses"]) == minimum
    print("No OR:", len(raw), "exact counts", sorted(exact_counts.items()))
    print("At most one OR:", len(source), "sources,", len(unions), "unions,",
          len(products), "products. Exact minimum residual CNF size:", minimum)


if __name__ == "__main__":
    main()
