"""Independently replay the two-endpoint certificate for the fixed case-35 prefix."""
from itertools import combinations
import re

from order3_case35_fifth_15_17 import prefix
from order3_prefix_search import ROOT, test_rows


def replay():
    path = ROOT / "lean/PEqualNP/Research/PlaneCase35SixthTraceBound.lean"
    source = path.read_text()
    charged = int(re.search(r"private def charged .*? := \((0x[0-9a-f]+) >>>", source)[1], 16)
    removed = int(re.search(r"private def removed : Nat := (0x[0-9a-f]+)", source)[1], 16)
    rows = test_rows()
    positive = [prefix(row) for row, answer in rows if answer]
    negative = [prefix(row) for row, answer in rows if not answer]
    count = len(negative)
    universe = (1 << count) - 1
    assert not (removed & ~universe)
    boards = [(charged >> (count * p)) & universe for p in range(len(positive))]
    assert not charged >> (count * len(positive))
    keep = [n for n in range(count) if not (removed >> n) & 1]
    loads = [w.bit_count() for w in boards]
    assert all(w & removed == 0 for w in boards)
    discarded = removed.bit_count() + sum(sorted(loads)[-4:])
    assert removed.bit_count() <= 27 and max(loads) <= 46 and count - discarded >= 257
    pairs = 0
    for a, b in combinations(keep, 2):
        union = negative[a] | negative[b]
        endpoints = (1 << a) | (1 << b)
        assert any(bits & endpoints and not flag & ~union for bits, flag in zip(boards, positive))
        pairs += 1
    print(f"Permanent exclusions: {removed.bit_count()}. Largest flag charge: {max(loads)}.")
    print(f"Checked {pairs} pairs of {len(keep)} retained negatives.")
    print(f"Four flags discard at most {discarded} of {count}; at least {count-discarded} remain.")


if __name__ == "__main__":
    replay()
