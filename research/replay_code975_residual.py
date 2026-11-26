"""Replay the 104 residual sixth-AND cases with no solver dependencies."""
import json
from itertools import combinations
from pathlib import Path

from order3_code888_fifth import start, test_rows


def main():
    fixture = Path(__file__).parent / "results/code975-residual-families.json"
    data = json.loads(fixture.read_text())
    rows = [(start(x) | ((x >> 2 & x >> 15 & 1) << 30), y) for x, y in test_rows()]
    positives = [r for r, y in rows if y]
    negatives = [r for r, y in rows if not y]
    assert (len(positives), len(negatives)) == (52, 468)
    columns = [sum(1 << k for k, p in enumerate(positives) if p >> w & 1) for w in range(31)]
    supports = [a & b for a in columns for b in columns]
    old = int(data["previous_mask"], 16)
    remaining = {k for k, s in enumerate(supports) if s & ~old}
    assert len(remaining) == 104
    for family in data["families"]:
        mask = int(family["mask"], 16)
        indices = family["negative_indices"]
        assert len(indices) == len(set(indices)) == 257
        assert all(0 <= i < len(negatives) for i in indices)
        covered = {k for k in remaining if not supports[k] & ~mask}
        assert covered and sorted(covered) == family["new_codes"]
        eligible = [p for k, p in enumerate(positives) if not mask >> k & 1]
        for a, b in combinations(indices, 2):
            union = negatives[a] | negatives[b]
            assert any(p & ~union == 0 for p in eligible)
        remaining -= covered
        print(hex(mask), len(covered), len(remaining))
    assert not remaining


if __name__ == "__main__":
    main()
