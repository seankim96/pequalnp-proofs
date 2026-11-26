"""A triple-cost certificate for discarding four flags beyond flags 0 through 3."""
from collections import defaultdict
from itertools import combinations
from math import comb
import re

from order3_case35_fifth_15_17 import prefix
from order3_prefix_search import ROOT, test_rows


def replay():
    rows = test_rows()
    high = [prefix(r) for r, yes in rows if yes][4:]
    negatives = [prefix(r) for r, yes in rows if not yes]
    ends = defaultdict(int)
    for i, j in combinations(range(len(negatives)), 2):
        union = negatives[i] | negatives[j]
        witnesses = sum(1 << k for k, row in enumerate(high) if not row & ~union)
        if witnesses.bit_count() <= 4:
            ends[witnesses] |= 1 << j
    # An endpoint present in a proper subset is already removed whenever this mask is.
    # Descending sizes leave every subset in its original form until all its supersets are done.
    reduced = dict(ends)
    for mask in sorted(ends, key=int.bit_count, reverse=True):
        sub = mask
        while sub:
            sub = (sub - 1) & mask
            reduced[mask] &= ~ends.get(sub, 0)
    weights = {m: w.bit_count() for m, w in reduced.items()}
    # A future Lean checker needs only this local property and the bucket costs.
    # If five witnesses exist, four omissions cannot remove all five. Otherwise
    # omitting every witness necessarily removes the higher endpoint through a bucket.
    by_end = [[m for m, bits in reduced.items() if bits >> j & 1] for j in range(468)]
    direct = bucket = 0
    for i, j in combinations(range(len(negatives)), 2):
        union = negatives[i] | negatives[j]
        witnesses = sum(1 << k for k, row in enumerate(high) if not row & ~union)
        if witnesses.bit_count() >= 5:
            direct += 1
        else:
            assert any(not (mask & ~witnesses) for mask in by_end[j])
            bucket += 1
    assert direct + bucket == 109278
    print("negative pairs:", direct, "with five witnesses;", bucket, "with a bucket witness")
    print("nonempty endpoint buckets:", sum(bool(w) for w in reduced.values()),
          "bucket memberships:", sum(weights.values()))
    module = ROOT / "lean/PEqualNP/Research/PlaneCase35FourOmissionCost.lean"
    tables = [[int(w, 16) for w in packed.split(", ")]
              for packed in re.findall(r"#\[([0-9a-fx, ]+)\]", module.read_text())]
    assert len(tables) == 4 and all(len(tab) == 48 for tab in tables)
    for size in range(1, 5):
        for indices in combinations(range(48), size):
            rank = sum(comb(v, i) for i, v in enumerate(indices[:-1], 1))
            word = tables[size-1][indices[-1]]
            if size == 1:
                encoded = word
            elif size < 4:
                encoded = (word >> (3*rank)) & 7
            else:
                encoded = ((word >> (2*rank)) & 3).bit_count()
            assert encoded == weights.get(sum(1 << k for k in indices), 0)
    print("all 213,052 one- through four-flag cost entries match the Lean tables")
    flags = [1 << k for k in range(48)]
    def triple(a, b, c):
        singles = sum(weights.get(x, 0) for x in (a, b, c))
        pairs = sum(weights.get(x, 0) for x in (a | b, a | c, b | c))
        return 2*singles + 3*pairs + 6*weights.get(a | b | c, 0)
    triple_cap = max(triple(*t) for t in combinations(flags, 3))
    fourth_cap = max(v for m, v in weights.items() if m.bit_count() == 4)
    # Summing the four triple bounds counts each singleton, pair, and triple six times.
    limit = weights[0] + 4*triple_cap // 6 + fourth_cap
    assert (weights[0], triple_cap, fourth_cap, limit) == (96, 162, 2, 206)
    print("permanent:", weights[0], "max of 17,296 triple costs:", triple_cap,
          "max residual four-mask cost:", fourth_cap, "at least", 468-limit, "survivors")
    worst_count = 0
    for group in combinations(flags, 4):
        s = sum(group)
        covered = surviving_prune = total = 0
        sub = s
        while True:
            covered |= ends.get(sub, 0)
            surviving_prune |= reduced.get(sub, 0)
            total += weights.get(sub, 0)
            if sub == 0:
                break
            sub = (sub-1) & s
        assert covered == surviving_prune
        assert covered.bit_count() <= total <= limit
        worst_count = max(worst_count, total)
    assert worst_count == 194
    print("checked all 194,580 four-flag masks; worst sum of residual costs:", worst_count)


if __name__ == "__main__":
    replay()
