"""Replay the 21-row obstruction and synthesize a conjunction on the same rows."""
from itertools import combinations
from functools import lru_cache
from order3_case35_flat_paid import PREFIX13, POINT7, SEPARATED, columns, join, test_rows

NEGATIVES = (49, 76, 200, 254, 298, 321, 361, 374, 435, 453)


def analyze():
    base = tuple(columns(PREFIX13 + POINT7, test_rows()))
    sources = base + tuple(v & base[32] for v in base)
    negatives = [52 + i for i in NEGATIVES]
    for p in SEPARATED:
        assert all(any(v >> j & 1 for j in negatives) for v in sources if v >> p & 1)
    for p, q in combinations(SEPARATED, 2):
        minimal_sides = {u | v for u in sources if u >> p & 1 for v in sources if v >> q & 1}
        assert any(all(sum(v >> j & 1 for j in triple) >= 2 for v in minimal_sides)
                   for triple in combinations(negatives, 3))

    # Any clause that rejects a given set of negatives can be enlarged to
    # include every source that vanishes on that set, preserving all positives.
    all_negative = (1 << len(negatives)) - 1
    clauses = {}
    for mask in range(1, all_negative + 1):
        chosen = [i for i, v in enumerate(sources)
                  if all(not (v >> j & 1) for k, j in enumerate(negatives) if mask >> k & 1)]
        val = join(sources[i] for i in chosen)
        if all(val >> p & 1 for p in SEPARATED):
            coverage = sum((1 - (val >> j & 1)) << k for k, j in enumerate(negatives))
            clauses[coverage] = chosen, val

    @lru_cache(None)
    def cover(remaining):
        if not remaining:
            return ()
        return min(((k,) + cover(remaining & ~k) for k in clauses if k & (remaining & -remaining)),
                   key=len)

    witness = cover(all_negative)
    full = (1 << 520) - 1
    for k in witness:
        chosen, val = clauses[k]
        # Remove redundant literals while preserving the 11 required positives.
        active = list(chosen)
        for i in chosen:
            trial = join(sources[t] for t in active if t != i)
            if all(trial >> p & 1 for p in SEPARATED):
                active.remove(i)
        val = join(sources[t] for t in active)
        full &= val
        print("OR sources", active)
    assert all(full >> p & 1 for p in SEPARATED)
    assert not any(full >> j & 1 for j in negatives)
    print("minimum CNF clauses", len(witness), "binary ANDs", len(witness)-1,
          "full-table accepted positives", (full & ((1 << 52)-1)).bit_count(),
          "accepted negatives", (full >> 52).bit_count())


if __name__ == "__main__":
    analyze()
