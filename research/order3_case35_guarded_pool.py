"""Replay the six-flag certificate and count guarded prefixes with ordered operands."""
from collections import Counter
from itertools import combinations, product

from order3_case35_eighth_guard import certificate
from order3_case35_fifth_15_17 import prefix
from order3_case35_sixth_and_exceptions import gates
from order3_prefix_search import test_rows

GUARD = 15 | (1 << 16) | (1 << 40)
OUTSIDE = ((1 << 52) - 1) ^ GUARD


def replay():
    rows = test_rows()
    pos = [prefix(v) for v, y in rows if y]
    neg = [prefix(v) for v, y in rows if not y]
    base = [sum(1 << r for r, (v, _) in enumerate(rows) if prefix(v) >> k & 1)
            for k in range(30)]
    pool = [*base, base[13] & base[26], base[13] & base[27]]
    assert all(not x & OUTSIDE for x in pool[30:])
    removed, charges = certificate("PlaneCase35GuardedPoolTraceBound")
    assert removed.bit_count() == 120 and max(w.bit_count() for w in charges) == 44
    assert not any(w & removed for w in charges)
    assert not any(w for i, w in enumerate(charges) if GUARD >> i & 1)
    survivors = [i for i in range(468) if not removed >> i & 1]
    pairs = 0
    for i, j in combinations(survivors, 2):
        union, ends = neg[i] | neg[j], (1 << i) | (1 << j)
        assert any(w & ends and not v & ~union for v, w in zip(pos, charges))
        pairs += 1
    print("independently checked negative pairs:", pairs)
    seventh = Counter()
    new = set()
    for a, b in product(range(32), repeat=2):
        for name, x in (("AND",pool[a] & pool[b]), ("OR",pool[a] | pool[b])):
            if not x & OUTSIDE:
                seventh[name] += 1
                if x not in pool and x & GUARD and x >> 52:
                    new.add(x)
    print("silent seventh choices by operator, per fifth/sixth order:", dict(seventh))
    print("distinct new seventh columns meeting both some positive and some negative:", len(new))
    # gates() merges equal 520-row signals but preserves ordered syntactic multiplicities.
    eighth = sum(mult * sum(v for y, v in gates([*pool, x]).items() if not y & OUTSIDE)
                 for x, mult in gates(pool).items() if not x & OUTSIDE)
    ninth_family = 2 * sum(seventh.values()) * (2*33**2) * (2*34**2)
    tenth_family = 2 * eighth * (2*34**2) * (2*35**2)
    print("ordered guarded seventh/eighth pairs per fifth/sixth order:", eighth)
    print("ordered ninth-prefix family:", ninth_family)
    print("ordered tenth-prefix family:", tenth_family)
    assert not ((pool[0] & pool[17]) | (pool[0] & pool[23])) & OUTSIDE
    print("four previously fixed eighth-prefix orders, arbitrary ninth and tenth:",
          4 * (2*34**2) * (2*35**2))
    chosen = [(13,26), (13,27)]
    for a, b in combinations(range(30), 2):
        x = base[a] & base[b]
        if not x & OUTSIDE and x >> 52 and x not in pool:
            chosen.append((a,b))
            pool.append(x)
            if len(chosen) == 30:
                assert len(set(pool)) == 60
                print("30 distinct guarded ANDs, each nonzero on a negative:", chosen)
                return
    raise AssertionError("could not construct prefix")


if __name__ == "__main__":
    replay()
