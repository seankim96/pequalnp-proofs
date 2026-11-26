"""Check two-line exceptions using only full flags and their two singleton inputs."""
from collections import Counter
from itertools import combinations_with_replacement
from order3_case35_third import base_row
from order3_prefix_search import test_rows

def replay():
    flags = [r for r, y in test_rows() if y]
    def signature(j):
        values = [v for raw in flags for v in (raw, raw & 8191, raw & ~8191)]
        return sum(1 << i for i, v in enumerate(values) if base_row(v) & (1 << j))
    wires = [signature(j) for j in range(28)]
    full = sum(1 << (3 * i) for i in range(52))
    def exceptions(x):
        return x & full & ~(x >> 1 | x >> 2)
    def outputs(pool):
        for a,b in combinations_with_replacement(range(len(pool)),2):
            weight = 1 + (a != b)
            yield pool[a] & pool[b], weight
            yield pool[a] | pool[b], weight
    third = Counter()
    for x,w in outputs(wires):
        third[x] += w
    distribution = Counter()
    for x,w in third.items():
        bad = exceptions(x)
        for y,z in outputs([*wires,x]):
            distribution[bad | exceptions(y)] += w*z
    counts = Counter()
    for mask,weight in distribution.items():
        lines = sum(bool(mask & (4095 << (12 * i))) for i in range(13))
        counts[lines] += weight
    assert sum(counts.values()) == 2637376 and max(counts) == 2
    print("ordered choices by number of exceptional lines", sorted(counts.items()),
          "distinct exception masks", len(distribution))

if __name__ == "__main__":
    replay()
