"""Enumerate optimal residual-cover extension costs. Bit i removes edge i."""
from collections import Counter

EDGES = [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6),
         (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10),
         (7, 9), (8, 9)]
SETS = range(1 << 11)
DELETIONS = range(1 << 16)
miss = [sum(1 << i for i, (a, b) in enumerate(EDGES)
            if not k & ((1 << a) | (1 << b))) for k in SETS]
covers = [t for t in SETS if not miss[t]]
assert min(t.bit_count() for t in covers) == 7
assert min(t.bit_count() for t in covers if t & 7 == 7) == 8
extra = [min((t & ~k).bit_count() for t in covers) for k in SETS]
# First minimize the residual cover size, then the number of added vertices.
best = [(12, 12, 0)] * len(DELETIONS)
for k in SETS:
    best[miss[k]] = min(best[miss[k]], (k.bit_count(), extra[k], k))
# A cover remains valid after deleting more edges.
for i in range(16):
    for u in DELETIONS:
        if u & (1 << i):
            best[u] = min(best[u], best[u ^ (1 << i)])
profile = Counter(size + added for size, added, _ in best)
assert profile == {7: 65519, 8: 17}
print('Minimum attainable full-cover size:', sorted(profile.items()))
for u, (size, added, _) in enumerate(best):
    if size + added == 8:
        opts = [k for k in SETS if k.bit_count() == size and miss[k] & ~u == 0]
        assert all(k & 7 == 7 for k in opts)
        print(f'{u:04x}  minimum {size}  extra {added}  optimal masks {opts}')
# Construct a replacement independently of U. Preserving every edge hit by K
# makes the replacement a residual cover wherever K was one.
for k in SETS:
    cap = 8 if k & 7 == 7 else 7
    assert any(j.bit_count() <= k.bit_count() and miss[j] & ~miss[k] == 0
               and j.bit_count() + extra[j] <= cap for j in SETS)
print('Verified all 2048 local exchange cases.')
