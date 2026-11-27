"""Check the case-35 rescued guard certificate directly on the 520 row words."""
from collections import Counter
from itertools import combinations
import json
import re
from pathlib import Path

from order3_case35_fifth_15_17 import prefix
from order3_prefix_search import test_rows


def main():
    sweep = json.loads((Path(__file__).with_name('results') /
                        'case35-guard-2-6-all-omissions.json').read_text())
    a, b, skip = 2, 6, 44
    keep = next(row['family'] for row in sweep if row['flag'] == skip)
    src = Path(__file__).resolve().parents[1] / 'lean/PEqualNP/Research/PlaneCase35RescuedGuardSuffix.lean'
    removed = re.search(r'private def removed : Nat := (0x[0-9a-f]+)', src.read_text())
    assert removed and int(removed[1], 16) == ((1 << 468)-1) ^ sum(1 << i for i in keep)
    assert len(keep) == len(set(keep)) == 257 and all(0 <= j < 468 for j in keep)
    fixed = [prefix(x) for x, _ in test_rows()]
    pos, neg = fixed[:52], fixed[52:]
    assert [p for p, x in enumerate(pos) if x & 2 and x & (1 << 24)] == [44]
    guard = 1 << a | 1 << b
    for i, j in combinations(keep, 2):
        union = neg[i] | neg[j]
        assert any(not x & ~union and (not x & guard or (neg[i] & guard and neg[j] & guard))
                   for p, x in enumerate(pos) if p >= 4 and p != skip)
    print('Checked 32,896 negative pairs and the positive support of AND(1,24).')

    # Each bit marks a possible high positive. Retain all bits except the
    # omitted flag, and verify both sides of each claimed optimum.
    pair_masks = {}
    for i, j in combinations(range(468), 2):
        union = neg[i] | neg[j]
        pair_masks[i, j] = sum(1 << p for p, x in enumerate(pos)
                               if p >= 4 and not x & ~union
                               and (not x & guard or (neg[i] & guard and neg[j] & guard)))
    assert [row['flag'] for row in sweep] == list(range(4, 52))
    sizes = {}
    for row in sweep:
        family, classes = row['family'], row['cover']
        allowed = ~(1 << row['flag'])
        assert len(classes) == len(family) == len(set(family))
        assert all(0 <= i < 468 for i in family)
        assert all(pair_masks[i,j] & allowed for i,j in combinations(sorted(family), 2))
        assert sorted(i for group in classes for i in group) == list(range(468))
        assert all(not pair_masks[i,j] & allowed for group in classes
                   for i,j in combinations(sorted(group), 2))
        sizes[row['flag']] = len(family)
    print('Maximum-size distribution:', sorted(Counter(sizes.values()).items()))
    print('Below 257:', {flag:n for flag,n in sizes.items() if n < 257})


if __name__ == '__main__':
    main()
