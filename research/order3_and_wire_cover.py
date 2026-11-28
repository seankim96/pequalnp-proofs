"""Apply the AND input wire cover bound to prefixes of the order-three plane problem."""
from collections import Counter, defaultdict

from order3_case35_star_packings import POINT7, PREFIX13, columns
from order3_prefix_search import representatives, test_rows


def minimal_covers(prefix):
    covers = {frozenset()}
    for is_and, left, right in prefix:
        if not is_and or left == right:
            continue
        candidates = {cover | {wire} for cover in covers for wire in (left, right)}
        covers = {cover for cover in candidates if not any(other < cover for other in candidates)}
    return covers


def cover_bounds(prefix, rows):
    wires = columns(prefix, rows)
    negative_rows = [i for i, (_, value) in enumerate(rows) if not value]
    bounds = Counter()
    for cover in minimal_covers(prefix):
        # The other m-|cover| observations give at most 2^(m-|cover|) patterns
        # inside any one group of negative rows with identical prefix values.
        indices = sorted(cover)
        fibers = Counter(tuple((wires[k] >> j) & 1 for k in indices) for j in negative_rows)
        largest = max(fibers.values())
        bounds[len(cover) + (largest - 1).bit_length()] += 1
    return bounds


def main():
    rows = test_rows()
    groups = defaultdict(list)
    for case, prefix in enumerate(representatives()):
        groups[min(cover_bounds(prefix, rows))].append(case)
    for bound, cases in sorted(groups.items()):
        print(f'Two-gate cases requiring at least {bound} covering wires ({len(cases)} cases):', *cases)
    prefix = PREFIX13 + POINT7
    for depth in (7, 8, 9, 10, 13, 17):
        bounds = cover_bounds(prefix[:depth], rows)
        print(f'Case 35 after {depth} gates: minimum {min(bounds)}; '
              f'minimal prefix covers by bound {dict(sorted(bounds.items()))}')


if __name__ == '__main__':
    main()
