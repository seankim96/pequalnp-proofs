"""Check shared 19-flag slices for gates five and six of the fixed case-35 prefix."""
from collections import Counter
from functools import cache
from itertools import combinations_with_replacement, product

from order3_case35_fifth_15_17 import prefix
from order3_case35_or_slices import CUTS
from order3_prefix_search import test_rows


def all_full_slices(rows, base):
    # The 26 raw coordinates have 19 zeros on each negative. A 19-flag
    # slice must spend exactly one distinct zero coordinate per positive.
    # Enumerate one incident flag per zero coordinate, then test derived wires.
    for n, (negative, _) in enumerate(rows[52:]):
        assert negative.bit_count() == 7
        choices = {}
        for i, (positive, _) in enumerate(rows[:52]):
            uncovered = positive & ~negative
            assert uncovered
            if uncovered.bit_count() == 1:
                choices.setdefault(uncovered, []).append(1 << i)
        assert len(choices) == 19
        rejected = [w for w in base[26:] if not w >> (52+n) & 1]
        for flags in product(*choices.values()):
            mask = sum(flags)
            if all((w & mask).bit_count() <= 1 for w in rejected):
                yield n, mask


def replay():
    rows = test_rows()
    base = [sum(1 << i for i, (r, _) in enumerate(rows) if prefix(r) >> j & 1)
            for j in range(30)]
    assert len(rows) == 520 and all(y == (i < 52) for i, (_, y) in enumerate(rows))
    assert all(0 <= n < 468 and flags < 1 << 52 and flags.bit_count() == 19
               for n, flags in CUTS)

    @cache
    def fits(column):
        return sum(1 << k for k, (n, flags) in enumerate(CUTS)
                   if column >> (52 + n) & 1 or (column & flags).bit_count() <= 1)

    def outputs(wires):
        for a, b in combinations_with_replacement(range(len(wires)), 2):
            weight = 1 + (a != b)
            yield wires[a] & wires[b], weight
            yield wires[a] | wires[b], weight

    def weighted_outputs(wires):
        counts = Counter()
        for col, weight in outputs(wires):
            counts[col] += weight
        return counts

    common = (1 << len(CUTS)) - 1
    for c in base:
        common &= fits(c)
    fifths = weighted_outputs(base)
    covered = 0
    missed = 0
    matched_at_eighteen = 0
    uncertified = Counter()
    first_miss = None
    for fifth, weight5 in fifths.items():
        usable = common & fits(fifth)
        assert usable
        for sixth, weight6 in weighted_outputs([*base, fifth]).items():
            weight = weight5 * weight6
            if usable & fits(sixth):
                covered += weight
                continue
            missed += weight
            uncertified[(fifth, sixth)] += weight
            if first_miss is None:
                first_miss = (fifth, sixth)
            # Restrict the catalogue to 18 flags by deleting a single flag.
            for k, (n, flags) in enumerate(CUTS):
                if not (common >> k & 1):
                    continue
                a, b = (0 if c >> (52 + n) & 1 else c & flags for c in (fifth, sixth))
                if max(a.bit_count(), b.bit_count()) <= 2 and (
                        min(a.bit_count(), b.bit_count()) < 2 or a & b):
                    matched_at_eighteen += weight
                    break
    assert covered + missed == (2 * 30**2) * (2 * 31**2)
    print('ordered pairs with 19 flags:', covered)
    print('additional ordered pairs with 18 flags:', matched_at_eighteen)
    print('remaining pairs outside these certificates:', missed - matched_at_eighteen)
    # Test catalogue misses against every possible full-size cut. Cache one
    # packed bitset per output column so the pair query is a single AND.
    full = list(all_full_slices(rows, base))

    @cache
    def all_fits(column):
        packed = bytearray((len(full) + 7) // 8)
        for i, (n, flags) in enumerate(full):
            if column >> (52+n) & 1 or (column & flags).bit_count() <= 1:
                packed[i//8] |= 1 << (i%8)
        return int.from_bytes(packed, 'little')

    recovered = sum(weight for (f, g), weight in uncertified.items() if all_fits(f) & all_fits(g))
    print('all 19-flag cuts compatible with the fixed four gates:', len(full))
    print('distinct signal pairs outside the catalogue:', len(uncertified))
    print('additional ordered gate pairs with a full-size cut:', recovered)
    print('ordered gate pairs with no possible 19-flag cut:', missed - recovered)
    if first_miss:
        wires = base.copy()
        for col in first_miss:
            witness = next((op, i, j) for i, j in combinations_with_replacement(range(len(wires)), 2)
                           for op, value in [('AND', wires[i] & wires[j]), ('OR', wires[i] | wires[j])]
                           if value == col)
            print('first pair outside the 19-flag catalogue:', *witness)
            wires.append(col)


if __name__ == '__main__':
    replay()
