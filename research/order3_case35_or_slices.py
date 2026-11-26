"""Replay 19- and 18-flag slices after the fourth gate of case 35."""
from collections import Counter
from functools import cache
from itertools import combinations_with_replacement

from order3_case35_third import base_row
from order3_prefix_search import test_rows

# (negative index, bit mask of positive indices)
CUTS = (
    (421, 0x71c142424f412),
    (270, 0x1f4411ba21284),
    (41, 0x88284f2418d51),
    (158, 0x212cf121d4112),
    (135, 0x448d81f131812),
    (79, 0x1218d24f812a1),
    (247, 0x4b12248816f81),
    (276, 0x27114c124f121),
    (436, 0x61bf114121212),
    (350, 0x71424881cf818),
    (176, 0x88684488b8f18),
    (88, 0x1818b1f211294),
    (50, 0x84828f8718868),
    (274, 0x19224f2424d48),
    (287, 0x2f44511e11124),
    (2, 0x121242881fcb1),
    (198, 0x21f24511e8112),
    (415, 0xb225f22484214),
    (427, 0xf1e111c121214),
    (126, 0x141b814c112f1),
    (244, 0x4b22242414fc1),
    (13, 0x124242498ef88),
    (375, 0xf4828b8146812),
    (349, 0xe1424881f4a12),
    (307, 0x4f1524b821244),
    (239, 0x22f9724181214),
    (48, 0x21828e115f112),
    (273, 0x1f124524144e1),
    (138, 0x141e115f21244),
    (94, 0x884498df18281),
    (246, 0x171224881f4a1),
    (306, 0x2f17111c11121),
    (51, 0x88181f8522d41),
    (232, 0x21bf2118a1124),
    (290, 0x1b11f13211281),
    (402, 0x612f8124b1214),
)

def check():
    rows = test_rows()
    columns = [sum(1 << i for i, (r, _) in enumerate(rows) if base_row(r) & (1 << j))
               for j in range(28)]
    cuts = [(1 << (52 + n), flags) for n, flags in CUTS]
    assert all(0 <= n < 468 and mask.bit_length() <= 52 and mask.bit_count() == 19
               for n, mask in CUTS)
    def small(signal, negative, flags):
        return bool(signal & negative) or (signal & flags).bit_count() <= 1
    assert all(small(w, n, p) for w in columns for n, p in cuts)

    @cache
    def fits(signal):
        return sum(1 << i for i, (n, p) in enumerate(cuts) if small(signal, n, p))

    def outputs(wires):
        for a, b in combinations_with_replacement(range(len(wires)), 2):
            count = 1 + (a != b)
            yield wires[a] & wires[b], count
            yield wires[a] | wires[b], count

    third_counts = Counter()
    for third, count in outputs(columns):
        third_counts[third] += count
    missing = Counter()
    covered = 0
    for third, weight in third_counts.items():
        for fourth, count in outputs([*columns, third]):
            if fits(third) & fits(fourth):
                covered += weight * count
            else:
                missing[(third, fourth)] += weight * count
    assert covered == 2633616 and sum(missing.values()) == 3760 and len(missing) == 940

    # Shrink a 19-flag slice by one for each remaining pair of signals.
    # A negative-accepting signal has empty support on any of its slices.
    def can_shrink(third, fourth):
        for n, p in cuts:
            x = 0 if third & n else third & p
            y = 0 if fourth & n else fourth & p
            if max(x.bit_count(), y.bit_count()) > 2:
                continue
            if x.bit_count() < 2 or y.bit_count() < 2 or x & y:
                return True
        return False

    recovered = sum(w for (c,d), w in missing.items() if can_shrink(c,d))
    assert recovered == sum(missing.values())
    print("19 flags:", covered, "ordered pairs; 18 flags:", recovered,
          "additional pairs; no certificate in catalogue:", 3760 - recovered)
    return recovered


if __name__ == "__main__":
    check()
