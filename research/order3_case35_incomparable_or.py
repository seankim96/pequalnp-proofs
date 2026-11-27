"""Replay tight flag packings at OR(4,5), OR(10,13), OR(7,22)."""
from itertools import combinations_with_replacement

from order3_case35_first_or import packing
from order3_case35_star_packings import PREFIX13, POINT7, columns
from order3_prefix_search import test_rows


# Width-17 packings on five negative rows. With sixteen ORs
# left, every OR must be charged by PlaneIncomparableOrBudget on each row.
CERTIFICATES = (
    (270, (0,6,9,12,16,20,21,22,23,26,27,28,32,40,46,47,48)),
    (290, (0,7,9,12,16,21,24,26,27,28,32,33,35,40,44,47,48)),
    (306, (0,5,8,12,16,20,21,22,23,28,32,37,39,40,45,46,48)),
    (307, (0,6,9,12,16,23,24,26,27,28,32,36,39,40,44,46,48)),
    (310, (0,6,9,12,16,20,21,22,23,26,27,28,32,39,40,46,48)),
    (270, (2,6,9,12,16,20,21,22,23,26,27,28,32,40,46,47,48)),
    (270, (0,6,9,12,17,20,21,22,23,26,27,28,32,40,46,47,48)),
    (270, (0,6,9,12,16,20,21,22,23,26,27,28,32,42,46,47,48)),
    (270, (0,6,9,12,16,20,21,22,23,27,28,32,38,40,46,47,48)),
    (306, (0,5,8,12,16,20,21,22,23,28,32,37,39,40,45,46,49)),
    (306, (5,8,12,16,20,21,22,23,28,32,37,38,39,40,45,46,48)),
    (306, (0,5,8,12,20,21,22,23,24,28,32,37,39,40,45,46,48)),
)


def fourth_counts(certificates=CERTIFICATES):
    base = tuple(columns(PREFIX13 + POINT7, test_rows()))
    pool = base + (base[4] | base[5], base[10] | base[13], base[7] | base[22])
    if any(len(flags) != 17 for _, flags in certificates):
        raise ValueError("expected a tight width-17 packing")
    tests = [packing(pool, cert) for cert in certificates]
    # Only guard ANDs may occur before this fourth OR.
    operands = set(pool) | {v & base[32] for v in pool}
    total, silent, incomparable = set(), set(), set()
    for a,b in combinations_with_replacement(sorted(operands), 2):
        out = a | b
        total.add(out)
        if all(not (out >> (52+j) & 1) for j,_ in tests):
            silent.add(out)
            if all((a & ~b & mask) and (b & ~a & mask) for _,mask in tests):
                incomparable.add(out)
    return len(total), len(silent), len(incomparable)


if __name__ == "__main__":
    for count in (5, len(CERTIFICATES)):
        print(count, "packings: all, silent, incomparable", fourth_counts(CERTIFICATES[:count]))
