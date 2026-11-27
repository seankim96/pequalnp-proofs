"""Check dual cover requirements on the 52 positive pivots after prepaying ORs."""
from collections import Counter
from itertools import combinations_with_replacement

from order3_case35_star_packings import PREFIX13, POINT7, columns
from order3_prefix_search import test_rows


def cover_requirements(pool):
    guard = pool[32]
    negatives = (1 << 468) - 1
    hard = []
    for pivot in range(52):
        # Retain exactly the negatives not already separated by the guard.
        required = guard >> 52 if guard >> pivot & 1 else negatives
        reject = [required & ~(wire >> 52) for wire in pool if wire >> pivot & 1]
        if not required or any(mask == required for mask in reject):
            continue
        if not any(a | b == required for a, b in combinations_with_replacement(reject, 2)):
            raise ValueError("a positive pivot needs more than two initial wires")
        hard.append((pivot, required))
    return hard


def paid_product_survey(pool):
    hard = cover_requirements(pool)
    # Before further ORs/paid gates, every input is in this guard-closed pool.
    operands = set(pool) | {wire & pool[32] for wire in pool}
    products = {a & b for a, b in combinations_with_replacement(operands, 2)}
    counts = Counter(sum(not (value >> p & 1 and not ((value >> 52) & required))
                         for p, required in hard) for value in products)
    return len(hard), len(products), sorted(counts.items())


if __name__ == "__main__":
    base = tuple(columns(PREFIX13 + POINT7, test_rows()))
    x = base[8] | base[25]
    y = base[13] | base[42]
    z = base[5] | base[18]
    for pool in (base, base + (x,), base + (x, y, z)):
        print(len(pool), paid_product_survey(pool))
