"""Allow every later paid gate to use the result of one preloaded first paid gate."""
from collections import Counter
from itertools import combinations_with_replacement

from order3_case35_flat_paid import optimum
from order3_case35_star_packings import PREFIX13, POINT7, columns
from order3_prefix_search import test_rows


def survey(pool):
    # At this boundary only guard ANDs may intervene before the first paid gate.
    operands = set(pool) | {v & pool[32] for v in pool}
    products = sorted({a & b for a,b in combinations_with_replacement(operands, 2)})
    counts = Counter()
    for value in products:
        *_, needed = optimum(pool + (value,), verify_separated=False)
        counts[needed] += 1
    return len(products), sorted(counts.items())


if __name__ == "__main__":
    base = tuple(columns(PREFIX13 + POINT7, test_rows()))
    pool = base + (base[8] | base[25], base[13] | base[42], base[5] | base[18])
    for w in (base, pool):
        print(len(w), survey(w), flush=True)
