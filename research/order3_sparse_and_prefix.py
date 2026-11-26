"""Count excluded negative rows after deleting up to five positive flags."""
from itertools import combinations
from math import comb

from order3_code888_fifth import start, test_rows


def scan(code):
    def prefix(row):
        extra = ((row >> 2) & (row >> 15) & 1) << 30 if code == 975 else 0
        return start(row) | extra

    pos = [prefix(x) for x, y in test_rows() if y]
    neg = [prefix(x) for x, y in test_rows() if not y]
    # Pack the high endpoints and low endpoints in separate 468-bit fields.
    endpoints = {}
    for j, right in enumerate(neg):
        for i, left in enumerate(neg[:j]):
            union = left | right
            surviving = sum(1 << k for k, p in enumerate(pos) if p & ~union == 0)
            if surviving.bit_count() <= 5:
                endpoints[surviving] = endpoints.get(surviving, 0) | (1 << j) | (1 << (468 + i))
    low = (1 << 468) - 1
    # For a deletion set S, a pair loses all witnesses iff its mask is a subset of S.
    previous = {0: endpoints.get(0, 0)}
    for size in range(1, 6):
        current = {}
        worst = -1
        certified = 0
        example = None
        for flags in combinations(range(52), size):
            bits = [1 << p for p in flags]
            mask = sum(bits)
            banned = endpoints.get(mask, 0)
            for bit in bits:
                banned |= previous[mask ^ bit]
            if size < 5:
                current[mask] = banned
            removed = min((banned & low).bit_count(), (banned >> 468).bit_count())
            certified += removed <= 211
            if removed > worst:
                worst, example = removed, flags
        print(code, size, certified, comb(52, size), worst, example, flush=True)
        # Independent scalar check of the extremal deletion set.
        selected = [p for k, p in enumerate(pos) if k not in example]
        lo, hi = set(), set()
        for j, right in enumerate(neg):
            for i, left in enumerate(neg[:j]):
                if not any(p & ~(right | left) == 0 for p in selected):
                    lo.add(i)
                    hi.add(j)
        assert min(len(lo), len(hi)) == worst
        previous = current


if __name__ == "__main__":
    for code in (888, 975):
        scan(code)
