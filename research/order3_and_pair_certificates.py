"""Check the nine-AND separation premise for every fourth gate in the case-6 AND(1,13) branch."""
from functools import lru_cache
from order3_prefix_search import test_rows


def prefix(row):
    def bit(i):
        return (row >> i) & 1
    return row | ((bit(0) & bit(13)) << 26) | ((bit(0) | bit(14)) << 27) | ((bit(1) & bit(13)) << 28)


def main():
    rows = test_rows()
    pos = [prefix(row) for row, label in rows if label]
    neg = [prefix(row) for row, label in rows if not label]
    # matches[i][p] contains every j whose union with negative i covers p.
    @lru_cache(None)
    def containing(bits):
        return sum(1 << j for j, row in enumerate(neg) if row & bits == bits)
    matches = [[containing(p & ~n) for p in pos] for n in neg]
    full = (1 << len(neg)) - 1
    columns = [tuple(sum(1 << j for j, row in enumerate(side) if row >> k & 1)
                     for side in (pos, neg)) for k in range(29)]

    @lru_cache(None)
    def certificate(pcol, ncol):
        # Retain a negative only when every pair involving it still has a witness.
        selected = 0
        for i, by_positive in enumerate(matches):
            covered = 0
            for p, possible in enumerate(by_positive):
                if pcol >> p & 1 and not (ncol >> i & 1):
                    possible &= ncol
                covered |= possible
                if covered & selected == selected:
                    selected |= 1 << i
                    break
        return selected

    sizes = []
    for code in range(1682):
        a, b = columns[code // 29 % 29], columns[code % 29]
        pcol, ncol = ((x & y if code >= 841 else x | y) for x, y in zip(a, b))
        chosen = certificate(pcol, ncol)
        assert chosen & ~full == 0
        sizes.append(chosen.bit_count())
        if code in (84, 858):
            # Independent direct check on the code-84 branch and the first minimum.
            def extend(row):
                left, right = (row >> (code // 29 % 29)) & 1, (row >> (code % 29)) & 1
                value = left & right if code >= 841 else left | right
                return row | (value << 29)
            accepted = [extend(row) for row in pos]
            selected = [extend(row) for i, row in enumerate(neg) if chosen >> i & 1]
            for i, left in enumerate(selected):
                for right in selected[:i]:
                    assert any(p & ~(left | right) == 0 for p in accepted)
    print(f"Fourth gates: {len(sizes)}, distinct columns: {certificate.cache_info().currsize}")
    print(f"Smallest certificate: {min(sizes)}, largest: {max(sizes)}, code 84: {sizes[84]}")
    print(f"First minimum code: {sizes.index(min(sizes))}")
    assert min(sizes) >= 257


if __name__ == "__main__":
    main()
