"""Check the eighth-gate exception census and replay the Lean endpoint certificate."""
from collections import Counter
from functools import cache
from itertools import combinations
import re

from order3_case35_fifth_15_17 import prefix
from order3_case35_sixth_and_exceptions import gates
from order3_prefix_search import ROOT, test_rows


def certificate(module):
    source = (ROOT / "lean/PEqualNP/Research" / (module + ".lean")).read_text()
    packed = int(re.search(r"private def charged .*? := \((0x[0-9a-f]+) >>>", source)[1], 16)
    removed = int(re.search(r"private def removed : Nat := (0x[0-9a-f]+)", source)[1], 16)
    board = [(packed >> (468*p)) & ((1 << 468) - 1) for p in range(52)]
    return removed, board


def replay():
    removed, board = certificate("PlaneCase35EighthTraceBound")
    rows = test_rows()
    pos = [prefix(row) for row, yes in rows if yes]
    neg = [prefix(row) for row, yes in rows if not yes]
    cols = [sum(1 << i for i, (row, _) in enumerate(rows) if prefix(row) >> k & 1)
            for k in range(30)]
    fifth, sixth = cols[13] & cols[26], cols[13] & cols[27]
    outside = ((1 << 52) - 1) ^ 15
    assert not (fifth | sixth) & outside
    pool = [*cols, fifth, sixth]

    @cache
    def missing(signal):
        flags = signal & outside
        for parent in pool:
            if not parent & ~signal:
                flags &= ~parent
        return flags

    counts = Counter()
    # Swapping wires 30 and 31 permutes the operand choices bijectively.
    for x, nx in gates(pool).items():
        for y, ny in gates([*pool, x]).items():
            counts[(missing(x) | missing(y)).bit_count()] += 2 * nx * ny
    assert sum(counts.values()) == 2 * (2*32**2) * (2*33**2)
    assert max(counts) <= 2
    seventh, eighth = pool[0] & pool[17], pool[0] & pool[23]
    fixed_mask = missing(seventh) | missing(eighth)
    assert fixed_mask == (1 << 16) | (1 << 40)
    ninth = Counter()
    for signal, weight in gates([*pool, seventh, eighth]).items():
        ninth[(fixed_mask | missing(signal)).bit_count()] += weight
    assert ninth == {2: 2200, 3: 112}
    print("Ninth-gate census with AND(0,17), AND(0,23) fixed:", sorted(ninth.items()))
    removed9, board9 = certificate("PlaneCase35NinthTraceBound")
    assert removed9 == (removed | board[16] | board[40])
    assert board9 == [w & ~removed9 for w in board]
    assert removed9.bit_count() == 162 and max(w.bit_count() for w in board9) <= 45
    keep = [i for i in range(468) if not removed >> i & 1]
    assert not any(board[:4]) and removed.bit_count() == 96
    assert max(w.bit_count() for w in board) == 45
    assert not any(w & removed for w in board)
    checked = 0
    for i, j in combinations(keep, 2):
        union = neg[i] | neg[j]
        ends = (1 << i) | (1 << j)
        assert any(ends & w and not flag & ~union for flag, w in zip(pos, board))
        checked += 1
    print("Ordered gate pairs by number of further exceptions:", sorted(counts.items()))
    print("Negative pairs certified:", checked, "surviving any two flag omissions >=", len(keep)-2*45)


if __name__ == "__main__":
    replay()
