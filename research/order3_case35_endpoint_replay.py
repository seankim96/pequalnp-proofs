"""Replay the actual Lean endpoint slots, the local five-witness table, and the 13-flag cut."""
from itertools import combinations
from math import comb
import re

from order3_case35_fifth_15_17 import prefix
from order3_prefix_search import ROOT, test_rows


def arrays(source):
    return [[int(v, 16) for v in row.split(", ")]
            for row in re.findall(r"#\[([0-9a-fx, ]+)\]", source)]


def replay():
    base = ROOT / "lean/PEqualNP/Research"
    one, two, three, quad, keys, endpoints = arrays((base / "PlaneCase35EndpointSurvivors.lean").read_text())
    pair = (base / "PlaneCase35LocalPairCertificate.lean").read_text()
    label_section = pair.split("def labels : Array (List Nat) := #[", 1)[1].split("private def highs", 1)[0]
    labels = [[int(v, 16) for v in row.split(", ") if v]
              for row in re.findall(r"\[([0-9a-fx, ]*)\]", label_section)]
    rows = test_rows()
    pos = [prefix(x) for x, y in rows if y][4:]
    neg = [prefix(x) for x, y in rows if not y]
    assert len(pos) == 48 and len(neg) == len(labels) == 468
    assert keys == sorted(set(keys))
    memberships = [set() for _ in neg]
    for size in range(5):
        for group in combinations(range(48), size):
            m = sum(1 << p for p in group)
            if size == 0:
                slots = 96
            else:
                rank = sum(comb(p, i) for i, p in enumerate(group[:-1], 1))
                word = (one, two, three, quad)[size-1][group[-1]]
                slots = word if size == 1 else (word >> (3*rank)) & 7
                if size == 4:
                    slots = ((word >> (2*rank)) & 3).bit_count()
            lo, hi = 0, len(keys)
            for _ in range(12):
                mid = (lo + hi)//2
                key = keys[mid] if mid < len(keys) else 0
                if key == m:
                    lo = hi = mid
                elif key < m:
                    lo = mid + 1
                else:
                    hi = mid
            mid = (lo+hi)//2
            found = mid < len(keys) and keys[mid] == m
            assert found == (slots > 0)
            if found:
                js = [(endpoints[mid] >> (9*i)) & 511 for i in range(slots)]
                assert len(set(js)) == slots and max(js) < 468
                for j in js:
                    memberships[j].add(m)
    for j, ms in enumerate(memberships):
        assert sorted(ms) == labels[j]
    assert sum(map(len, memberships)) == 3812
    cut = (base / "PlaneCase35ThirteenFlagSuffix.lean").read_text()
    removed = int(re.search(r"private def removed : Nat := (0x[\da-f]+)", cut)[1], 16)
    forbidden = int(re.search(r"if \((0x[\da-f]+) : Nat\).testBit p", cut)[1], 16)
    covered = five = weak = 0
    for i,j in combinations(range(468),2):
        u = neg[i] | neg[j]
        w = sum(1 << p for p,x in enumerate(pos) if not x & ~u)
        if w.bit_count() >= 5:
            five += 1
        else:
            assert any(not m & ~w for m in memberships[j])
            weak += 1
        if not (removed >> i & 1 or removed >> j & 1):
            assert (w << 4) & ~forbidden
            covered += 1
    assert (covered, five, weak) == (32896, 90764, 18514)
    print("3812 endpoint memberships; five-or-bucket pairs:", five, weak)
    print("13 omitted positives, 257 surviving negatives, separated pairs:", covered)
    print("physical flags:", [i for i in range(52) if forbidden >> i & 1])


if __name__ == "__main__":
    replay()
