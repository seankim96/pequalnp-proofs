"""Replay a five-flag numerical certificate and a six-flag obstruction on the case-35 baseline."""
from itertools import combinations
from math import comb
import re

from order3_case35_fifth_15_17 import prefix
from order3_prefix_search import ROOT, test_rows


def ranked_buckets():
    rows = test_rows()
    positives = [prefix(x) for x, yes in rows if yes][4:]
    negatives = [prefix(x) for x, yes in rows if not yes]
    by_mask = {}
    neighbors = [[] for _ in negatives]
    scores = [0] * len(negatives)
    for i, j in combinations(range(len(negatives)), 2):
        union = negatives[i] | negatives[j]
        witnesses = sum(1 << t for t, p in enumerate(positives) if p & ~union == 0)
        size = witnesses.bit_count()
        if size <= 6:
            by_mask.setdefault(witnesses, []).append((i, j))
            weight = comb(48-size, 6-size)
            neighbors[i].append((j, weight))
            neighbors[j].append((i, weight))
            scores[i] += weight
            scores[j] += weight
    # Higher initial bad-pair weight gets earlier priority. Recompute after each removal.
    rank = {}
    for step in range(len(negatives)):
        i = max((n for n in range(len(negatives)) if n not in rank), key=scores.__getitem__)
        rank[i] = step
        for j, weight in neighbors[i]:
            scores[j] -= weight
    buckets = {}
    for m, pairs in by_mask.items():
        if m.bit_count() <= 5:
            endpoints = {i if rank[i] < rank[j] else j for i, j in pairs}
            buckets[m] = sum(1 << v for v in endpoints)
    return buckets, by_mask


def replay():
    buckets, pairs = ranked_buckets()
    maximum = checked = 0
    worst = None
    for group in combinations(range(48), 5):
        m = sum(1 << p for p in group)
        sub, endpoints = m, buckets[0]
        while sub:
            endpoints |= buckets.get(sub, 0)
            sub = (sub-1) & m
        lost = endpoints.bit_count()
        if lost > maximum:
            maximum, worst = lost, group
        checked += 1
    assert checked == comb(48, 5)
    print(checked, "five-high-flag masks; worst discarded:", maximum,
          "; retained:", 468-maximum, "; worst physical flags:", [p+4 for p in worst])
    assert maximum <= 211

    barrier = (ROOT / "lean/PEqualNP/Research/PlaneCase35SixOmissionBarrier.lean").read_text()
    members = [int(v, 16) for v in re.search(r"private def members : Array Nat := #\[([^\]]+)\]", barrier)[1].split(", ")]
    slots = [[(word >> (9*k)) & 511 for k in range(6)] for word in members]
    classes = [[i for i in row if i < 468] for row in slots]
    assert len(classes) == 242 and sorted(i for c in classes for i in c) == list(range(468))
    omitted = sum(1 << (p-4) for p in (8, 10, 11, 13, 14, 15))
    bad = {edge for mask, edges in pairs.items() if mask & ~omitted == 0 for edge in edges}
    assert all(tuple(sorted(edge)) in bad for c in classes for edge in combinations(c, 2))
    print("Six-high-flag obstruction: 242 cliques partition all 468 negatives;",
          sum(comb(len(c), 2) for c in classes), "within-class pairs have no surviving witness.")
    # This matching lower witness on family size makes the obstruction numerically exact.
    retained = 0xff72feddfcfcde7dc7d12261dcf523a3b57f3dcdc99bda6a151b22667d7835f63324b1f63c0b3e3311eb74a0a512a954190d819185427042d608c
    assert retained.bit_length() <= 468 and retained.bit_count() == 242
    assert all(not (retained >> i & 1 and retained >> j & 1) for i, j in bad)
    print("Exact numerical maximum family size: 242 (explicit 242-element witness).")



if __name__ == "__main__":
    replay()
