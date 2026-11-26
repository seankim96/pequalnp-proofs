"""Replay the checked mask and a two-certificate extension for the fifth gate."""
from collections import deque
from itertools import combinations
from pathlib import Path
import re

from order3_case35_fifth_15_17 import prefix
from order3_case35_third import base_row, choose_family
from order3_prefix_search import test_rows

SEED = 0x103ff
SECOND = 0xf000f10200


def maps(source, name, width, size):
    match = re.search('private def ' + name + r' : Array Nat := #\[(.*?)\]', source)
    result = []
    for word in map(lambda x: int(x, 0), match.group(1).split(',')):
        perm = [word >> (width*i) & ((1 << width) - 1) for i in range(size)]
        assert sorted(perm) == list(range(size))
        result.append(perm)
    return result


def replay():
    rows = test_rows()
    pos = [base_row(r) for r, y in rows if y]
    neg = [base_row(r) for r, y in rows if not y]
    pairs = [(a, b, sum(1 << f for f, p in enumerate(pos) if not p & ~(neg[a] | neg[b])))
             for a, b in combinations(range(468), 2)]
    witnesses = {(a, b): w for a, b, w in pairs}

    def family(mask):
        adj = [0] * len(neg)
        for a, b, w in pairs:
            if not w & ~mask:
                adj[a] |= 1 << b
                adj[b] |= 1 << a
        return choose_family(adj)

    root = Path(__file__).resolve().parents[1] / 'lean/PEqualNP/Research'
    geom = (root/'PlaneCase35AnyLines.lean').read_text()
    pm, nm = maps(geom, 'pm', 6, 52), maps(geom, 'nm', 9, 468)
    fam1, fam2 = family(SEED), family(SECOND)
    assert (len(fam1), len(fam2)) == (260, 278)
    proof = (root/'PlaneCase35FifthGuard.lean').read_text()
    packed = int(re.search(r'private def indices.*?\n  \((0x[0-9a-f]+)', proof)[1], 16)
    assert [packed >> (9*i) & 511 for i in range(257)] == fam1[:257]
    assert f'def omittedFlags : Nat := {SEED}\n' in proof

    # Search the orbit of the first certificate. Transport only its indices.
    # Every retained pair is then tested afresh on the actual 28 base wires.
    fixed = (1 << 9) | (1 << 16)
    masks = {SEED: ()}
    pending = deque([SEED])
    todo = set(range(52))
    selected = {}
    while pending and todo:
        m = pending.popleft()
        if m & fixed == fixed:
            new = {i for i in todo if m >> i & 1}
            if new:
                selected[m] = masks[m]
                todo -= new
        for g, perm in enumerate(pm):
            image = sum(1 << perm[i] for i in range(52) if m >> i & 1)
            if image not in masks:
                masks[image] = masks[m] + (g,)
                pending.append(image)
    assert todo == {*range(20, 24), *range(36, 40)}
    assert all(SECOND >> i & 1 for i in todo) and SECOND & fixed == fixed
    families = {SECOND: fam2[:257]}
    for m, path in selected.items():
        ids = fam1[:257]
        for g in path:
            ids = [nm[g][i] for i in ids]
        families[m] = ids
    for m, ids in families.items():
        assert len(set(ids)) == 257
        assert all(witnesses[a, b] & ~m for a, b in combinations(sorted(ids), 2))

    cols = [sum(1 << i for i, (r, _) in enumerate(rows) if prefix(r) >> j & 1)
            for j in range(30)]
    ps = (1 << 52) - 1
    assert cols[28] & ps == 1 << 9 and cols[29] & ps == 1 << 16
    direct = 0
    for a in cols:
        for b in cols:
            fifth = a & b
            support = fifth & ps
            direct += int(not support & ~SEED)
            # If equal to a parent on every row, any certificate for the
            # first four gates works. Otherwise choose an avoiding family.
            assert fifth in (a, b) or any(not support & ~m for m in families)
    # The standalone proof instead transports just one differently chosen
    # ten-flag mask. Reconstruct its published family, independently verify
    # all transported pairs, and check that every singleton exception fits.
    seed = 0x4020141020f
    direct_source = (root/'PlaneCase35FifthDirect.lean').read_text()
    direct_ids = family(seed)
    assert len(direct_ids) == 302 and seed & (fixed | 15) == fixed | 15
    packed = int(re.search(r'private def indices.*?\n  \((0x[0-9a-f]+)', direct_source)[1], 16)
    assert [packed >> (9*i) & 511 for i in range(257)] == direct_ids[:257]
    queue = deque([(seed, ())])
    visited = {seed}
    left = set(range(52))
    used = 0
    while left and queue:
        m, path = queue.popleft()
        new = {i for i in left if m >> i & 1}
        if m & fixed == fixed and new:
            ids = direct_ids[:257]
            for g in path:
                ids = [nm[g][i] for i in ids]
            assert len(set(ids)) == 257
            assert all(witnesses[a,b] & ~m for a,b in combinations(sorted(ids),2))
            left -= new
            used += 1
        for g, perm in enumerate(pm):
            image = sum(1 << perm[i] for i in range(52) if m >> i & 1)
            if image not in visited:
                visited.add(image)
                queue.append((image, path+(g,)))
    assert not left
    print('standalone single seed retained rows:', len(direct_ids), 'transported masks used:', used)
    print('single seed covered fifth ANDs:', direct, 'of 900')
    print('transports:', len(selected), 'maximum length:', max(map(len, selected.values())))
    print('second seed flags still needed:', sorted(todo))
    print('certificates:', len(families), 'negative pairs replayed per certificate:', 257*256//2)
    print('all 900 fifth ANDs covered in finite replay')


if __name__ == '__main__':
    replay()
