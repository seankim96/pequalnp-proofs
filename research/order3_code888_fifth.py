"""Finite fifth-gate separation certificates after case 6, fourth code 888."""
from itertools import combinations
from random import Random

from order3_and_pair_certificates import prefix
from order3_prefix_search import test_rows
from order3_robust_flag_families import select


WIRES = 30
HALF = WIRES * WIRES
ALL = (1 << (2 * HALF)) - 1


def start(row):
    return prefix(row) | (((row >> 1) & (row >> 18) & 1) << 29)


def outputs(row):
    """Bit k gives the value of ordered fifth gate k on this row."""
    result = 0
    for left in range(WIRES):
        for right in range(WIRES):
            code = WIRES * left + right
            x, y = (row >> left) & 1, (row >> right) & 1
            result |= (x | y) << code
            result |= (x & y) << (HALF + code)
    return result


def obstructions(positives, negatives):
    """For each negative pair, identify fifth gates that destroy all positive witnesses."""
    positive_outputs = [outputs(row) for row in positives]
    negative_outputs = [outputs(row) for row in negatives]
    conflicts = []
    for j, right in enumerate(negatives):
        current = []
        for i, left in enumerate(negatives[:j]):
            union = left | right
            witnesses = [c for p, c in zip(positives, positive_outputs) if p & ~union == 0]
            # A candidate fifth gate destroys the pair if it is true on every
            # available witness and false on both negatives.
            if witnesses:
                lost = ALL & ~(negative_outputs[i] | negative_outputs[j])
                for column in witnesses:
                    lost &= column
            else:
                lost = ALL
            current.append(lost)
        conflicts.append(current)
    return conflicts


def certificate(conflicts, group):
    blocked = [0] * len(conflicts)
    for j, entries in enumerate(conflicts):
        for i, mask in enumerate(entries):
            if mask & group:
                blocked[j] |= 1 << i
                blocked[i] |= 1 << j
    chosen = select([blocked], 0)
    if len(chosen) < 257:
        raise ValueError(f"found only {len(chosen)} negatives")
    invalid = 0
    for i, j in combinations(chosen[:257], 2):
        invalid |= conflicts[j][i]
    assert not invalid & group
    return chosen, ALL & ~invalid


def direct_pair_check(positives, negatives, chosen, code):
    """Check a full certificate without using packed gate columns."""
    def extend(row):
        x = row >> (code // WIRES % WIRES) & 1
        y = row >> (code % WIRES) & 1
        return row | ((x & y if code >= HALF else x | y) << WIRES)

    ps = list(map(extend, positives))
    selected = [extend(negatives[i]) for i in chosen[:257]]
    for left, right in combinations(selected, 2):
        assert any(p & ~(left | right) == 0 for p in ps)


def main():
    tests = test_rows()
    positives = [start(r) for r, y in tests if y]
    negatives = [start(r) for r, y in tests if not y]
    conflicts = obstructions(positives, negatives)
    # Pairs without any witness conflict with every gate. Other pairs can
    # become incompatible only for the codes in this union.
    dangerous = 0
    for row in conflicts:
        for mask in row:
            if mask != ALL:
                dangerous |= mask
    # A gate and its operand swap give identical columns.
    pending = [k for k in range(2 * HALF) if dangerous >> k & 1
               and k // WIRES % WIRES <= k % WIRES]
    assert len(pending) == 56
    Random(0).shuffle(pending)
    covered = 0
    for index in range(3):
        codes = pending[index::3]
        chosen, valid = certificate(conflicts, sum(1 << k for k in codes))
        direct_pair_check(positives, negatives, chosen, codes[0])
        covered |= valid
        print(f"group {index+1}: {len(chosen)} negatives, {valid.bit_count()} valid fifth gates,"
              f" independent pair replay at {codes[0]}, cumulative {covered.bit_count()}")
    assert covered == ALL


if __name__ == "__main__":
    main()
