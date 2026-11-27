"""Exact paid-AND count at depth one, with OR and physical guard ANDs free."""
from functools import lru_cache
import json
from pathlib import Path

from order3_case35_guarded_covers import cover_requirements
from order3_case35_star_packings import PREFIX13, POINT7, columns
from order3_prefix_search import test_rows


POS = (1 << 52) - 1
NEG = (1 << 468) - 1
SEPARATED = (4, 8, 14, 18, 23, 27, 28, 32, 42, 46, 51)


def join(values):
    result = 0
    for value in values:
        result |= value
    return result


def product_terms(pool, guarded, hard):
    guard = pool[32]
    # Sources stand for initial wires and their physical guard-masked copies.
    sources = sorted(set(pool) | {v & guard for v in pool})
    reject = guard >> 52 if guarded else NEG
    neighbors = [sum(1 << j for j, b in enumerate(sources) if not ((a & b) >> 52 & reject))
                 for a in sources]
    neighborhoods = {(1 << len(sources)) - 1}
    for row in sorted(set(neighbors)):
        neighborhoods |= {bits & row for bits in neighborhoods}

    # Every compatible rectangle extends to one of these: intersect the
    # neighborhoods of its left inputs, then take all compatible left inputs.
    terms = {}
    for right in sorted(neighborhoods):
        left_inputs = [v for v, n in zip(sources, neighbors) if not right & ~n]
        right_inputs = [v for i, v in enumerate(sources) if right >> i & 1]
        value = join(left_inputs) & join(right_inputs)
        if guarded:
            value &= guard
        if value >> 52:
            raise ValueError("rectangle accepts a negative")
        hits = value & hard
        if hits:
            terms[hits] = left_inputs, right_inputs, guarded
    return terms, len(neighborhoods)


def optimum(pool, *, verify_separated=True):
    guard = pool[32]
    free = set(pool) | {v & guard for v in pool}
    safe = [v for v in free if not v >> 52]
    hard = POS & ~join(safe)
    if hard != sum(1 << p for p, _ in cover_requirements(pool)):
        raise ValueError("initial cover and free-wire tests disagree")
    direct, direct_count = product_terms(pool, False, hard)
    masked, masked_count = product_terms(pool, True, hard)
    terms = {**masked, **direct}
    separated = sum(1 << p for p in SEPARATED)
    if verify_separated and (separated & ~hard or any((v & separated).bit_count() > 1 for v in terms)):
        raise ValueError("a free wire or paid term violates the eleven-pivot certificate")
    maximal = sorted(v for v in terms if not any(v != u and not v & ~u for u in terms))
    by_flag = sorted(((p, [v for v in maximal if v >> p & 1])
                      for p in range(52) if hard >> p & 1), key=lambda item: len(item[1]))

    @lru_cache(None)
    def cover(todo):
        if not todo:
            return ()
        choices = next(opts for p, opts in by_flag if todo >> p & 1)
        return min(((v,) + cover(todo & ~v) for v in choices), key=len)

    selected = cover(hard)
    # Build a circuit expression for the upper bound directly from the chosen
    # rectangles. Each group of source wires is ORed before applying one AND.
    output = join(safe)
    for hits in selected:
        left, right, mask = terms[hits]
        value = join(left) & join(right)
        output |= value & guard if mask else value
    if output != POS:
        raise ValueError("constructed circuit disagrees on the 520 tests")
    return hard.bit_count(), (direct_count, masked_count), (max(v.bit_count() for v in direct),
            max(v.bit_count() for v in masked)), len(maximal), len(selected)


def replay_witness(pool):
    path = Path(__file__).with_name("results") / "case35-flat-eleven-paid-witness.json"
    witness = json.loads(path.read_text())
    wires = list(pool)
    has_paid_ancestor = [False] * len(wires)
    paid = guards = 0
    for op, a, b in witness["gates"]:
        if op not in (0, 1) or not (0 <= a < len(wires) and 0 <= b < len(wires)):
            raise ValueError("invalid physical gate")
        is_paid = bool(op and 32 not in (a, b))
        inherited = has_paid_ancestor[a] or has_paid_ancestor[b]
        if is_paid and inherited:
            raise ValueError("paid gates have a dependency")
        paid += is_paid
        guards += bool(op and not is_paid)
        has_paid_ancestor.append(is_paid or inherited)
        wires.append(wires[a] & wires[b] if op else wires[a] | wires[b])
    output = witness["output"]
    if not (0 <= output < len(wires)) or wires[output] != POS or paid != 11:
        raise ValueError("incorrect eleven-paid-AND witness")
    return paid, guards, len(witness["gates"]) - paid - guards


if __name__ == "__main__":
    base = tuple(columns(PREFIX13 + POINT7, test_rows()))
    pool = base + (base[8] | base[25], base[13] | base[42], base[5] | base[18])
    print("witness suffix (paid AND, guard AND, OR)", replay_witness(base))
    for k in range(7, 17):
        print("prefix length, optimum", k, optimum(base[:26+k], verify_separated=False)[-1])
    for w in (base, pool):
        print("pool, hard pivots, neighborhood counts, maximum hits, maximal masks, optimum",
              len(w), optimum(w))
