"""Flag-packing bounds after star OR trees at the thirteen-gate case-35 prefix."""
from collections import Counter
from itertools import combinations_with_replacement
import json
from pathlib import Path

from order3_case35_colored_trace import density
from order3_case35_first_or import PREFIX13, columns, packing

ROOT = Path(__file__).with_name("results")
POINT7 = ((False,17,19),(False,20,24),(False,39,40),(True,7,41))


def records(base):
    data = json.loads((ROOT / "case35-star-or-packings.json").read_text())
    seen = set()
    for center, gates, j, flags in data:
        arms = {i for i in range(26) if (i < 13) != (center < 13)
                and base[i] & base[center] & ((1 << 52)-1)}
        if len(arms) != 4 or not 0 <= center < 26 or len(gates) != 3:
            raise ValueError("expected a four-arm star and a three-OR tree")
        sources = [v for pair in gates for v in pair]
        if sorted(sources) != sorted([*arms,39,40]):
            raise ValueError("tree must read every arm and intermediate exactly once")
        ops = tuple((False,a,b) for a,b in gates)
        pool = list(base)
        for _,a,b in ops:
            if not 0 <= a <= b < len(pool):
                raise ValueError("invalid wiring")
            pool.append(pool[a] | pool[b])
        if gates[2] == [39,40] and gates[0][0] > gates[1][0]:
            raise ValueError("balanced trees use canonical child order")
        if (center,ops) in seen:
            raise ValueError("duplicate star tree")
        seen.add((center,ops))
        packing(pool,(j,flags))
        yield ops, len(flags)
    if len(seen) != 390:
        raise ValueError("expected 15 binary trees per center")


def first_unions(pool):
    data = json.loads((ROOT / "case35-point-seven-tight-packings.json").read_text())
    tests = [packing(pool, entry) for entry in data]
    if any(len(flags) != 19 for _, flags in data):
        raise ValueError("first-OR tests require 19 flags")
    # Enumerate all nonempty intersections. No leading OR means every
    # available signal is one of these even with arbitrary gate reuse.
    closure = set()
    for wire in pool:
        closure |= {old & wire for old in closure} | {wire}
    eligible = [v for v in closure if all(not (v >> (52+j) & 1) and v & m for j,m in tests)]
    pairs = [(a,b) for a,b in combinations_with_replacement(eligible,2)
             if all(((a | b) & m).bit_count() >= 2 for _,m in tests)]
    return eligible, {a | b for a,b in pairs}


def leaf_floor(base, suffix):
    data = json.loads((ROOT / "case35-star-tight-leaves.json").read_text())
    for _, gates, pivot, tests in data:
        if tuple((False,a,b) for a,b in gates) != suffix[:3]:
            continue
        pool = list(base)
        for a,b in gates:
            pool.append(pool[a] | pool[b])
        if not 0 <= pivot < 52 or not tests:
            raise ValueError("invalid required positive or empty witness list")
        m = len(tests[0][1])
        # A conjunction true at the pivot uses only pivot-true generators.
        # Enumerate every such nonempty conjunction, allowing arbitrary fanout.
        candidates = set()
        for x in pool:
            if x >> pivot & 1:
                candidates |= {x} | {x & y for y in candidates}
        for j,flags in tests:
            _,mask = packing(pool,(j,flags))
            if len(flags) != m:
                raise ValueError("unequal sizes in tight packing family")
            candidates = {x for x in candidates if not (x >> (52+j) & 1) and x & mask}
        if candidates:
            raise ValueError("a pivot-true AND-only signal survives every packing")
        return m
    return 0


def constrain(model, rows, h, *, leaves=False, probes=False):
    if model.size != 63 or model.prefix[:13] != PREFIX13 or len(rows) != 520:
        raise ValueError("star packings require the fixed prefix and complete target")
    base = columns(PREFIX13,rows)
    bound = density(base, ROOT / "case35-or-trace-density.json")["required_ors"]
    suffix = model.prefix[13:]
    floor = 0
    for ops, width in records(base):
        for n in (1,2,3):
            if suffix[:n] == ops[:n]:
                floor = max(floor, n+width-1)
    if leaves or probes:
        leaf = leaf_floor(base, suffix)
        if leaf:
            floor = max(floor,3+leaf)
    slots = 50-max(0,h-2)
    # The checked negative trace needs at least eight paid ANDs. In the
    # eight-paid case the separate density replay also requires 'bound' ORs.
    if 8+max(bound,floor)>slots and 9+floor>slots:
        model.clause()
        return
    model.require_at_least([-g.is_and for g in model.gates],floor-sum(not op for op,_,_ in suffix))
    extra_cert = None
    if probes and len(suffix) >= 4 and suffix[:4] != POINT7:
        for center, gates, cert in json.loads((ROOT / "case35-star-completion-probes.json").read_text()):
            ops = tuple((False, a, b) for a, b in gates) + ((True, center, 41),)
            if ops == suffix[:4]:
                extra_cert = cert
                break
    if probes and (suffix[:4] == POINT7 or extra_cert is not None):
        from order3_case35_point_seven_probes import replay
        pool = columns(model.prefix[:17],rows)
        *_,eight_or_floor = replay(pool, extra_cert)
        residual = 46-max(0,h-2)
        # The >128-negative family forces eight paid suffix ANDs. If there
        # are nine or more, the unconditional leaf floor still applies.
        if 8+eight_or_floor > residual and 9+floor-3 > residual:
            model.clause()
            return
    if h == 22 and suffix[:4] == POINT7:
        pool = columns(model.prefix,rows)
        _,allowed = first_unions(pool[:43])
        for i,(op,a,b) in enumerate(suffix[4:],43):
            if not op:
                if pool[i] not in allowed:
                    model.clause()
                return
        if model.gates:
            gate = model.gates[0]
            for a,b in combinations_with_replacement(range(len(pool)),2):
                if pool[a] | pool[b] not in allowed:
                    model.clause(gate.is_and,-gate.left[a],-gate.right[b])
                    model.clause(gate.is_and,-gate.left[b],-gate.right[a])


if __name__ == "__main__":
    from order3_prefix_search import test_rows
    rows = test_rows()
    base = columns(PREFIX13,rows)
    print("certificate widths", dict(Counter(width for _,width in records(base))))
    pool = columns(PREFIX13+POINT7,rows)
    eligible,unions = first_unions(pool)
    print("eligible operands",sorted(pool.index(v) for v in eligible),"union signatures",len(unions))
