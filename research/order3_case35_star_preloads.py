"""Check single paid-output preloads at the point-seven h=20 boundary."""
from collections import Counter, defaultdict
from functools import lru_cache
from itertools import combinations, combinations_with_replacement
import json

from order3_case35_colored_trace import constants, family, witness_graph
from order3_case35_point_seven_probes import replay
from order3_case35_star_packings import ROOT, PREFIX13, POINT7, columns

POS = (1 << 52) - 1


def dominates(u, v):
    """Replacing v by u preserves acceptance of positives and rejection of negatives."""
    return not (v & ~u & POS or u & ~v & ~POS)


def eight_paid_floor(base, value, rows, guard_off, packings, *, unique_paid_outputs=False):
    pool = base + [value]
    graph = witness_graph(pool)
    guard = pool[32]
    # A newly preloaded column may cover several flags while false on the
    # negative. Retain at most its first such flag in that row's packing.
    packs = []
    for j in rows:
        flags = packings[j]
        if not value >> (52+j) & 1:
            hits = [f for f in flags if value >> f & 1]
            flags = [f for f in flags if f not in hits[1:]]
        packs.append([j, flags])
    constant = constants(graph, pool)
    blocked = []
    ports = []
    for i, wire in enumerate(pool):
        ones = sum(wire >> (52+j) & 1 for j in rows)
        if max(ones, len(rows)-ones) > 128:
            continue
        if wire in constant:
            blocked.append([i, constant[wire][1]])
        else:
            ports.append(i)
    if len(guard_off) < 129:
        ports.extend([len(pool), len(pool)+1])
    edges = []
    for a, b in combinations(ports, 2):
        if a >= len(pool):
            continue
        groups = defaultdict(list)
        for j in range(468):
            if b >= len(pool) and guard >> (52+j) & 1:
                continue
            left = pool[a] >> (52+j) & 1
            right = pool[b] >> (52+j) & 1 if b < len(pool) else 0
            groups[left, right].append(j)
        for group in sorted(groups.values(), key=len, reverse=True):
            witness = family(graph, group, 65)
            if witness:
                edges.append([a, b, witness])
                break
    return replay(pool, dict(packs=packs, guard=guard_off, constants=blocked,
                             incompatible=edges), unique_paid_outputs=unique_paid_outputs)[-1]


def classify(base):
    data = json.loads((ROOT / "case35-point-seven-preloads.json").read_text())
    packings = dict(data["packings"])
    floor = {0: replay(base)[-1]}
    witnesses = {}
    for a,b,rows,off in data["families"]:
        if not (0 <= a <= b < len(base) and 32 not in (a,b)):
            raise ValueError("invalid preload operands")
        value = base[a] & base[b]
        if value in witnesses:
            raise ValueError("duplicate preload")
        witnesses[value] = rows,off
    counts = Counter()
    simple = 0
    for a,b in combinations_with_replacement([i for i in range(len(base)) if i != 32],2):
        value = base[a] & base[b]
        # A constant-false signal can be treated as an extra starting column:
        # it changes no witness/packing and can never be an eight-probe port.
        if any(dominates(u,value) for u in [0]+base):
            counts[floor[0]] += 1
            simple += 1
            continue
        if value not in floor:
            rows,off = witnesses.pop(value)
            floor[value] = eight_paid_floor(base, value, rows, off, packings)
        counts[floor[value]] += 1
    if witnesses or sum(counts.values()) != 903:
        raise ValueError("incomplete preload census")
    return simple, counts, floor


@lru_cache(maxsize=1)
def verify_all_pairs(base):
    _, counts, _ = classify(list(base))
    if min(counts) <= 19:
        raise ValueError("a paid preload still admits the h=20 OR budget")


def constrain(model, rows, h):
    if h < 20 or model.prefix[:17] != PREFIX13 + POINT7 or model.size != 63:
        return
    verify_all_pairs(tuple(columns(PREFIX13 + POINT7, rows)))
    # Each marked wire is an initial input, possibly ANDed with the guard.
    # Two such operands can be combined from a single prepaid pair and at
    # most one free guard gate. Their use by a paid AND would save one paid
    # gate while preserving the complete row behaviour and the OR budget.
    marked = [True] * 43
    for op,a,b in model.prefix[17:]:
        if op and 32 not in (a,b) and marked[a] and marked[b]:
            model.clause()
            return
        marked.append(op and ((a == 32 and marked[b]) or (b == 32 and marked[a])))
    for gate in model.gates:
        operands = []
        for selectors in (gate.left, gate.right):
            mark = model.fresh()
            for selector, source in zip(selectors, marked, strict=True):
                if source is True:
                    model.clause(-selector, mark)
                elif source is not False:
                    model.clause(-selector, -source, mark)
            operands.append(mark)
        left, right = operands
        model.clause(-gate.is_and, gate.left[32], gate.right[32], -left, -right)
        out = model.fresh()
        model.clause(-gate.is_and, -gate.left[32], -right, out)
        model.clause(-gate.is_and, -gate.right[32], -left, out)
        marked.append(out)


if __name__ == "__main__":
    from order3_prefix_search import test_rows
    base = columns(PREFIX13+POINT7, test_rows())
    simple, counts, _ = classify(base)
    print("direct dominance",simple,"eight-paid suffix OR floors",dict(sorted(counts.items())))
