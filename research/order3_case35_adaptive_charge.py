"""Certified adaptive charge, using only legal earlier wires as replacement witnesses."""
from order3_case35_semantic_reuse import PREFIX, choices, columns, exclude_codes, guard_dominance
from order3_case35_wire_credit import replacements


def is_guard(g):
    return g[0] and 32 in g[1:]


def witnesses(wires, rows):
    positive = sum(1 << i for i, (_, yes) in enumerate(rows) if yes)
    negative = ((1 << len(rows)) - 1) ^ positive
    alternatives = [(v, (False, i, i)) for i, v in enumerate(wires)]
    alternatives.extend((v & wires[32], (True, i, 32)) for i, v in enumerate(wires))
    result = {}
    for gate, value, _ in choices(wires):
        if is_guard(gate):
            continue
        for alt, code in alternatives:
            if not (value & positive & ~alt or alt & negative & ~value):
                result[gate] = code
                break
    return result


def constrain(model, rows, min_reads):
    if model.size != 63 or model.prefix[:8] != PREFIX[:8] or len(rows) != 520:
        raise ValueError("adaptive charge requires the certified 520-row eight-gate prefix")
    guard = extra = 0
    for i, gate in enumerate(model.prefix[8:], 8):
        if is_guard(gate):
            guard += 1
        elif gate in witnesses(columns(model.prefix[:i], rows), rows):
            extra += 1
    remaining = 28 - max(min_reads, guard) - extra
    if remaining < 0:
        model.clause()
        return
    codes = witnesses(columns(model.prefix, rows), rows)
    marks, costs = [], []
    for g in model.gates:
        if remaining == 0:
            exclude_codes(g, codes, model)
        else:
            extra_mark = model.fresh()
            marks.append(extra_mark)
            exclude_codes(g, codes, model, extra_mark)
        cost = model.fresh()
        costs.append(cost)
        if remaining > 0:
            model.clause(-extra_mark, cost)
        model.clause(-g.is_and, -g.left[32], cost)
        model.clause(-g.is_and, -g.right[32], cost)
    for group, cap in [(marks, remaining), (costs, 28 - guard - extra)]:
        if len(group) > cap:
            model.require_at_least([-x for x in group], len(group) - cap)


def replay():
    from order3_prefix_search import test_rows
    rows = test_rows()
    prefix = PREFIX + ((True, 0, 17), (True, 0, 23))
    wires = columns(prefix, rows)
    table = witnesses(wires, rows)
    options = list(choices(wires))
    old = {g for g, _, eq in options if eq or g in replacements()}
    old.update(guard_dominance(wires, rows))
    print("Gate 13 total, old exclusions, new witnesses, surviving at h=28:",
          len(options), len(old), [(g, w) for g, w in table.items() if g not in old],
          len(options) - len(old | table.keys()))
    pairs = additional = new_witness = 0
    negative = sum(1 << i for i, (_, yes) in enumerate(rows) if not yes)
    # Flip negative-row bits: set inclusion now compares both labels in one direction.
    fixed_scores = {v ^ negative for v in wires} | {(wires[32] & v) ^ negative for v in wires}
    needs_last = {}
    cache = {}
    fixed_table = replacements()
    for g, value, old_flexible in options:
        if g not in table:
            continue
        if value not in cache:
            extended = wires + [value]
            second = witnesses(extended, rows)
            flags = []
            needs_last[value] = 0
            for k, v, eq in choices(extended):
                if k in second:
                    flags.append((eq, k in fixed_table))
                    if not any(((v ^ negative) | z) == z for z in fixed_scores):
                        needs_last[value] += 1
            cache[value] = {(f, t): sum(not (f and eq or t and member) for eq, member in flags)
                            for f in (False, True) for t in (False, True)}
        new_witness += needs_last[value]
        pairs += cache[value][False, False]
        additional += cache[value][old_flexible, g in fixed_table]
    print("At h>=27, two individually chargeable non-guard gates:", pairs,
          "of", len(options) * (len(wires)+1) * (len(wires)+2), "ordered physical gate pairs")
    print("Of these, pairs not already excluded by either previous pair-count rule:", additional)
    print("Pairs whose second charge requires the newly available wire in its witness:", new_witness)
    # Neither of these fixed gates is a guard. The second witness may use gate 13.
    for g in [(True, 23, 26), (True, 0, 38)]:
        k = witnesses(wires, rows)[g]
        op, a, b = g
        val = wires[a] & wires[b] if op else wires[a] | wires[b]
        for i, (_, yes) in enumerate(rows):
            v = (val >> i) & 1
            left, right = (wires[k[z]] >> i & 1 for z in (1, 2))
            replacement = left & right if k[0] else left | right
            assert (v <= replacement) if yes else (replacement <= v)
        print("gate", g, "witness", k)
        wires.append(val)


if __name__ == "__main__":
    replay()
