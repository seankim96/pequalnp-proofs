"""Classify continuations of the ten fixed gates at the 28-read boundary."""
from collections import Counter
from itertools import combinations_with_replacement


PREFIX = ((False, 0, 1), (False, 3, 9), (True, 15, 27), (True, 17, 26),
          (True, 13, 26), (True, 13, 27), (False, 2, 6), (True, 1, 24),
          (True, 15, 32), (True, 25, 32))


def columns(prefix, rows=None):
    if rows is None:
        from order3_prefix_search import test_rows
        rows = test_rows()
    wires = [sum(1 << i for i, (x, _) in enumerate(rows) if x & (1 << j))
             for j in range(26)]
    for op, a, b in prefix:
        wires.append((wires[a] & wires[b]) if op else (wires[a] | wires[b]))
    return wires


def choices(wires):
    pairs = list(combinations_with_replacement(range(len(wires)), 2))
    ands = {wires[a] & wires[b] for a, b in pairs}
    ors = {wires[a] | wires[b] for a, b in pairs}
    # An out-of-range read returns zero in the Lean model. Include its
    # possible outputs when testing alternate implementations.
    ands.add(0)
    free = ors | {w & wires[32] for w in wires} | {0}
    for a, b in pairs:
        for op in (False, True):
            value = (wires[a] & wires[b]) if op else (wires[a] | wires[b])
            alias = value in ands and value in free
            explicit = op and 32 in (a, b)
            assert not explicit or alias
            yield (op, a, b), value, alias and not explicit


def fixed_state(model, rows):
    if model.prefix[:8] != PREFIX[:8] or model.size != 63 or len(rows) != 520:
        raise ValueError("semantic pruning needs the certified prefix, 520 rows and size 63")
    wires = columns(model.prefix[:8], rows)
    extra_count = guard_count = 0
    for gate in model.prefix[8:]:
        value, extra = next((v, b) for g, v, b in choices(wires) if g == gate)
        extra_count += extra
        guard_count += gate[0] and 32 in gate[1:]
        wires.append(value)
    extra_choices = [g for g, _, extra in choices(wires) if extra]
    return len(wires), extra_choices, extra_count, guard_count


def exclude_unmarked(g, pool_size, extra_choices, model, *mark):
    # With a mark literal the clause charges this gate. Without one it
    # excludes the gate. Both orientations of every physical gate are covered.
    for op, a, b in extra_choices:
        literal = -g.is_and if op else g.is_and
        model.clause(literal, -g.left[a], -g.right[b], *mark)
        if a != b:
            model.clause(literal, -g.left[b], -g.right[a], *mark)
    for k in range(pool_size, len(g.left)):
        # A repeated operand copies a newly created wire with either operator.
        model.clause(-g.left[k], -g.right[k], *mark)


def prune_boundary(model, rows):
    """At h >= 28 every flexible gate after gate eight must be an explicit guard read."""
    pool_size, extra_choices, extra_count, _ = fixed_state(model, rows)
    if extra_count:
        model.clause()
        return
    for g in model.gates:
        exclude_unmarked(g, pool_size, extra_choices, model)


def cap_flexible(model, rows):
    """Require at most 28 provably flexible gates, including all explicit guard ANDs."""
    pool_size, extra_choices, extra_count, guard_count = fixed_state(model, rows)
    fixed_count = extra_count + guard_count
    indicators = []
    for g in model.gates:
        mark = model.fresh()
        indicators.append(mark)
        model.clause(-g.is_and, -g.left[32], mark)
        model.clause(-g.is_and, -g.right[32], mark)
        exclude_unmarked(g, pool_size, extra_choices, model, mark)
    remaining = 28 - fixed_count
    if remaining < 0:
        model.clause()
    elif remaining < len(indicators):
        model.require_at_least([-mark for mark in indicators], len(indicators) - remaining)


def main():
    wires = columns(PREFIX)
    first = list(choices(wires))
    # Compare the actual enumerated physical gates to the formally certified list.
    from pathlib import Path
    import re
    source = Path(__file__).resolve().parents[1] / 'lean/PEqualNP/Research/PlaneCase35BoundaryCodes.lean'
    cert = re.search(r'def codes : Array Nat := #\[([^\]]+)\]', source.read_text())
    computed = [1369*op + 37*a + b for (op,a,b), _, bad in first if bad]
    assert cert and list(map(int, cert[1].split(','))) == computed
    assert len(set(computed)) == 237
    counts = Counter()
    # Continuations producing the same 520-bit column have identical choices
    # at gate twelve. Keep multiplicities of distinct physical gate codes.
    cache = {}
    for gate, value, wasted in first:
        counts['first_total'] += 1
        counts['first_excluded'] += wasted
        if value not in cache:
            second = list(choices(wires + [value]))
            cache[value] = len(second), sum(w for _, _, w in second)
        total, excluded = cache[value]
        counts['two_total'] += total
        counts['two_excluded'] += total if wasted else excluded
    # After gate 10, equal columns preserve every future wire. Keep the total
    # number of explicit guard reads as well, since this is the h=28 boundary.
    by_value = {}
    for (op, a, b), value, excluded in first:
        if not excluded:
            by_value.setdefault(value, set()).add(int(op and 32 in (a, b)))
    one_keys = sum(len(reads) for reads in by_value.values())
    two_keys = 0
    for value, reads in by_value.items():
        keys = {(next_value, h + int(op and 32 in (a, b)))
                for (op, a, b), next_value, excluded in choices(wires + [value])
                if not excluded for h in reads}
        two_keys += len(keys)
    assert one_keys == 1076
    print('Distinct surviving wire states and guard counts:', one_keys, two_keys)
    print(dict(counts))
    print('Excluded gate 11 by type:', {op: sum(bad for g, _, bad in first if g[0] == op)
                                         for op in (False, True)})
    # The gate used by the fixed-eleventh SAT attempt is a surviving choice.
    continuation = wires + [wires[0] & wires[1]]
    fixed_and = [g for g, _, bad in choices(continuation) if bad]
    assert len(fixed_and) == 262 and sum(36 in g[1:] for g in fixed_and) == 24
    print('Following AND(0,1): 262 of 1406 excluded, 24 read wire 36')
    print('First surviving non-guard ANDs:', [g for g, _, bad in first
                                              if g[0] and 32 not in g[1:] and not bad][:5])


if __name__ == '__main__':
    main()
