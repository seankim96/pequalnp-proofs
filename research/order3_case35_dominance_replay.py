"""Count the gate exclusions and validate all dominance witnesses row by row."""
from order3_case35_semantic_reuse import PREFIX, choices, columns, guard_dominance
from order3_prefix_search import test_rows


def audit(prefix):
    rows = test_rows()
    wires = columns(prefix, rows)
    witnesses = guard_dominance(wires, rows)
    classified = list(choices(wires))
    previous = {g for g, _, interchangeable in classified if interchangeable}
    for row, (bits, positive) in enumerate(rows):
        state = [bool(bits & (1 << k)) for k in range(26)]
        for op, a, b in prefix:
            state.append(state[a] and state[b] if op else state[a] or state[b])
        assert all(state[k] == bool(word & (1 << row)) for k, word in enumerate(wires))
        for (op, a, b), partner in witnesses.items():
            original = state[a] and state[b] if op else state[a] or state[b]
            replacement = state[32] and state[partner]
            assert (not original or replacement) if positive else (not replacement or original)
    combined = previous.union(witnesses)
    print(f'{len(prefix)} fixed gates: {len(classified)} choices, '
          f'{len(previous)} interchangeable, {len(witnesses)} dominated, '
          f'{len(combined) - len(previous)} new, {len(classified) - len(combined)} remaining')


if __name__ == '__main__':
    for prefix in (PREFIX[:8], PREFIX[:9], PREFIX, PREFIX + ((True, 0, 17),)):
        audit(prefix)
