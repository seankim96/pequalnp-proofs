"""Replay the wire-replacement certificate and encode its size-63 consequence."""
import re
from pathlib import Path

from order3_case35_semantic_reuse import PREFIX, choices, columns, exclude_codes, guard_dominance


def replacements():
    source = Path(__file__).resolve().parents[1] / "lean/PEqualNP/Research/PlaneCase35WireCredit.lean"
    line = next(s for s in source.read_text().splitlines() if s.startswith("def pairs :"))
    entries = {(op == "true", int(a), int(b)): int(w)
               for op, a, b, w in re.findall(r"\(\((true|false),(\d+),(\d+)\),(\d+)\)", line)}
    if len(entries) != 22 or any(entries.get((op, b, a)) != w for (op, a, b), w in entries.items()):
        raise ValueError("unexpected Lean replacement table")
    return {g: w for g, w in entries.items() if g[1] <= g[2]}


def cap_wire_credit(model, minimum_reads):
    if model.size != 63 or model.prefix[:8] != PREFIX[:8]:
        raise ValueError("wire credit needs the certified eight-gate prefix and size 63")
    table = replacements()
    fixed = model.prefix[8:]
    guard = sum(op and 32 in (a, b) for op, a, b in fixed)
    marked = sum(g in table for g in fixed)
    if max(guard, minimum_reads) + marked > 28:
        model.clause()
        return
    if minimum_reads == 28:
        for gate in model.gates:
            exclude_codes(gate, table, model)
        # The general budget also caps guard reads when this flag is used alone.
    indicators = []
    for gate in model.gates:
        mark = model.fresh()
        indicators.append(mark)
        model.clause(-gate.is_and, -gate.left[32], mark)
        model.clause(-gate.is_and, -gate.right[32], mark)
        if minimum_reads < 28:
            exclude_codes(gate, table, model, mark)
    required = len(indicators) - (28 - guard - marked)
    if required > 0:
        model.require_at_least([-m for m in indicators], required)



def representatives(candidates, rows):
    """Keep one maximal output per operator/guard class and verify a witness for each gate."""
    positives = sum(1 << i for i, (_, yes) in enumerate(rows) if yes)
    negatives = ((1 << len(rows)) - 1) ^ positives
    def key(g):
        return g[0], g[0] and 32 in g[1:]
    # XOR the negative-row mask so that set inclusion means improvement on both labels.
    ranked = sorted(((g, v ^ negatives) for g, v in candidates),
                    key=lambda x: (-x[1].bit_count(), x[0]))
    maximal = {}
    witness = {}
    for gate, score in ranked:
        bucket = maximal.setdefault(key(gate), [])
        for kept, top in bucket:
            if score & ~top == 0:
                witness[gate] = kept
                break
        else:
            bucket.append((gate, score))
            witness[gate] = gate
    values = dict(candidates)
    for g, k in witness.items():
        assert key(g) == key(k)
        assert not (values[g] & positives & ~values[k])
        assert not (values[k] & negatives & ~values[g])
    return witness


def main():
    from order3_prefix_search import test_rows
    rows = test_rows()
    table = replacements()
    wires = columns(PREFIX[:8], rows)
    for (op, a, b), replacement in table.items():
        value = (wires[a] & wires[b]) if op else (wires[a] | wires[b])
        for i, (_, label) in enumerate(rows):
            actual = (value >> i) & 1
            substitute = (wires[replacement] >> i) & 1
            assert (actual <= substitute) if label else (substitute <= actual)
    print(f"{len(table)} replacement certificates replayed on {len(rows)} rows")
    for prefix in (PREFIX, PREFIX + ((True, 0, 17),)):
        wires = columns(prefix, rows)
        dominated = guard_dominance(wires, rows)
        candidates = list(choices(wires))
        old = {g for g, _, bad in candidates if bad or g in dominated}
        extra = set(table) - old
        remaining = [g for g, _, _ in candidates if g not in old and g not in table]
        print("after", len(prefix), "gates:", len(candidates), "choices,", len(old),
              "previous exclusions,", len(extra), "new exclusions,", len(remaining), "remain")
        allowed = set(remaining)
        witness = representatives([(g, v) for g, v, _ in candidates if g in allowed], rows)
        print("distinct maximal representatives with the same operator and guard charge:",
              len(set(witness.values())))
        if len(prefix) == 11:
            print("AND(0,23) maps to", witness[(True, 0, 23)])
        print("first surviving non-guard ANDs:",
              [g for g in remaining if g[0] and 32 not in g[1:]][:5])


if __name__ == "__main__":
    main()
