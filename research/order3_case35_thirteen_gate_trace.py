"""Replay and apply the case-35 bound for a block supported on 24 positive flags."""
import json
import re
from itertools import combinations
from collections import Counter
from pathlib import Path

from order3_case35_semantic_reuse import PREFIX, choices, columns, exclude_codes
from order3_case35_adaptive_charge import is_guard


def certificate():
    src = Path(__file__).resolve().parents[1] / "lean/PEqualNP/Research/PlaneCase35ThirteenGateTrace.lean"
    text = src.read_text()
    omitted = int(re.search(r"have zero : ∀ i : Fin 52, \((0x[0-9a-f]+) : Nat\)", text)[1], 16)
    deleted = int(re.search(r"private def removed : Nat := (0x[0-9a-f]+)", text)[1], 16)
    return omitted, [i for i in range(468) if not deleted >> i & 1]


def constrain(model, rows, min_reads):
    if model.size != 63 or model.prefix[:7] != PREFIX[:7] or len(rows) != 520:
        raise ValueError("expected size 63, certified seven-gate prefix and all labeled tests")
    omitted, _ = certificate()
    outside = ((1 << 52) - 1) ^ omitted
    wires = columns(model.prefix, rows)
    cut = 7
    while cut < len(model.prefix) and wires[26 + cut] & outside == 0:
        cut += 1
    before = model.prefix[7:cut]
    after = model.prefix[cut:]
    spent = sum(g[0] and not is_guard(g) for g in before)
    if spent + min_reads > 30:
        model.clause()
        return
    if spent + min_reads == 30 and cut == len(model.prefix) and model.gates:
        bad = [g for g, value, _ in choices(wires) if g[0] and not is_guard(g) and value & outside == 0]
        exclude_codes(model.gates[0], bad, model)
    # The guard ANDs are free in the negative trace. Require eight other ANDs
    # after the cut, and at least eighteen ORs anywhere after gate seven.
    marks = []
    for gate in model.gates:
        mark = model.fresh()
        model.clause(-mark, gate.is_and)
        model.clause(-mark, -gate.left[32])
        model.clause(-mark, -gate.right[32])
        marks.append(mark)
    limits = [(marks, 8 - sum(g[0] and not is_guard(g) for g in after)),
              ([-g.is_and for g in model.gates], 18 - sum(not g[0] for g in model.prefix[7:]))]
    for flags, minimum in limits:
        if minimum > len(flags):
            model.clause()
        elif minimum > 0:
            model.require_at_least(flags, minimum)


def verify_fourteenth(rows):
    """Check the supplied negative families directly against the physical wires."""
    prefix = PREFIX + ((True, 0, 17), (True, 0, 23), (True, 0, 25))
    cols = columns(prefix, rows)
    words = [sum(((c >> r) & 1) << k for k, c in enumerate(cols)) for r in range(520)]
    path = Path(__file__).with_name("results") / "case35-gate14-trace-families.json"
    expected = {39*a+b for a in range(39) for b in range(a, 39) if 32 not in (a, b)}
    checked = set()
    for group in json.loads(path.read_text()):
        family = group["negatives"]
        if len(set(family)) != len(family) or min(family) < 0 or max(family) >= 468 or len(family) < 129:
            raise ValueError("invalid negative family")
        # For each pair, independently find all positive rows satisfying the guard
        # condition and the coverage condition on the first 39 physical wires.
        pairs = []
        for i, j in combinations(family, 2):
            x, y = words[52+i], words[52+j]
            allowed = sum(1 << r for r, v in enumerate(words[:52])
                          if v & ~(x | y) == 0 and (not (v >> 32 & 1) or x & y & (1 << 32)))
            if not allowed:
                raise ValueError("base wires have no pair witness")
            pairs.append((x, y, allowed))
        for code in group["codes"]:
            if code not in expected or code in checked:
                raise ValueError("invalid or duplicate physical gate code")
            a, b = divmod(code, 39)
            operands = (1 << a) | (1 << b)
            active = cols[a] & cols[b] & ((1 << 52) - 1)
            if any(not flags & ~active and x & operands != operands and y & operands != operands
                   for x, y, flags in pairs):
                raise ValueError("fourteenth gate destroys every positive witness of a pair")
            checked.add(code)
    if checked != expected:
        raise ValueError("missing fourteenth-gate case")
    return len(checked)


def constrain_fourteenth(model, rows, min_reads):
    prefix = PREFIX + ((True, 0, 17), (True, 0, 23), (True, 0, 25))
    if model.size != 63 or model.prefix[:13] != prefix or len(rows) != 520:
        raise ValueError("fourteenth-gate certificate requires the specified thirteen-gate prefix")
    verify_fourteenth(rows)
    # For a non-guard AND at slot 14 the trace requires eight further
    # non-guard ANDs and the OR bound requires eighteen ORs. Only 49 slots
    # remain, so at most 23 more guard reads, plus two already fixed.
    if min_reads >= 26:
        if len(model.prefix) == 13:
            gate = model.gates[0]
            model.clause(-gate.is_and, gate.left[32], gate.right[32])
        elif model.prefix[13][0] and not is_guard(model.prefix[13]):
            model.clause()


def constrain_preloaded(model, rows, min_reads):
    prefix = PREFIX + ((True, 0, 17), (True, 0, 23), (True, 0, 25))
    if model.size != 63 or model.prefix[:13] != prefix or len(rows) != 520:
        raise ValueError("preloaded AND reduction requires the certified thirteen gates")
    verify_fourteenth(rows)
    fixed = Counter((a, b) for op, a, b in model.prefix[13:]
                    if op and 32 not in (a, b) and max(a, b) < 39)
    if min_reads + max(fixed.values(), default=0) > 26:
        model.clause()
        return
    for gate in model.gates:
        if min_reads == 26:
            # A non-guard AND must select a post-prefix wire on at least one side.
            model.clause(-gate.is_and, gate.left[32], gate.right[32], *gate.left[39:], *gate.right[39:])
        elif min_reads < 26:
            # A previously fixed pair may have exhausted its own multiplicity allowance.
            exclude_codes(gate, [(True, a, b) for (a, b), n in fixed.items() if n + min_reads == 26], model)


def main():
    from order3_prefix_search import test_rows
    rows = test_rows()
    omit, family = certificate()
    p13 = PREFIX + ((True, 0, 17), (True, 0, 23), (True, 0, 25))
    words = []
    for row, _ in rows:
        word = row
        for i, (op, a, b) in enumerate(p13):
            x, y = word >> a & 1, word >> b & 1
            word |= ((x & y) if op else (x | y)) << (26+i)
        words.append(word)
    high = [(p, x) for p, x in enumerate(words[:52]) if not omit >> p & 1]
    for i, j in combinations(family, 2):
        a, b = words[52+i], words[52+j]
        assert any(not (x & ~(a | b)) and (not (x >> 32 & 1) or a & b & (1 << 32))
                   for _, x in high)
    outside = ((1 << 52) - 1) ^ omit
    w = columns(p13, rows)
    assert len(family) == 131 and all(not (col & outside) for col in w[33:])
    print("Checked",len(family),"negative rows,",len(family)*(len(family)-1)//2,
          "pairs,",len(high),"usable positive flags; gates 8–13 satisfy support condition")
    for n in (10, 11, 12, 13):
        opts = list(choices(w[:26+n]))
        bad = [g for g, v, _ in opts if g[0] and not is_guard(g) and not v & outside]
        print("After",n,"gates:",len(bad),"of",len(opts),"next gates spend another non-guard AND")
    surviving = [g for g, v, _ in opts if g[0] and not is_guard(g) and v & outside]
    print("First ANDs outside the flag set:",surviving[:10])
    print("Fourteenth-gate certificates verified:", verify_fourteenth(rows))


if __name__ == "__main__":
    main()
