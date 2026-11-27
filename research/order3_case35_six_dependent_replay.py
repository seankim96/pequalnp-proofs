"""Evaluate the six-paid-gate witness on original 26-bit rows and audit its Lean table."""
import json
import re
from pathlib import Path

from order3_case35_twenty_one_rows import NEGATIVES, POINT7, PREFIX13, SEPARATED, test_rows

ROOT = Path(__file__).resolve().parent


def replay():
    data = json.loads((ROOT / "results/case35-six-dependent-filtered.json").read_text())
    rows = test_rows()
    proof = (ROOT.parent / "lean/PEqualNP/Research/PlaneSixDependentProducts.lean").read_text()
    raw = [sum(((row >> i) & 1) << j for j, (row, _) in enumerate(rows)) for i in range(26)]
    assert json.loads(re.search(r"let raw : List Nat := (\[.*\])", proof)[1]) == raw
    masks = [0] * 4
    for j, (row, _) in enumerate(rows):
        wires = [bool(row >> i & 1) for i in range(26)]
        for is_and, a, b in PREFIX13 + POINT7:
            wires.append((wires[a] and wires[b]) if is_and else (wires[a] or wires[b]))
        guard = wires[32]
        pool = wires + [v and guard for v in wires]
        for left, right in data["first_six_products"]:
            assert all(0 <= i < len(pool) for i in left + right)
            value = any(pool[i] for i in left) and any(pool[i] for i in right)
            pool.extend([value, value and guard])
        masks[0] |= int(value) << j
        for k, side in enumerate(data["optional_filters"], 1):
            value = value and any(pool[i] for i in side)
            masks[k] |= int(value) << j
    assert int(re.search(r"pool.getD 96 0 = (\d+)", proof)[1]) == masks[0]
    for k, mask in enumerate(masks, 6):
        assert all(mask >> j & 1 for j in SEPARATED)
        assert all(not mask >> (52 + j) & 1 for j in NEGATIVES)
        print(k, "paid ANDs:", (mask % 2**52).bit_count(), "positive hits,",
              (mask >> 52).bit_count(), "negative hits")


if __name__ == "__main__":
    replay()
