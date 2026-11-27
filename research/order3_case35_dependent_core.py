"""Exact synthesis on the 21-row core, charging only non-guard ANDs.

Usage: python research/order3_case35_dependent_core.py CADICAL K SECONDS
A model is decoded on all 520 rows. A timeout is UNKNOWN.
"""
import argparse
import json
import subprocess
import tempfile
from pathlib import Path

from order3_case35_twenty_one_rows import NEGATIVES, POINT7, PREFIX13, SEPARATED, columns, join, test_rows


class Encoding:
    def __init__(self):
        self.count = 0
        self.clauses = []

    def variable(self):
        self.count += 1
        return self.count

    def either(self, inputs):
        result = self.variable()
        self.clauses.extend([[-wire, result] for wire in inputs])
        self.clauses.append([-result, *inputs])
        return result

    def both(self, a, b):
        result = self.variable()
        self.clauses.extend([[-result, a], [-result, b], [result, -a, -b]])
        return result


def synthesize(solver, budget, seconds, canonical=False):
    wires = tuple(columns(PREFIX13 + POINT7, test_rows()))
    sources = list(wires) + [v & wires[32] for v in wires]
    rows = list(SEPARATED) + [52 + j for j in NEGATIVES]

    def restrict(column):
        return sum(((column >> j) & 1) << r for r, j in enumerate(rows))

    # Select one representative per distinct nonzero initial truth column.
    initial = {}
    for idx, val in enumerate(sources):
        if sig := restrict(val):
            initial.setdefault(sig, idx)
    encoding = Encoding()
    previous = []
    operands = []

    def side():
        selectors = [encoding.variable() for _ in range(len(initial) + 2 * len(previous))]
        if canonical:
            # An unmasked source subsumes its masked copy in an OR.
            for q in range(len(previous)):
                offset = len(initial) + 2 * q
                encoding.clauses.append([-selectors[offset], -selectors[offset + 1]])
        values = []
        for r, j in enumerate(rows):
            terms = [s for s, sig in zip(selectors, initial) if sig >> r & 1]
            for q, bits in enumerate(previous):
                offset = len(initial) + 2 * q
                terms.append(encoding.both(selectors[offset], bits[r]))
                if wires[32] >> j & 1:
                    terms.append(encoding.both(selectors[offset + 1], bits[r]))
            values.append(encoding.either(terms))
        return selectors, values

    for _ in range(budget):
        left, left_bits = side()
        right, right_bits = side()
        if canonical:
            # Lexicographic order breaks only the commutativity of this AND.
            equal_prefix = None
            for a, b in zip(reversed(left), reversed(right)):
                guard = [-equal_prefix] if equal_prefix is not None else []
                encoding.clauses.append([*guard, -a, b])
                equal_next = encoding.variable()
                encoding.clauses.extend([[*guard, -a, -b, equal_next], [*guard, a, b, equal_next]])
                equal_prefix = equal_next
        operands.append((left, right))
        previous.append([encoding.both(a, b) for a, b in zip(left_bits, right_bits)])

    output, bits = side()
    for r, v in enumerate(bits):
        encoding.clauses.append([v if r < len(SEPARATED) else -v])
    result = dict(canonical=canonical, gates=budget, seconds=seconds, variables=encoding.count, clauses=len(encoding.clauses))
    with tempfile.TemporaryDirectory() as temp:
        path = Path(temp) / "problem.cnf"
        with path.open("w") as f:
            print("p cnf", encoding.count, len(encoding.clauses), file=f)
            for clause in encoding.clauses:
                print(*clause, 0, file=f)
        try:
            proc = subprocess.run([solver, "-q", str(path)], capture_output=True, text=True, timeout=seconds)
        except subprocess.TimeoutExpired:
            return dict(result, verdict="UNKNOWN")
    if proc.returncode == 20:
        return dict(result, verdict="UNSAT")
    if proc.returncode != 10:
        raise RuntimeError(f"CaDiCaL returned {proc.returncode}: {proc.stderr}")
    model = {int(x) for line in proc.stdout.splitlines() if line.startswith("v ")
             for x in line.split()[1:] if int(x) > 0}
    indices = list(initial.values())

    def decode(selectors):
        selected = [i for i, s in zip(indices, selectors) if s in model]
        return selected, join(sources[i] for i in selected)

    witness = []
    for left, right in operands:
        lidx, lv = decode(left)
        ridx, rv = decode(right)
        product = lv & rv
        witness.append([lidx, ridx])
        indices.extend([len(sources), len(sources) + 1])
        sources.extend([product, product & wires[32]])
    selected, value = decode(output)
    assert restrict(value) == (1 << len(SEPARATED)) - 1
    return dict(result, verdict="SAT", ops=witness, output=selected,
                positive_hits=(value & ((1 << 52) - 1)).bit_count(), negative_hits=(value >> 52).bit_count())


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("solver")
    parser.add_argument("gates", type=int)
    parser.add_argument("seconds", type=float)
    parser.add_argument("--canonical", action="store_true")
    args = parser.parse_args()
    print(json.dumps(synthesize(args.solver, args.gates, args.seconds, args.canonical)))
