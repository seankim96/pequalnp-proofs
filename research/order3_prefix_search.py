"""Search a certified two-gate case of L-meta-2625 on its 520 distinct tests."""
import argparse
from dataclasses import dataclass
from pathlib import Path
import re
import subprocess
import tempfile
from time import monotonic

Gate = tuple[bool, int, int]
ROOT = Path(__file__).resolve().parents[1]
LEAN_CASES = ROOT / "lean/PEqualNP/Research/OrderThreePlaneSwaps.lean"
DIFFERENCES = (0, 1, 3, 9)
NEGATIVE_REPS = ((7, 904), (13, 2848), (19, 708), (21, 2720),
                 (25, 2656), (37, 2440), (41, 2370), (133, 808))


def decode(code: int) -> Gate:
    return code >= 729, (code % 729) // 27, code % 27


def representatives() -> list[tuple[Gate, Gate]]:
    text = LEAN_CASES.read_text().split("def retained : List Pair :=", 1)[1]
    section = text.split("private def witnesses", 1)[0]
    result = [(decode(int(a)), decode(int(b))) for a, b in re.findall(r"\((\d+), (\d+)\)", section)]
    if len(result) != 68 or len(set(result)) != 68:
        raise ValueError("unexpected certificate format or case count")
    return result


def test_rows() -> list[tuple[int, bool]]:
    positive = {(1 << p) | (1 << (13 + w)) for p in range(13) for w in range(13)
                if (p - w) % 13 in DIFFERENCES}
    negative = set()
    for points, lines in NEGATIVE_REPS:
        for multiplier in (1, 3, 9):
            for offset in range(13):
                for dual in (False, True):
                    first, second = (lines, points) if dual else (points, lines)
                    row = 0
                    for i in range(13):
                        j = (multiplier * i + offset) * (-1 if dual else 1) % 13
                        row |= ((first >> j) & 1) << i
                        row |= ((second >> j) & 1) << (13 + i)
                    negative.add(row)
    if len(positive) != 52 or len(negative) != 468 or positive & negative:
        raise ValueError("invalid test family")
    return [(r, True) for r in sorted(positive)] + [(r, False) for r in sorted(negative)]


def evaluate(gates: list[Gate], row: int) -> bool:
    wires = [bool((row >> i) & 1) for i in range(26)]
    for is_and, left, right in gates:
        if not (0 <= left < len(wires) and 0 <= right < len(wires)):
            raise ValueError("wire is out of range")
        wires.append((wires[left] and wires[right]) if is_and else (wires[left] or wires[right]))
    return wires[-1]


@dataclass(frozen=True)
class Choices:
    is_and: int
    left: list[int]
    right: list[int]


def negate(literal: int | bool) -> int | bool:
    return not literal if isinstance(literal, bool) else -literal


class Encoding:
    def __init__(self, prefix: tuple[Gate, ...], size: int, n_inputs: int = 26):
        self.n_inputs = n_inputs
        self.prefix = prefix
        self.size = size
        self.variables = 0
        self.clauses = []
        self.gates = []
        for gate in range(len(prefix), size):
            choices = Choices(self.fresh(), [self.fresh() for _ in range(n_inputs + gate)],
                              [self.fresh() for _ in range(n_inputs + gate)])
            self.gates.append(choices)
            self.clause(*choices.left)
            self.clause(*choices.right)

    def fresh(self) -> int:
        self.variables += 1
        return self.variables

    def clause(self, *values: int | bool):
        if not any(v is True for v in values):
            self.clauses.append(tuple(v for v in values if v is not False))

    def operand(self, selectors, wires) -> int:
        result = self.fresh()
        for select, incoming in zip(selectors, wires, strict=True):
            self.clause(-select, negate(incoming), result)
            self.clause(-select, incoming, -result)
        return result

    def add_row(self, row: int, answer: bool):
        wires = [bool(row & (1 << i)) for i in range(self.n_inputs)]
        for is_and, a, b in self.prefix:
            wires.append((wires[a] and wires[b]) if is_and else (wires[a] or wires[b]))
        for gate in self.gates:
            left = self.operand(gate.left, wires)
            right = self.operand(gate.right, wires)
            bit = self.fresh()
            self.clause(-gate.is_and, -bit, left)
            self.clause(-gate.is_and, -bit, right)
            self.clause(-gate.is_and, bit, -left, -right)
            self.clause(gate.is_and, bit, -left)
            self.clause(gate.is_and, bit, -right)
            self.clause(gate.is_and, -bit, left, right)
            wires.append(bit)
        self.clause(wires[-1] if answer else negate(wires[-1]))

    def write(self, path: Path):
        with path.open("w") as stream:
            stream.write(f"p cnf {self.variables} {len(self.clauses)}\n")
            for clause in self.clauses:
                stream.write(" ".join(map(str, clause)) + " 0\n")

    def read_model(self, true: set[int]) -> list[Gate]:
        # Several selectors may be true. Their input values must agree on
        # every encoded row, so choosing any one of them preserves the model.
        def index(choices):
            return next(i for i, variable in enumerate(choices) if variable in true)
        return list(self.prefix) + [(g.is_and in true, index(g.left), index(g.right)) for g in self.gates]


def search(case: int, seconds: int, solver: str, out: Path | None, all_positives: bool = False,
           point_quadrangles: bool = False, zero_third: bool = False,
           third: Gate | None = None, fourth: Gate | None = None,
           prune_tail: bool = True) -> str:
    rows = test_rows()
    if point_quadrangles:
        point_mask = (1 << 13) - 1
        rows = [(r, y) for r, y in rows if y or (r & point_mask).bit_count() == 4]
        if len(rows) != 286:
            raise ValueError("expected 52 flags and 234 point quadrangles")
    prefix = representatives()[case]
    label = f"case {case}"
    if zero_third:
        if case != 3 or prefix != ((True, 0, 13), (False, 0, 1)):
            raise ValueError("zero-third requires the certified case-3 prefix")
        prefix += ((True, 26, 1),)
        label += " with AND(26,1)"
    if third is not None:
        op, a, b = third
        if len(prefix) != 2 or not (0 <= a <= b < 28):
            raise ValueError("third gate must read two ordered wires of the two-gate prefix")
        prefix += (third,)
        label += f" with {'AND' if op else 'OR'}({a},{b})"
    if fourth is not None:
        op, a, b = fourth
        if len(prefix) != 3 or not 0 <= a <= b < 29:
            raise ValueError("fourth gate needs a three-gate prefix and ordered earlier wires")
        prefix += (fourth,)
        label += f" then {'AND' if op else 'OR'}({a},{b})"
    model = Encoding(prefix, 63)
    if (prune_tail and not point_quadrangles and fourth is not None and
            prefix[:3] == ((True, 0, 13), (False, 0, 14), (True, 1, 13))):
        # PlaneFlagAndTail and PlaneFlagOrTail exclude each homogeneous suffix.
        model.clause(*(g.is_and for g in model.gates))
        model.clause(*(-g.is_and for g in model.gates))
    # Start with both answers. Add concrete counterexamples to each candidate.
    active = set(range(52)) if all_positives else {0, 26}
    active.update((52, 52 + (len(rows) - 52) // 2))
    for i in sorted(active):
        model.add_row(*rows[i])
    candidates = 0
    deadline = monotonic() + seconds
    with tempfile.TemporaryDirectory() as tmp:
        cnf = Path(tmp) / "branch.cnf"
        while monotonic() < deadline:
            model.write(cnf)
            remaining = deadline - monotonic()
            if remaining <= 0:
                break
            try:
                result = subprocess.run([solver, "-q", str(cnf)], capture_output=True, text=True,
                                        timeout=remaining, check=False)
            except subprocess.TimeoutExpired:
                break
            if result.returncode == 20:
                return f"{label}: UNSAT on {len(active)} rows (solver result)"
            if result.returncode != 10:
                raise RuntimeError(f"solver exited with {result.returncode}: {result.stderr[-500:]}")
            true = {int(v) for line in result.stdout.splitlines() if line.startswith("v ")
                    for v in line.split()[1:] if int(v) > 0}
            gates = model.read_model(true)
            candidates += 1
            wrong = [i for i, (r, y) in enumerate(rows) if evaluate(gates, r) != y]
            if not wrong:
                if out:
                    with out.open("x") as stream:
                        for op, left, right in gates:
                            stream.write(f"{'AND' if op else 'OR'} {left} {right}\n")
                return f"{label}: 63-gate witness on all {len(rows)} rows"
            if active.intersection(wrong):
                raise ValueError("decoded model disagrees with an encoded row")
            # Refine both halves so false positives cannot swamp missing flags.
            new = [i for i in wrong if rows[i][1]][:2] + [i for i in wrong if not rows[i][1]][:2]
            for i in new:
                model.add_row(*rows[i])
                active.add(i)
    return f"{label}: UNKNOWN, {len(active)} encoded rows, {candidates} decoded candidates"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--case", type=int, choices=range(68), metavar="0..67")
    parser.add_argument("--seconds", type=int, default=30)
    parser.add_argument("--solver", default="cadical", help="path to a CaDiCaL executable")
    parser.add_argument("--all-positives", action="store_true",
                        help="start with all 52 incident pairs and two negative rows")
    parser.add_argument("--zero-third", action="store_true",
                        help="in case 3 fix AND(26,1), representing 24 equivalent third gates")
    parser.add_argument("--point-quadrangles", action="store_true",
                        help="test this fixed prefix on flags and point quadrangles only; "
                             "the full-set symmetry classification need not apply")
    parser.add_argument("--third", nargs=3, metavar=("OP", "LEFT", "RIGHT"),
                        help="fix a third binary gate (e.g. AND 0 17) after the selected prefix")
    parser.add_argument("--witness", type=Path, help="write a new file only after every selected test passes")
    parser.add_argument("--fourth", nargs=3, metavar=("OP", "LEFT", "RIGHT"),
                        help="fix a fourth binary gate after the third")
    parser.add_argument("--no-tail-pruning", action="store_true",
                        help="omit the two certified gate-type clauses when replaying earlier runs")
    args = parser.parse_args()
    if args.zero_third and args.case != 3:
        parser.error("--zero-third requires --case 3")
    third = None
    if args.third:
        op, a, b = args.third
        if args.case is None or args.zero_third or op not in ("AND","OR"):
            parser.error("--third needs a case, AND or OR, and no other third-gate option")
        try:
            third = (op == "AND", int(a), int(b))
        except ValueError:
            parser.error("wire indices must be integers")
        if not 0 <= third[1] <= third[2] < 28:
            parser.error("expected 0 <= LEFT <= RIGHT < 28")
    fourth = None
    if args.fourth:
        op, a, b = args.fourth
        if not (args.third or args.zero_third) or op not in ("AND", "OR"):
            parser.error("--fourth requires a fixed third gate and AND or OR")
        try:
            fourth = (op == "AND", int(a), int(b))
        except ValueError:
            parser.error("fourth-gate wire indices must be integers")
        if not 0 <= fourth[1] <= fourth[2] < 29:
            parser.error("expected 0 <= LEFT <= RIGHT < 29")
    if args.case is None:
        for i, gates in enumerate(representatives()):
            print(i, " ".join(f"{'AND' if op else 'OR'}({a},{b})" for op, a, b in gates))
        return
    if args.seconds < 1:
        parser.error("--seconds must be positive")
    print(search(args.case, args.seconds, args.solver, args.witness, args.all_positives,
                 args.point_quadrangles, args.zero_third, third, fourth, not args.no_tail_pruning))


if __name__ == "__main__":
    main()
