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


def evaluate(gates: list[Gate] | tuple[Gate, ...], row: int) -> bool:
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

    def require_at_least(self, literals: list[int], minimum: int):
        """Force a threshold by witnessing enough true literals in successive prefixes."""
        if not 0 <= minimum <= len(literals):
            raise ValueError("threshold out of range")
        reached = [True] + [False] * minimum
        for literal in literals:
            next_row = [True]
            for count in range(1, minimum + 1):
                witness = self.fresh()
                # Either the previous prefix suffices or this literal extends it.
                self.clause(-witness, reached[count], literal)
                self.clause(-witness, reached[count], reached[count - 1])
                next_row.append(witness)
            reached = next_row
        self.clause(reached[minimum])

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
           prune_tail: bool = True, operator_bounds: bool = False, fifth: Gate | None = None,
           sixth: Gate | None = None, seventh: Gate | None = None,
           eighth: Gate | None = None, ninth: Gate | None = None,
           negative_seeds: tuple[int, ...] = (), *, tenth: Gate | None = None) -> str:
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
    for name, gate, position in (("fifth", fifth, 5), ("sixth", sixth, 6),
                                 ("seventh", seventh, 7), ("eighth", eighth, 8), ("ninth", ninth, 9),
                                 ("tenth", tenth, 10)):
        if gate is None:
            continue
        op, a, b = gate
        if len(prefix) != position - 1 or not 0 <= a <= b < 26 + len(prefix):
            raise ValueError(f"{name} gate needs its full prefix and ordered earlier wires")
        prefix += (gate,)
        label += f" then {'AND' if op else 'OR'}({a},{b})"
    model = Encoding(prefix, 63)
    if (prune_tail and not point_quadrangles and len(prefix) == 4 and
            prefix[:3] == ((True, 0, 13), (False, 0, 14), (True, 1, 13))):
        # PlaneFlagAndTail and PlaneFlagOrTail exclude each homogeneous suffix.
        model.clause(*(g.is_and for g in model.gates))
        model.clause(*(-g.is_and for g in model.gates))
    if operator_bounds:
        if point_quadrangles:
            raise ValueError("operator bounds require the full 520-row problem")
        flags = [gate.is_and for gate in model.gates]
        min_or = 18 - sum(not gate[0] for gate in prefix[:5])
        sixth_and = int(sixth is not None and sixth[0])
        later_and = sum(g[0] for g in prefix[6:])
        later_or = sum(not g[0] for g in prefix[6:])
        sixth_or = int(sixth is not None and not sixth[0])
        if len(prefix) >= 4 and prefix[:3] == ((True, 0, 13), (False, 0, 14), (True, 1, 13)):
            # PlaneAllFourthAndCount and PlaneAllFourthOrCount cover all 1,682 codes.
            min_and = 9 - int(fifth is not None and fifth[0])
            min_or = 18 - int(fifth is not None and not fifth[0])
            if fourth == (True, 1, 18) and fifth is not None and fifth[0]:
                # Plane888FifthAndCodes: the fifth AND is false outside these nine flags.
                support = sum(1 << i for i, (row, positive) in enumerate(rows)
                              if positive and evaluate(prefix[:5], row))
                if support & ~0x1604E3 == 0:
                    min_and = 9
            model.require_at_least(flags, min_and - sixth_and - later_and)
        if len(prefix) >= 4 and prefix[:2] == ((False, 0, 1), (False, 3, 9)):
            # The 19 flags at negative row 159 already separate the 28 base wires.
            min_or = 18 - sum(not gate[0] for gate in prefix[2:5])
            # Charge each already-fixed AND against the generic fourth-gate bound.
            min_and = 9 - int(fifth is not None and fifth[0]) - sixth_and
            if prefix[2:4] == ((True, 15, 27), (True, 17, 26)):
                # PlaneCase35FirstOrFree requires 19 ORs strictly after gate four.
                min_or = 19 - int(fifth is not None and not fifth[0])
                # The uniform fifth- and sixth-gate theorems retain all nine ANDs.
                min_and = 9
            min_and -= later_and
            if (prefix[2:4] == ((True, 15, 27), (True, 17, 26)) and seventh is not None
                    and {fifth, sixth} == {(True, 13, 26), (True, 13, 27)}):
                # The uniform seventh- and eighth-gate bounds cover these two orders.
                min_and = 9 - sum(g[0] for g in prefix[8:])
                if ninth is not None and {seventh, eighth} == {(True, 0, 17), (True, 0, 23)}:
                    min_and = 9 - sum(g[0] for g in prefix[9:])  # PlaneCase35NinthTraceBound
            if (prefix[2:4] == ((True, 15, 27), (True, 17, 26)) and len(prefix) >= 7):
                # PlaneCase35GuardedPoolTraceBound allows any number of guarded wires
                # before the last two free choices. Check only its silent-wire alternative.
                guard = {0, 1, 2, 3, 16, 40}
                if all(not evaluate(prefix[:end], row)
                       for end in range(5, len(prefix) - 1)
                       for i, (row, yes) in enumerate(rows) if yes and i not in guard):
                    min_and = 9
            if prefix[2:4] == ((True, 15, 27), (True, 17, 26)):
                # OR preserves domination by an active base wire. Each subsequent
                # AND is safe if it is silent outside the certified 13 flags.
                omitted = {0, 1, 2, 3, 5, 6, 7, 9, 15, 16, 22, 33, 42}
                if all(not evaluate(prefix[:end], row)
                       for end in range(5, len(prefix)+1) if prefix[end-1][0]
                       for i, (row, yes) in enumerate(rows) if yes and i not in omitted):
                    min_and = 9  # PlaneCase35ThirteenFlagSuffix
            model.require_at_least(flags, min_and)
        model.require_at_least([-flag for flag in flags], min_or - sixth_or - later_or)
    # Start with both answers. Add concrete counterexamples to each candidate.
    active = set(range(52)) if all_positives else {0, 26}
    active.update((52, 52 + (len(rows) - 52) // 2))
    for n in negative_seeds:
        if not 0 <= n < len(rows) - 52:
            raise ValueError("negative seed index outside the selected negative family")
        active.add(52 + n)
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
    parser.add_argument("--negative-seed", type=int, action="append", default=[],
                        help="also encode this zero-based index in the selected negative family (repeatable)")
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
    parser.add_argument("--fifth", nargs=3, metavar=("OP", "LEFT", "RIGHT"),
                        help="fix a fifth binary gate after the fourth")
    parser.add_argument("--sixth", nargs=3, metavar=("OP", "LEFT", "RIGHT"),
                        help="fix a sixth binary gate after the fifth")
    parser.add_argument("--seventh", nargs=3, metavar=("OP", "LEFT", "RIGHT"),
                        help="fix a seventh binary gate after the sixth")
    parser.add_argument("--eighth", nargs=3, metavar=("OP", "LEFT", "RIGHT"),
                        help="fix a eighth binary gate after the seventh")
    parser.add_argument("--ninth", nargs=3, metavar=("OP", "LEFT", "RIGHT"),
                        help="fix a ninth binary gate after the eighth")
    parser.add_argument("--tenth", nargs=3, metavar=("OP", "LEFT", "RIGHT"),
                        help="fix a tenth binary gate after the ninth")
    parser.add_argument("--no-tail-pruning", action="store_true",
                        help="omit the two certified gate-type clauses when replaying earlier runs")
    parser.add_argument("--operator-bounds", action="store_true",
                        help="apply certified full-row lower bounds on AND and OR counts")
    args = parser.parse_args()
    if args.operator_bounds and args.point_quadrangles:
        parser.error("--operator-bounds requires the full row set")
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
    extra_gates = []
    previous = fourth
    for position, name in enumerate(("fifth", "sixth", "seventh", "eighth", "ninth", "tenth"), start=5):
        operand_spec = getattr(args, name)
        gate = None
        if operand_spec:
            op, left, right = operand_spec
            if previous is None or op not in ("AND", "OR"):
                parser.error(f"--{name} requires the previous gate and AND or OR")
            try:
                gate = (op == "AND", int(left), int(right))
            except ValueError:
                parser.error(f"{name}-gate wire indices must be integers")
            limit = 26 + position - 1
            if not 0 <= gate[1] <= gate[2] < limit:
                parser.error(f"expected 0 <= LEFT <= RIGHT < {limit}")
        extra_gates.append(gate)
        previous = gate
    if args.case is None:
        for i, gates in enumerate(representatives()):
            print(i, " ".join(f"{'AND' if op else 'OR'}({a},{b})" for op, a, b in gates))
        return
    if args.seconds < 1:
        parser.error("--seconds must be positive")
    print(search(args.case, args.seconds, args.solver, args.witness, args.all_positives,
                 args.point_quadrangles, args.zero_third, third, fourth, not args.no_tail_pruning, args.operator_bounds, *extra_gates[:5], negative_seeds=tuple(args.negative_seed), tenth=extra_gates[5]))


if __name__ == "__main__":
    main()
