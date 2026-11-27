"""Cross-check tight initial cover sizes using pinned CaDiCaL and unary counters."""
import argparse
import subprocess

from order3_case35_initial_cover import PREFIX13, POINT7, columns, test_rows


def check(solver, pool, negative, limit):
    wires = [wire for wire in pool if not (wire >> (52 + negative) & 1)]
    count = len(wires)
    clauses = [[i for i, wire in enumerate(wires, 1) if wire >> flag & 1]
               for flag in range(52)]

    def counter(prefix, threshold):
        return count + (prefix - 1) * (limit + 1) + threshold

    # Forward implications force counter(i,r) if >= r of the first i wires
    # were selected. The true prefix counts always extend a valid selection.
    for i in range(1, count + 1):
        clauses.append([-i, counter(i, 1)])
        for r in range(1, min(i - 1, limit + 1) + 1):
            clauses.append([-counter(i - 1, r), counter(i, r)])
            if r <= limit:
                clauses.append([-counter(i - 1, r), -i, counter(i, r + 1)])
    clauses.append([-counter(count, limit + 1)])
    lines = [f"p cnf {counter(count, limit + 1)} {len(clauses)}"]
    lines.extend(" ".join(map(str, clause)) + " 0" for clause in clauses)
    try:
        run = subprocess.run([solver, "-q"], input="\n".join(lines) + "\n",
                             text=True, capture_output=True, timeout=10)
    except subprocess.TimeoutExpired:
        return "UNKNOWN"
    if run.returncode == 20:
        return "UNSAT"
    if run.returncode != 10:
        raise RuntimeError(f"CaDiCaL exited with {run.returncode}: {run.stderr}")

    model = (int(token) for line in run.stdout.splitlines() if line.startswith("v ")
             for token in line.split()[1:])
    selected = [wires[i - 1] for i in model if 0 < i <= count]
    if len(selected) > limit or not all(any(w >> f & 1 for w in selected) for f in range(52)):
        raise ValueError("invalid cover witness")
    return "SAT"


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("solver", help="path to the pinned CaDiCaL binary")
    solver = parser.parse_args().solver
    base = tuple(columns(PREFIX13 + POINT7, test_rows()))
    x = base[5] | base[19]
    for a, b in ((7, 13), (13, 42)):
        y = base[a] | base[b]
        for i, indices in [(11, [48, 53, 377]), (23, [197, 198, 200]), (25, [374, 377, 379])]:
            pool = base + (x, y, y | base[i])
            for j in indices:
                print(a, b, i, j, check(solver, pool, j, 16), check(solver, pool, j, 17))
