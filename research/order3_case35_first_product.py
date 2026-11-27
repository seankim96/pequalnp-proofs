"""Maximize the hard pivots one paid AND can discharge with arbitrary preceding ORs."""
import argparse
from itertools import product
from pathlib import Path
import subprocess

from order3_case35_guarded_covers import cover_requirements
from order3_case35_flat_paid import SEPARATED
from order3_case35_star_packings import PREFIX13, POINT7, columns
from order3_prefix_search import test_rows


def decision(pool, guard_only, k, solver, selected_pivots=None):
    guard = pool[32]
    required = guard >> 52 if guard_only else (1 << 468) - 1
    pivots = [p for p, _ in cover_requirements(pool) if not guard_only or (guard >> p & 1)]
    if selected_pivots is not None:
        pivots = [p for p in pivots if p in selected_pivots]
    sources = sorted(set(pool) | {v & guard for v in pool})
    n = len(sources)
    clauses = [[-i-1, -n-j-1] for i, j in product(range(n), repeat=2)
               if (sources[i] & sources[j]) >> 52 & required]
    top = 2*n + len(pivots) + 1
    one = top
    clauses.append([one])
    prev = [one] + [-one] * k
    for h, p in enumerate(pivots, 1):
        hit = 2*n + h
        for offset in (0, n):
            clauses.append([-hit] + [offset+i for i,v in enumerate(sources, 1) if v >> p & 1])
        row = [one]
        for j in range(1,k+1):
            top += 1
            clauses.extend(([-top, prev[j], hit], [-top, prev[j], prev[j-1]]))
            row.append(top)
        prev = row
    clauses.append([prev[k]])
    cnf = [f"p cnf {top} {len(clauses)}"]
    cnf.extend(" ".join(map(str, c)) + " 0" for c in clauses)
    try:
        r = subprocess.run([solver, "-q"], input="\n".join(cnf)+"\n", text=True,
                           capture_output=True, timeout=30)
    except subprocess.TimeoutExpired:
        return "UNKNOWN", None
    if r.returncode == 20:
        return "UNSAT", None
    if r.returncode != 10:
        raise RuntimeError(r.stderr)
    model = {int(v) for line in r.stdout.splitlines() if line.startswith("v ") for v in line.split()[1:]}
    values = []
    witness = []
    for offset in (0,n):
        selected = [i for i in range(n) if offset+i+1 in model]
        union = 0
        for i in selected:
            union |= sources[i]
        witness.append(selected)
        values.append(union)
    out = values[0] & values[1]
    if out >> 52 & required or sum(out >> p & 1 for p in pivots) < k:
        raise ValueError("invalid product witness")
    return "SAT", witness


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("solver", type=Path)
    solver = parser.parse_args().solver.resolve()
    base = tuple(columns(PREFIX13 + POINT7, test_rows()))
    x, y, z = base[8] | base[25], base[13] | base[42], base[5] | base[18]
    for pool in (base, base + (x,y,z)):
        for guard_only in (False, True):
            for k in range(1, len(cover_requirements(pool))+2):
                verdict, witness = decision(pool, guard_only, k, solver)
                print(len(pool), guard_only, k, verdict, witness, flush=True)
                if verdict != "SAT":
                    break
            pair_verdict, _ = decision(pool, guard_only, 2, solver, SEPARATED)
            print("two of eleven", len(pool), guard_only, pair_verdict)
