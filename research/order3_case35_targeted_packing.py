"""Find a pivot certificate for one specific OR left open by the shared bank."""
import argparse
from functools import lru_cache
import json
from pathlib import Path

from order3_case35_first_or import packing
from order3_case35_point_seven_or_order import guard_unions, verify_union_data
from order3_case35_star_packings import PREFIX13, POINT7, columns
from order3_prefix_search import test_rows


def target_union(base, candidate, width, seconds):
    import numpy as np
    from scipy.optimize import Bounds, LinearConstraint, milp

    pool = (*base, candidate)
    constraints = [
        LinearConstraint(np.array([[column >> p & 1 for p in range(52)]
                                   for column in pool if not column >> (52+j) & 1]), -np.inf, 1)
        for j in range(468)
    ]

    @lru_cache(None)
    def find_flags(j, excluded):
        upper = [not (excluded >> p & 1) for p in range(52)]
        solution = milp(-np.ones(52), integrality=np.ones(52), bounds=Bounds(0, upper),
                        constraints=constraints[j], options={"time_limit": seconds})
        if solution.x is None:
            return None
        flags = tuple(np.flatnonzero(solution.x > 0.5).tolist()[:width])
        if len(flags) == width:
            packing(pool, (j, flags))
            return flags
        return None

    available = {j: flags for j in range(468) if (flags := find_flags(j, 0))}
    positive_mask = (1 << 52) - 1

    @lru_cache(None)
    def eliminate(leaf):
        for j, flags in available.items():
            if leaf >> (52+j) & 1 or all(not leaf >> p & 1 for p in flags):
                return j, flags
        # A packing that avoids this leaf's positive support eliminates it too.
        for j in available:
            if flags := find_flags(j, leaf & positive_mask):
                return j, flags
        return None

    pivots = []
    for p in range(52):
        leaves = set()
        for value in pool:
            if value >> p & 1:
                leaves |= {value} | {leaf & value for leaf in leaves}
        pivots.append((p, leaves))
    for pivot, leaves in sorted(pivots, key=lambda item: len(item[1])):
        witnesses = set()
        for leaf in sorted(leaves, key=int.bit_count):
            witness = eliminate(leaf)
            if witness is None:
                break
            witnesses.add(witness)
        else:
            tests = sorted(witnesses)
            index = guard_unions(base).index(candidate)
            data = {"tests": tests, "witnesses": [[index, pivot, list(range(len(tests)))]]}
            if verify_union_data(base, data, width) != {candidate}:
                raise ValueError("pivot certificate failed replay")
            return data
    return None


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--union", type=int, nargs=2, action="append", default=[])
    parser.add_argument("--candidate", type=int, nargs=2, required=True)
    parser.add_argument("--milp-seconds", type=float, default=1.0)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    if len(args.union) >= 19 or args.milp_seconds <= 0:
        parser.error("expected a positive width and per-query time budget")
    base = columns(PREFIX13 + POINT7, test_rows())
    for a,b in [*args.union, args.candidate]:
        if not 0 <= min(a,b) <= max(a,b) < len(base):
            parser.error("invalid OR operand")
        base.append(base[a] | base[b])
    candidate = base.pop()
    data = target_union(tuple(base), candidate, 19-len(args.union), args.milp_seconds)
    if data is None:
        print("UNKNOWN: no pivot certificate found")
        return
    with args.out.open("x") as stream:
        stream.write(json.dumps(data, separators=(",", ":")) + "\n")
    print("certified exclusion;", len(data["tests"]), "packings")


if __name__ == "__main__":
    main()
