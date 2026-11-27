"""Exact initial-wire cover sizes for the six OR(5,19) frontiers on 520 rows."""
from functools import lru_cache

from order3_case35_point_seven_or_order import guard_unions
from order3_case35_star_packings import PREFIX13, POINT7, columns
from order3_prefix_search import test_rows


FLAGS = (1 << 52) - 1


def cover_solver(pool, negative):
    """Return minimum number of negative-false initial wires covering a flag mask."""
    supports = {wire & FLAGS for wire in pool if not (wire >> (52 + negative) & 1)}
    maximal = [s for s in supports if s and not any(s != t and s & t == s for t in supports)]
    choices = [[s for s in maximal if s >> f & 1] for f in range(52)]
    order = sorted(range(52), key=lambda f: len(choices[f]))

    @lru_cache(None)
    def solve(mask):
        if not mask:
            return 0
        f = next(f for f in order if mask >> f & 1)
        return 1 + min((solve(mask & ~s) for s in choices[f]), default=float("inf"))

    return solve


def census(pool):
    costs = [cover_solver(pool, j)(FLAGS) for j in range(468)]
    # After prepaying a fourth OR, 15 ORs remain. Sixteen initial wires
    # must cover all flags. An old optimal cover of size <=16 still works.
    hard = [(j, cover_solver(pool, j)) for j, size in enumerate(costs) if size > 16]
    candidates = guard_unions(pool)
    survivors = [v for v in candidates if all(
        not (v >> (52+j) & 1) and solve(FLAGS & ~v) <= 15 for j,solve in hard)]
    return max(costs), [j for j,_ in hard], len(candidates), len(survivors)


if __name__ == "__main__":
    base = tuple(columns(PREFIX13 + POINT7, test_rows()))
    x = base[5] | base[19]
    for a,b in [(7,13), (13,42)]:
        y = base[a] | base[b]
        for i in (11,23,25):
            print((a,b,i), census(base + (x,y,y | base[i])), flush=True)
