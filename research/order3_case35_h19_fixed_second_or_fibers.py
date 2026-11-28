"""Check stronger OR floors on the remaining AND, OR(14,18), AND cases."""
from collections import Counter
import gzip
import json

from order3_case35_h19_exceptional_floor import replay_bound
from order3_case35_h19_first_or import parent_pool
from order3_case35_h19_fixed_second_or import replay as previous_frontier
from order3_case35_h19_or4_44 import prune_sources
from order3_case35_star_packings import ROOT


def replay():
    pending = previous_frontier()
    base = list(parent_pool())
    union = base[14] | base[18]
    floors = Counter()
    with gzip.open(ROOT / "case35-h19-fixed-second-or-fibers.json.gz", "rt") as stream:
        for a_hex, p_hex, cert, fibers in json.load(stream):
            a, p = int(a_hex, 16), int(p_hex, 16)
            pool = prune_sources([*base, a, union, p])
            floor = replay_bound(pool, cert, fibers)[-1]
            if floor <= 18:
                raise ValueError("floor does not exceed the remaining OR budget")
            pending.remove((a, p))
            floors[floor] += 1
    print("additional checked floors", sorted(floors.items()), "remaining", len(pending))
    return pending


if __name__ == "__main__":
    replay()
