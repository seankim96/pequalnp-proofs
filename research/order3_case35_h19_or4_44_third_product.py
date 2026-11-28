"""A third OR is necessary when the first of the two required ORs is OR(4,44)."""
from collections import Counter
import gzip
import json

from order3_case35_colored_trace import witness_graph
from order3_case35_h19_or4_44 import initial
from order3_case35_h19_second_product import seven_probe_floor
from order3_case35_h19_second_or import replay as remaining_first
from order3_case35_h19_two_consecutive_ors import replay as checked_preloads
from order3_case35_point_seven_or_order import guard_unions
from order3_case35_star_packings import ROOT
from order3_case35_star_preloads import dominates
from order3_case35_two_or_preloads import clique


def replay():
    prior = checked_preloads()
    inputs = initial()
    old = inputs[:-1]
    banned = set(guard_unions(old)) - remaining_first()
    # Include even second ORs subsequently excluded by the eight-AND test.
    zs = set(guard_unions(inputs)) - banned
    products = {z & w for z in zs for w in (*inputs,z)}
    required = {p for p in products if not any(dominates(v,p) for v in prior)}
    with gzip.open(ROOT / "case35-h19-or4-44-third-product.json.gz","rt") as f:
        bank, records = json.load(f)
    histogram = Counter()
    for r in records:
        v = int(r[0],16)
        if v not in required:
            raise ValueError("unexpected product")
        pool = [*old,v]
        graph = witness_graph(pool)
        if len(r) == 2:
            group = bank[r[1]]
            clique(graph,group)
            if len(group) <= 128:
                raise ValueError("seven-bit signature bound is insufficient")
            histogram["129-clique"] += 1
        else:
            _,tests,constant,off,floor = r
            bound = seven_probe_floor(pool,graph,[(j,bank[k]) for j,k in tests],
                                      [bank[k] for k in constant],bank[off])
            if bound != floor or bound <= 19:
                raise ValueError("insufficient OR floor")
            histogram[bound] += 1
        required.remove(v)
    if required:
        raise ValueError("untested AND after the second OR")
    print("second ORs",len(zs),"products involving them",len(products),
          "additional witnesses",dict(histogram))
    print("OR(4,44) requires three consecutive non-guard ORs")


if __name__ == "__main__":
    replay()
