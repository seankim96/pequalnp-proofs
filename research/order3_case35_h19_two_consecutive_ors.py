"""Check that two non-guard ORs must precede the next ordinary AND in case 35."""
from collections import Counter
import gzip
import json

from order3_case35_colored_trace import witness_graph
from order3_case35_h19_second_or import replay as remaining_unions
from order3_case35_h19_second_product import read_ledger, replay as check_old, seven_probe_floor
from order3_case35_star_packings import ROOT, PREFIX13, POINT7, columns
from order3_case35_star_preloads import dominates
from order3_case35_two_or_preloads import clique
from order3_prefix_search import test_rows


def replay():
    check_old()
    unions = remaining_unions()
    base = columns(PREFIX13 + POINT7 + ((False, 14, 18), (True, 1, 43)), test_rows())
    guard = base[32]
    old = {int(word,16) for word in read_ledger("next-and")}
    old.update(int(row[0],16) for row in read_ledger("density"))
    free = old | set(base)
    free.update(v & guard for v in tuple(free))
    free.add(0)
    # An AND of two old sources commutes before the new OR. Otherwise,
    # prepay (new OR) AND (old source), then reconstruct the OR at normal
    # cost. Intervening guard reads need at most another free guard mask.
    products = {v & y for y in unions for v in (*base, y)}
    needed = {v for v in products if not any(dominates(w,v) for w in free)}
    with gzip.open(ROOT / "case35-h19-ordinary-after-one-or.json.gz","rt") as f:
        groups, records = json.load(f)
    floors = Counter()
    for record in records:
        v = int(record[0],16)
        if v not in needed:
            raise ValueError("duplicate or unexpected product")
        inputs = [*base,v]
        graph = witness_graph(inputs)
        if len(record) == 2:
            rows = groups[record[1]]
            clique(graph,rows)
            if len(rows) <= 128:
                raise ValueError("seven bits may suffice")
            floors["129-clique"] += 1
        else:
            _, tests, constant, off, claimed = record
            packs = [(j,groups[i]) for j,i in tests]
            floor = seven_probe_floor(inputs, graph, packs,
                                      [groups[i] for i in constant],groups[off])
            if floor != claimed or floor <= 19:
                raise ValueError("no contradiction at nineteen ORs")
            floors[floor] += 1
        needed.remove(v)
    if needed:
        raise ValueError("missing products")
    print("first OR values",len(unions),"associated products",len(products),
          "additional certificates",len(records),dict(floors))
    print("first OR values permitting an ordinary AND immediately afterwards",0)
    return free | {int(record[0],16) for record in records}


if __name__ == "__main__":
    replay()
