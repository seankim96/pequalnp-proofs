"""Rebuild the AND-closure signatures and check the certificate embedded in Lean."""
from pathlib import Path
import re

from order3_case35_fifth_15_17 import prefix
from order3_case35_or_slices import CUTS
from order3_prefix_search import test_rows

PROOF = Path(__file__).resolve().parents[1] / "lean/PEqualNP/Research/PlaneCase35FirstOrFree.lean"


def table(source, name):
    declaration = re.search(r"private def " + name + r" : Array [^\n]+? := #\[(.*?)\]",
                            source, re.DOTALL)
    return [int(entry.strip(), 0) for entry in declaration.group(1).split(",")]


def replay():
    rows = test_rows()
    assert len(rows) == 520 and all(y == (i < 52) for i, (_, y) in enumerate(rows))
    cuts = CUTS[:5]
    raw = [sum(1 << i for i, (r, _) in enumerate(rows) if prefix(r) >> j & 1)
           for j in range(30)]
    closure = {0, (1 << len(rows)) - 1}
    for w in raw:
        closure.update(v & w for v in tuple(closure))
    sampled_rows = [*range(52), *(52+n for n, _ in cuts)]

    def project(w):
        return sum(((w >> r) & 1) << i for i, r in enumerate(sampled_rows))

    words = sorted({project(v) for v in closure})
    ids = {v: i for i, v in enumerate(words)}
    assert len(words) < 128
    generators = [ids[project(v)] for v in raw]
    intersections = [sum(ids[x & y] << (7*j) for j, y in enumerate(words)) for x in (words[i] for i in generators)]
    choices = []
    exceptional = []
    for i, w in enumerate(words):
        assert all(w >> (52+k) & 1 or (w & flags).bit_count() <= 1
                   for k, (_, flags) in enumerate(cuts))
        compatible = [k for k, (_, flags) in enumerate(cuts)
                      if w >> (52+k) & 1 or not w & flags]
        if not compatible:
            exceptional.append(i)
        choices.append(compatible[0] if compatible else 0)
    assert exceptional == [generators[13]]
    source = PROOF.read_text()
    for name, values in [('signatures', words), ('generators', generators),
                         ('intersections', intersections), ('witnesses', choices)]:
        assert table(source, name) == values, name
    print('distinct conjunctions on 520 labels:', len(closure))
    print('distinct signatures on 57 selected rows:', len(words))
    print('checked generator/signature intersections:', len(generators)*len(words))
    print('exceptional signature equals wire 13:', exceptional[0])


if __name__ == '__main__':
    replay()
