"""Match clique lower and coloring upper bounds on each residual witness graph."""
from collections import Counter
import gzip
from itertools import combinations
import json

from order3_case35_colored_trace import witness_graph
from order3_case35_h19_first_or import parent_pool
from order3_case35_h19_fixed_second_or_fibers import replay as frontier
from order3_case35_h19_or4_44 import prune_sources
from order3_case35_star_packings import ROOT


def replay():
    pending = frontier()
    base = list(parent_pool())
    union = base[14] | base[18]
    sizes = Counter()
    with gzip.open(ROOT / "case35-h19-residual-colors.json.gz", "rt") as stream:
        for a_hex, p_hex, clique, classes in json.load(stream):
            a, p = int(a_hex, 16), int(p_hex, 16)
            pending.remove((a, p))
            graph = witness_graph(prune_sources([*base, a, union, p]))
            if sorted(i for group in classes for i in group) != list(range(468)):
                raise ValueError("coloring must partition all negative rows")
            if not all(classes) or any(graph[i,j] for group in classes for i,j in combinations(group,2)):
                raise ValueError("invalid independent color class")
            if (len(set(clique)) != len(classes) or len(clique) != len(classes)
                    or any(i not in range(468) for i in clique)
                    or any(not graph[i,j] for i,j in combinations(clique,2))):
                raise ValueError("missing matching clique lower bound")
            sizes[len(clique)] += 1
    if pending:
        raise ValueError("uncovered residual cases")
    print("exact clique and chromatic numbers (size, cases)", sorted(sizes.items()))


if __name__ == "__main__":
    replay()
