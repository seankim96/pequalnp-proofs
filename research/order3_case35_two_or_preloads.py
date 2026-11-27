"""Exclude a first paid AND after at most two suffix ORs at the h=24 boundary."""
from collections import defaultdict
from functools import reduce
from itertools import combinations, combinations_with_replacement
import json
from operator import and_, or_

from order3_case35_colored_trace import density, witness_graph
from order3_case35_first_or import PREFIX13, packing
from order3_case35_preload_density import ROOT, columns, evaluator, verify_sparse

POS = (1 << 52) - 1


def lightest(bits, count, implication=False):
    return sum(sorted(w.bit_count() for w in range(1 << bits)
                      if not implication or not w & 1 or w & 2)[:count])


def clique(graph, rows):
    if len(set(rows)) != len(rows) or any(not 0 <= j < 468 for j in rows):
        raise ValueError("invalid negative indices")
    if any(not graph[a, b] for a, b in combinations(rows, 2)):
        raise ValueError("missing separating witness for a pair")


def single_certificate(pool, cert):
    value = int(cert["word"], 16)
    inputs = pool + [value]
    graph = witness_graph(inputs)
    rows = [j for j, _ in cert["rows"]]
    k = len(rows)
    if not 160 < k <= 192:
        raise ValueError("this certificate expects between 161 and 192 rows")
    clique(graph, rows)
    width = 0
    for j, flags in cert["rows"]:
        packing(inputs, (j, flags))
        width += len(flags)
    off = cert["guard_off"]
    clique(graph, off)
    if len(off) <= 64 or any(pool[32] >> (52+j) & 1 for j in off):
        raise ValueError("expected more than 64 guard-false negatives")
    constant = set()
    for word, (bit, family) in cert["constants"]:
        v = int(word, 16)
        clique(graph, family)
        if len(family) < 129 or any((v >> (52+j) & 1) != bit for j in family):
            raise ValueError("invalid constant-port exclusion")
        constant.add(v)
    # In an orientation with a paid-output probe, its bit implies a distinct
    # earlier probe bit. In particular it is true in at most 64 codewords.
    # Two different receivers cannot have paid-output ports on a >160 clique.
    # Each orientation therefore loses at most this one paid-output probe.
    useful = min(lightest(8, k), lightest(8, k, implication=True) - 64)
    exceptional = []
    for c in inputs:
        ones = sum((c >> (52+j)) & 1 for j in rows)
        if c in constant or max(ones, k-ones) >= 129:
            continue
        on_off = sum((c >> (52+j)) & 1 for j in off)
        exceptional.append((min(128, ones), on_off))
    raw_cost = sum(weight for weight, _ in exceptional)
    loss = raw_cost
    if len(off) < 129:
        # Two receiving gates probing guard-AND outputs would lose two bits
        # on 'off'. With one receiving gate fixed to zero on 'off', every
        # other gate must be balanced to within [|off|-64,64] there.
        stable = sum(weight for weight, hits in exceptional if len(off)-64 <= hits <= 64)
        unstable = sorted((weight for weight, hits in exceptional
                           if not len(off)-64 <= hits <= 64), reverse=True)
        guard_on = min(128, sum((pool[32] >> (52+j)) & 1 for j in rows))
        for cheap in (1, 2):
            loss = max(loss, cheap*guard_on + stable + sum(unstable[:2-cheap]))
    minimum = (width + 2*useful - loss + k-1)//k - 1
    if minimum <= 19:
        raise ValueError("certificate leaves a 19-OR continuation")
    return minimum


def verify(pool):
    if density(pool, ROOT / "case35-or-trace-density.json")["required_ors"] < 24:
        raise ValueError("missing eight-paid baseline")
    verify_sparse(pool)
    budget = evaluator(pool)
    dominators = [v for v in pool if budget(v, True)[1] > 19]
    base = set(pool) | {v & pool[32] for v in pool}
    pairs = {a | b for a, b in combinations_with_replacement(base, 2)}
    triples = {u | b for u in pairs for b in base}
    # A union of at most three members costs at most two ORs, regardless of
    # how many cheap mask gates are needed. Replacing a paid gate by such a
    # construction leaves eight paid ANDs and at most 21 ORs, below 24.
    def residual(values):
        distinct = {v for v in values if v not in triples and (v & POS).bit_count() >= 3}
        return {v for v in distinct if all(v & ~d for d in dominators)}
    crossed = residual(a & b for a, b in combinations_with_replacement(pairs, 2))
    nested = residual(t & b for t in triples for b in base)
    families = defaultdict(list)
    for v in sorted(crossed | nested):
        families[v & POS].append(v)
    difficult = {}
    for c in json.loads((ROOT / "case35-two-or-exceptions.json").read_text()):
        difficult[int(c["word"], 16)] = single_certificate(pool, c)
    used = set()
    def check(block):
        _, bound = budget(reduce(or_, block), True, reduce(and_, block))
        if bound > 19:
            return
        if len(block) == 1:
            if block[0] not in difficult:
                raise ValueError("unresolved exact output")
            used.add(block[0])
            return
        mid = len(block)//2
        check(block[:mid])
        check(block[mid:])
    for block in families.values():
        check(block)
    if used != set(difficult):
        raise ValueError("exception certificate no longer matches enumerated outputs")
    return dict(masked_base=len(base), pair_unions=len(pairs), triple_unions=len(triples),
                crossed=len(crossed), nested=len(nested), residual=len(crossed | nested),
                positive_classes=len(families), exceptional_bounds=sorted(difficult.values()))


if __name__ == "__main__":
    from order3_prefix_search import test_rows
    print(verify(columns(PREFIX13, test_rows())))
