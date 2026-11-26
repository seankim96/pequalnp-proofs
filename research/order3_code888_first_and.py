"""Check separation after arbitrary OR gates and the first further AND in case 6, code 888."""
from collections import Counter
from functools import lru_cache

from order3_code888_fifth import start
from order3_prefix_search import test_rows
from order3_robust_flag_families import select


def negative_graph(positives, negatives):
    bad = [0] * len(negatives)
    for j, right in enumerate(negatives):
        for i, left in enumerate(negatives[:j]):
            if not any(p & ~(left | right) == 0 for p in positives):
                bad[i] |= 1 << j
                bad[j] |= 1 << i
    return bad


def balanced_disjunctions(rows, sample):
    # Distinguish disjunctions on ALL 520 rows. Prune only by their counts on
    # the initial, pairwise separated negative sample. An added wire can only
    # enlarge an OR. Wire 27 is already the OR of original wires 0 and 14.
    states = {0}
    for k in range(30):
        if k == 27:
            continue
        column = sum(1 << i for i, row in enumerate(rows) if row >> k & 1)
        states.update({old | column for old in states if ((old | column) & sample).bit_count() <= 256})
    # Constant true also has more than 256 true negatives on this sample.
    return sorted(s for s in states if (sample & ~s).bit_count() <= 256), len(states)


def verify_or_closure(rows, sample, expected):
    # Independently traverse subsets of all thirty physical wires, including
    # the redundant OR at 27. Count entire subtrees when monotonicity prunes.
    columns = [sum(1 << i for i, row in enumerate(rows) if row >> k & 1) for k in range(30)]
    balanced = set()

    def visit(k, signature):
        if (signature & sample).bit_count() > 256:
            return 1 << (len(columns) - k)
        if k == len(columns):
            if (sample & ~signature).bit_count() <= 256:
                balanced.add(signature)
            return 1
        return visit(k + 1, signature) + visit(k + 1, signature | columns[k])

    assert visit(0, 0) == 1 << 30
    assert balanced == set(expected)


def verify_families(positives, negatives, bad, columns, find_family):
    # This verification does not use the searcher's transposed compatibility
    # table. Compute the exact set of witnesses for each pair from the rows.
    witnesses = [[sum(1 << j for j, p in enumerate(positives) if p & ~(a | b) == 0)
                  for a in negatives[:i]] for i, b in enumerate(negatives)]
    for column in columns:
        chosen = find_family(column)
        pos = column >> len(negatives)
        assert chosen.bit_count() >= 257
        absent = []
        for i in range(len(negatives)):
            if not (chosen >> i & 1):
                continue
            assert not (chosen & bad[i])
            if not (column >> i & 1):
                assert all(witnesses[i][j] & ~pos for j in absent)
                absent.append(i)


def direct_family(positives, negatives):
    @lru_cache(None)
    def contains(bits):
        return sum(1 << i for i, row in enumerate(negatives) if row & bits == bits)

    matches = [[contains(p & ~row) for p in positives] for row in negatives]
    cut = len(negatives)
    negative_bits = (1 << cut) - 1

    @lru_cache(None)
    def select_family(column):
        pos, neg = column >> cut, column & negative_bits
        chosen = 0
        for i, candidates in enumerate(matches):
            covered = 0
            for j, compatible in enumerate(candidates):
                if pos >> j & 1 and not neg >> i & 1:
                    compatible &= neg
                covered |= compatible
                if covered & chosen == chosen:
                    chosen |= 1 << i
                    break
        return chosen

    return select_family


def main():
    tests = test_rows()
    positives = [start(r) for r, y in tests if y]
    negatives = [start(r) for r, y in tests if not y]
    bad = negative_graph(positives, negatives)
    # This graph is a matching plus isolated vertices. This lets us compute
    # the exact independence number of any induced subgraph.
    assert all(mask.bit_count() <= 1 for mask in bad)
    edges = [(1 << i) | m for i, m in enumerate(bad) if m > 1 << i]
    sample = sum(1 << i for i in select([bad], 0))
    assert len(edges) == 54 and sample.bit_count() == 414
    full = (1 << len(negatives)) - 1

    def independent(mask):
        return mask.bit_count() - sum(mask & edge == edge for edge in edges)

    choices, states = balanced_disjunctions(negatives + positives, sample)
    verify_or_closure(negatives + positives, sample, choices)
    restricted = [column & sample for column in choices]
    counts = [column.bit_count() for column in restricted]
    find_family = direct_family(positives, negatives)
    exact = Counter()
    final_columns = set()
    sample_size = sample.bit_count()
    both_large = 0
    worst_column = None
    worst = len(negatives) + 1
    for j, right in enumerate(restricted):
        for i in range(j):
            # Only a pair with opposite (1,0) and (0,1) operand values can
            # lose its positive witness after adding the AND. Dropping either
            # of those two classes eliminates all such conflicts.
            smaller = min(counts[i], counts[j]) - (restricted[i] & right).bit_count()
            if sample_size - smaller >= 257:
                continue
            both_large += 1
            a, b = choices[i] & full, choices[j] & full
            if max(independent(full & ~(a & ~b)), independent(full & ~(b & ~a))) >= 257:
                continue
            column = choices[i] & choices[j]
            final_columns.add(column)
            size = find_family(column).bit_count()
            exact[size] += 1
            if size < worst:
                worst, worst_column = size, column
    assert worst >= 257 and worst_column is not None
    verify_families(positives, negatives, bad, final_columns, find_family)
    # Scalar replay of every pair in one smallest final family, with the
    # derived AND column included as wire 30.
    chosen = find_family(worst_column)
    lifted_pos = [p | (((worst_column >> (len(negatives) + j)) & 1) << 30)
                  for j, p in enumerate(positives)]
    lifted_neg = [n | (((worst_column >> i) & 1) << 30)
                  for i, n in enumerate(negatives) if chosen >> i & 1]
    for j, right in enumerate(lifted_neg):
        for left in lifted_neg[:j]:
            assert any(p & ~(left | right) == 0 for p in lifted_pos)
    print(f"initial conflicts: {len(edges)} disjoint pairs; initial sample: {sample.bit_count()}")
    print(f"capped OR closure: {states} signatures; balanced: {len(choices)}")
    print(f"unordered distinct balanced pairs: {len(choices) * (len(choices)-1) // 2}")
    print(f"survived sample: {both_large}; survived matching: {sum(exact.values())}")
    print(f"distinct final AND signatures: {find_family.cache_info().currsize}")
    print(f"final family sizes and multiplicities: {sorted(exact.items())}")
    print(f"independent checks: all 2^30 input subsets accounted for and {len(final_columns)} families replayed")
    print(f"scalar replay: {len(lifted_neg) * (len(lifted_neg)-1) // 2} pairs")


if __name__ == "__main__":
    main()
