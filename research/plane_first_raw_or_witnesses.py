"""Test positive-pair intersections after any one OR on two raw wires."""
from itertools import combinations, combinations_with_replacement
from order3_prefix_search import test_rows


def main():
    positives = [x for x, label in test_rows() if label]
    negatives = [x for x, label in test_rows() if not label]
    negative_columns = [
        sum(1 << i for i, x in enumerate(negatives) if x & (1 << j))
        for j in range(26)
    ]
    all_negatives = (1 << len(negatives)) - 1
    gates = list(combinations_with_replacement(range(26), 2))
    conflicts = {gate: [] for gate in gates}
    total = 0
    for a, b in combinations(range(len(positives)), 2):
        x, y = positives[a], positives[b]
        eligible = sum(1 << i for i, n in enumerate(negatives) if (x & y) & ~n == 0)
        for left, right in gates:
            inputs = (1 << left) | (1 << right)
            needs_or = bool(x & inputs) and bool(y & inputs)
            on = negative_columns[left] | negative_columns[right]
            support = eligible & (on if needs_or else all_negatives)
            if not support:
                conflicts[left, right].append((a, b))
            total += 1
    assert total == 1326 * 351
    from collections import Counter
    profile = Counter()
    for gate, edges in conflicts.items():
        # Retain a subset whose every pair has a negative witness.
        removed = set()
        pending = edges[:]
        while pending:
            counts = Counter(v for edge in pending for v in edge)
            vertex = counts.most_common(1)[0][0]
            removed.add(vertex)
            pending = [e for e in pending if vertex not in e]
        assert all(a in removed or b in removed for a, b in edges)
        profile[len(positives) - len(removed)] += 1
        if gate == (0, 14):
            print("code-975 first OR", len(edges), "conflicts;", len(positives)-len(removed), "retained positives")
    print(total, 'pair/gate cases; retained positives -> gate count', sorted(profile.items()))
    assert min(profile) >= 33


if __name__ == '__main__':
    main()
