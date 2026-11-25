"""Classify third gates on the 520 certified rows for a fixed two-gate prefix.

The circuit model permits reading any previous wire repeatedly. Raw wire
renamings preserve both gates, and equal tested columns allow the same suffix.
"""
from collections import Counter
from itertools import combinations
from order3_prefix_search import DIFFERENCES, representatives, test_rows

def stabilizer():
    neighbors = [set() for _ in range(26)]
    for p in range(13):
        for l in range(13):
            if (p-l) % 13 in DIFFERENCES:
                neighbors[p].add(13+l)
                neighbors[13+l].add(p)
    def extend(mapping):
        if len(mapping) == 26:
            yield tuple(mapping[i] for i in range(26))
            return
        unused = set(range(26)).difference(mapping.values())
        def choices(i):
            return [j for j in unused if i//13 == j//13 and
                    all((k in neighbors[i]) == (v in neighbors[j]) for k,v in mapping.items())]
        available, i = min(((choices(i),i) for i in range(26) if i not in mapping),
                           key=lambda item: len(item[0]))
        for j in available:
            yield from extend(dict(mapping) | {i:j})
    dual = tuple((1-i//13)*13 + (-i)%13 for i in range(26))
    for p in extend({0:0,13:13}):
        yield p+(26,27)
        yield tuple(dual[i] for i in p)+(26,27)

def move(r,p):
    result = 0
    while r:
        bit = r & -r
        result |= 1 << p[bit.bit_length()-1]
        r ^= bit
    return result

def classify(case=5):
    rows = test_rows()
    pin, second = representatives()[case]
    if pin != (True,0,13):
        raise ValueError("the first gate must be AND(0,13)")
    is_and, a, b = second
    raw = [sum(((r >> i)&1) << k for k,(r,_) in enumerate(rows)) for i in range(26)]
    cols = raw+[raw[0]&raw[13]]
    cols.append(cols[a] & cols[b] if is_and else cols[a] | cols[b])
    old = set(cols)
    gates = [(op,i,j) for op in ('AND','OR') for i,j in combinations(range(28),2)]
    def sig(g):
        op,i,j = g
        return cols[i]&cols[j] if op == 'AND' else cols[i]|cols[j]
    fresh = {g:sig(g) for g in gates if sig(g) not in old}
    group = [p for p in stabilizer() if {p[a],p[b]} == {a,b}]
    labels = dict(rows)
    for p in group:
        assert len(set(p)) == 28 and {p[0],p[13]} == {0,13}
        assert all(labels.get(move(r,p)) == y for r,y in rows)
    assert len(set(group)) == len(group)
    # Choose the first syntax of each same-column class before taking orbits.
    first = {}
    for g,v in fresh.items():
        first.setdefault(v,g)
    def representative(g):
        op,i,j = g
        orbit = [(op,*sorted((p[i],p[j]))) for p in group]
        return min(first[fresh[h]] for h in orbit)
    counts = Counter(representative(g) for g in fresh)
    assert all(representative(r)==r for r in counts)
    # A substitute may be higher on positive rows and lower on negative rows.
    # The suffix uses only monotone gates and can keep all its other operands.
    positive = (1 << sum(y for _,y in rows)) - 1
    negative = ((1 << len(rows)) - 1) ^ positive
    assert all(y == (i < positive.bit_count()) for i,(_,y) in enumerate(rows))
    def better(x,y):
        return y & positive & ~x == 0 and x & negative & ~y == 0
    possible = {g:v for g,v in fresh.items() if not any(better(w,v) for w in old | {0})}
    # Check that even zero-dominated cases can use an existing physical wire.
    assert all(not better(0,v) or any(better(w,v) for w in old) for v in fresh.values())
    maximal = {g:v for g,v in possible.items()
               if not any(w != v and better(w,v) for w in possible.values())}
    assert all(any(better(w,v) for w in maximal.values()) for v in possible.values())
    survivors = sorted({representative(g) for g in maximal})
    print(f'{len(group)} permutations; {len(rows)} rows; {len(gates)} distinct-operand gates; '
          f'{len(gates)-len(fresh)} old-column gates; {len(first)} fresh columns; {len(counts)} orbits')
    print('uncovered by old wires or zero:',len(possible), 'maximal syntaxes:',len(maximal),
          'maximal orbits:',len(survivors))
    for r in survivors:
        print(*r)
    return survivors

if __name__ == '__main__':
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--case", type=int, default=5)
    classify(parser.parse_args().case)
