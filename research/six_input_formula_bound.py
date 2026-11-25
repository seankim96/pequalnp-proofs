"""Check the nine-gate tree-formula subcase of L-meta-16116 by truth-table DP.

A root costs one gate. If neither child is a literal, a formula of size
at most nine has both children of size at most seven. Constants, unary
copies, and repeated identical subformulas can be simplified in a tree.
"""
from itertools import product

TABLE = (3941264000 << 32) + 3937060992
INPUTS = [sum((x >> i & 1) << x for x in range(64)) for i in range(6)]

def layers_through(limit):
    layers = [set(INPUTS)]
    seen = set(INPUTS)
    for cost in range(1, limit + 1):
        values = set()
        for left in range((cost - 1) // 2 + 1):
            for a, b in product(layers[left], layers[cost - 1 - left]):
                values.add(a & b)
                values.add(a | b)
        values.difference_update(seen)
        layers.append(values)
        seen.update(values)
    return layers

def minimal_true_rows(table):
    return [x for x in range(64) if table >> x & 1 and
            all(not (table >> (x ^ (1 << i)) & 1) for i in range(6) if x >> i & 1)]

def dual(table):
    return sum((1 - (table >> (63-x) & 1)) << x for x in range(64))

def check_root(layers, dualize):
    # By De Morgan duality it suffices to check OR roots. Once a child's
    # table lies below the target, the union only needs to cover its minterms.
    target = dual(TABLE) if dualize else TABLE
    assert all((v & target) != v for v in INPUTS), 'a literal child needs separate testing'
    frontier = minimal_true_rows(target)
    signatures = []
    for layer in layers:
        signatures.append({sum((v >> x & 1) << i for i, x in enumerate(frontier))
                           for v in layer if v & target == v})
    full = (1 << len(frontier)) - 1
    return [(a, b) for a in range(1, 8) for b in range(a, 8) if a+b <= 8 and
            any((x | y) == full for x, y in product(signatures[a], signatures[b]))]

if __name__ == '__main__':
    layers = layers_through(7)
    print('new monotone tables at costs 0..7:', [len(layer) for layer in layers])
    for name, dualize in [('OR', False), ('AND', True)]:
        print(name, 'root: feasible child budgets at total size <= 9:', check_root(layers, dualize))
