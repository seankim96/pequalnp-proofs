"""Enumerate AND/OR/NOT tree formulas through size nine for L-meta-16116."""
import argparse
from itertools import product
from six_input_formula_bound import INPUTS, TABLE

MASK = (1 << 64) - 1

def layers_through(inputs, limit):
    layers = [set(inputs)]
    seen = set(inputs)
    for cost in range(1, limit+1):
        layer = {MASK ^ x for x in layers[-1]}
        for left in range((cost-1)//2+1):
            for x,y in product(layers[left], layers[cost-1-left]):
                layer.add(x & y)
                layer.add(x | y)
        layer.difference_update(seen)
        seen.update(layer)
        layers.append(layer)
    return layers

def binary_root(target, budget, layers, is_and):
    # Complement both child tables for an AND root, reducing the test to union.
    flip = MASK if is_and else 0
    wanted = target ^ flip
    allowed = [x ^ flip for x in layers[0] if ((x ^ flip) & wanted) == (x ^ flip)]
    if allowed:
        # One literal plus an arbitrarily unbalanced other child. Only this
        # split can need the extra layer, so stream it rather than storing it.
        def matches(raw):
            child = raw ^ flip
            return any((literal | child) == wanted for literal in allowed)
        for cost, layer in enumerate(layers[:budget]):
            if any(matches(v) for v in layer):
                return (0,cost)
        other = budget-1
        if other == len(layers):
            if any(matches(v ^ MASK) for v in layers[-1]):
                return (0,other)
            for a in range((other-1)//2+1):
                for x,y in product(layers[a],layers[other-1-a]):
                    if matches(x & y) or matches(x | y):
                        return (0,other)
    candidates = [[x ^ flip for x in layer if ((x ^ flip) & wanted) == (x ^ flip)]
                  for layer in layers]
    for left in range(1, budget//2+1):
        for right in range(left, budget-left):
            for x,y in product(candidates[left], candidates[right]):
                if x | y == wanted:
                    return (left,right)
    return None

def check(inputs, budget):
    layers = layers_through(inputs, budget - 2)
    print('new signed tables by cost:', [len(layer) for layer in layers], flush=True)
    if any(TABLE in layer or (MASK ^ TABLE) in layer for layer in layers):
        raise ValueError('a target or its complement already occurs in the generated layers')
    # After cancelling double negation the root has at most one leading NOT.
    for target,remaining,head in [(TABLE,budget,''), (MASK ^ TABLE,budget-1,'NOT-')]:
        for op in ('AND','OR'):
            print(head+op, 'root:', binary_root(target,remaining,layers,op=='AND'), flush=True)

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--shared-input-not', type=int, choices=range(6))
    parser.add_argument('--shared-pair', choices=['AND','OR'])
    parser.add_argument('--inputs', type=int, nargs=2, choices=range(6))
    args = parser.parse_args()
    if bool(args.shared_pair) != bool(args.inputs) or (args.shared_pair and args.shared_input_not is not None):
        parser.error('choose one shared gate and provide its operands')
    if args.shared_pair:
        a,b = (INPUTS[i] for i in args.inputs)
        check(INPUTS + [a & b if args.shared_pair == 'AND' else a | b], 8)
        raise SystemExit(0)
    if args.shared_input_not is None:
        check(INPUTS, 9)
    else:
        # Pay one gate for NOT(x_i). Make its output freely reusable at every
        # leaf, then account for the other eight gates as a tree formula.
        check(INPUTS + [MASK ^ INPUTS[args.shared_input_not]], 8)
