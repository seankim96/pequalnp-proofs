"""Search the remaining nine-gate budget for L-meta-16116 by counterexample refinement."""
import argparse
import subprocess
import tempfile
from pathlib import Path
from time import monotonic

from order3_prefix_search import Choices, Encoding

TABLE = (3941264000 << 32) + 3937060992

class NineGates(Encoding):
    def __init__(self, monotone_only):
        super().__init__((), 0)
        self.inversions = []
        for k in range(9):
            width = 6 + k
            gate = Choices(self.fresh(), [self.fresh() for _ in range(width)],
                           [self.fresh() for _ in range(width)])
            self.gates.append(gate)
            inv = self.fresh()
            self.inversions.append(inv)
            if monotone_only:
                self.clause(-inv)
            self.clause(*gate.left)
            self.clause(*gate.right)
            for i in range(width):
                for j in range(i):
                    self.clause(-gate.left[i], -gate.right[j])

    def add_test(self, x):
        wires = [bool(x & (1 << i)) for i in range(6)]
        for gate, inv in zip(self.gates, self.inversions):
            a = self.operand(gate.left, wires)
            b = self.operand(gate.right, wires)
            v = self.fresh()
            for literals in [(-gate.is_and,-v,a),(-gate.is_and,-v,b),(-gate.is_and,v,-a,-b),
                             (gate.is_and,v,-a),(gate.is_and,v,-b),(gate.is_and,-v,a,b)]:
                self.clause(inv, *literals)
            self.clause(-inv,-v,-a)
            self.clause(-inv,v,a)
            wires.append(v)
        self.clause(wires[-1] if TABLE >> x & 1 else -wires[-1])

    def decode(self, model):
        def selected(choices):
            return next(i for i,v in enumerate(choices) if v in model)
        return [('NOT' if inv in model else 'AND' if g.is_and in model else 'OR',
                 selected(g.left), selected(g.right)) for g,inv in zip(self.gates,self.inversions)]

def evaluate(gates, x):
    w = [x >> i & 1 for i in range(6)]
    for op,a,b in gates:
        w.append(1-w[a] if op == 'NOT' else w[a]&w[b] if op == 'AND' else w[a]|w[b])
    return w[-1]

def run(args):
    enc = NineGates(args.monotone)
    rows = {0,63,7,11,14,17,41,54}
    for x in sorted(rows):
        enc.add_test(x)
    deadline = monotonic() + args.seconds
    count = 0
    with tempfile.TemporaryDirectory() as directory:
        cnf = Path(directory) / 'nine.cnf'
        while monotonic() < deadline:
            enc.write(cnf)
            try:
                result = subprocess.run([args.solver, '-q', str(cnf)], capture_output=True,
                                        text=True, timeout=max(.001, deadline - monotonic()))
            except subprocess.TimeoutExpired:
                break
            if result.returncode == 20:
                return f'UNSAT on {len(rows)} encoded rows (solver verdict)'
            if result.returncode != 10:
                raise RuntimeError(result.stderr)
            model = {int(v) for line in result.stdout.splitlines() if line.startswith('v ')
                     for v in line.split()[1:] if int(v) > 0}
            gates = enc.decode(model)
            errors = [x for x in range(64) if evaluate(gates,x) != (TABLE >> x & 1)]
            count += 1
            if rows.intersection(errors):
                raise RuntimeError('decoded candidate disagrees with an encoded row')
            if not errors:
                return f'SAT checked on all 64 rows: {gates}'
            for x in errors[:4]:
                enc.add_test(x)
                rows.add(x)
    return f'UNKNOWN, {len(rows)} encoded rows, {count} decoded candidates'

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--seconds',type=int,default=180)
    parser.add_argument('--solver',default='cadical')
    parser.add_argument('--monotone',action='store_true')
    print(run(parser.parse_args()))
