"""Generate L-meta-9800's monotone boundary rows in the desk's 40-wire order."""
import argparse
import hashlib
from itertools import combinations
import subprocess
import tempfile
from time import monotonic
from order3_prefix_search import Encoding
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / 'lean/PEqualNP/Research/PuncturedPlaneOrNetwork.lean'

def neighborhoods():
    line = next(line for line in SOURCE.read_text().splitlines() if line.startswith('def columns :'))
    cols = [[int(i) for i in group.split(',')] for group in re.findall(r'\{([0-9,]+)\}',line)]
    assert len(cols) == 19 and all(len(set(c)) == 5 and all(0 <= i < 21 for i in c) for c in cols)
    return cols

def boundary(cols):
    points = (1 << 21)-1
    masks = [sum(1 << i for i in c) for c in cols]
    positives = sorted((1 << i) | (1 << (21+j)) for j,c in enumerate(cols) for i in c)
    unions = [0] * (1 << len(cols))
    negatives = []
    for lines in range(len(unions)):
        if lines:
            bit = lines & -lines
            unions[lines] = unions[lines ^ bit] | masks[bit.bit_length()-1]
        left = points ^ unions[lines]
        # Every excluded line has a neighbor among the selected points.
        if all(lines & (1 << j) or neighbors & left for j,neighbors in enumerate(masks)):
            negatives.append(left | (lines << 21))
    # Independent construction using the distinct unions, without enumerating line subsets.
    closed = {0}
    for m in masks:
        closed |= {x | m for x in closed}
    from_unions = set()
    for u in closed:
        lines = sum(1 << j for j,m in enumerate(masks) if (m | u) == u)
        from_unions.add((points ^ u) | (lines << 21))
    assert len(negatives) == len(from_unions) and set(negatives) == from_unions
    return positives, sorted(negatives)

def column_formula(cols):
    gates = []
    def gate(op,a,b):
        gates.append((op,a,b))
        return 39+len(gates)
    terms = []
    for j,col in enumerate(cols):
        v = col[0]
        for i in col[1:]:
            v = gate('OR',v,i)
        terms.append(gate('AND',v,21+j))
    out = terms[0]
    for v in terms[1:]:
        out = gate('OR',out,v)
    return gates,out

def pair_seeds(pos, neg):
    # Seed one positive flag for each line and each point, plus maximal
    # independent sets covering every forbidden two-input conjunction.
    positive_rows = set(pos)
    pairs = [(i,j) for i,j in combinations(range(40),2)
             if ((1 << i) | (1 << j)) not in positive_rows]
    index = {pair:k for k,pair in enumerate(pairs)}
    masks = []
    for row in neg:
        active = [i for i in range(40) if row >> i & 1]
        masks.append(sum(1 << index[pair] for pair in combinations(active,2)))
    missing = (1 << len(pairs))-1
    selected = set()
    while missing:
        best = max(range(len(neg)),key=lambda i: (missing & masks[i]).bit_count())
        assert missing & masks[best]
        selected.add(len(pos)+best)
        missing &= ~masks[best]
    remaining = (1 << 40)-1
    while remaining:
        best = max(range(len(pos)),key=lambda i: (remaining & pos[i]).bit_count())
        assert remaining & pos[best]
        selected.add(best)
        remaining &= ~pos[best]
    return selected

def search(pos, neg, raw, seconds, solver, pair_cover=False):
    """CEGIS on 112 binary AND/OR gates with unrestricted earlier-wire fan-out."""
    rows = pos + neg
    wanted = (1 << len(pos)) - 1
    enc = Encoding((), 112, n_inputs=40)
    active = pair_seeds(pos,neg) if pair_cover else {0, len(pos)-1, len(pos), len(rows)-1}
    print(f"seeds: {sum(i < len(pos) for i in active)} positive, {sum(i >= len(pos) for i in active)} negative",flush=True)
    for i in sorted(active):
        enc.add_row(rows[i], i < len(pos))
    deadline = monotonic() + seconds
    count = 0
    with tempfile.TemporaryDirectory() as directory:
        path = Path(directory) / 'network.cnf'
        while monotonic() < deadline:
            enc.write(path)
            try:
                result = subprocess.run([solver, '-q', str(path)], capture_output=True, text=True,
                                        timeout=max(.001,deadline-monotonic()))
            except subprocess.TimeoutExpired:
                break
            if result.returncode == 20:
                return f'UNSAT on {len(active)} encoded rows (solver verdict)'
            if result.returncode != 10:
                raise RuntimeError(result.stderr)
            model = {int(v) for line in result.stdout.splitlines() if line.startswith('v ')
                     for v in line.split()[1:] if int(v) > 0}
            gates = enc.read_model(model)
            pool = raw.copy()
            for is_and,a,b in gates:
                pool.append(pool[a] & pool[b] if is_and else pool[a] | pool[b])
            wrong = pool[-1] ^ wanted
            count += 1
            assert not any(wrong >> i & 1 for i in active)
            if not wrong:
                return f'112-gate witness checked on the entire boundary: {gates}'
            for errors in (wrong & wanted, wrong & ~wanted):
                for _ in range(2):
                    if not errors:
                        break
                    bit = errors & -errors
                    i = bit.bit_length()-1
                    enc.add_row(rows[i], i < len(pos))
                    active.add(i)
                    errors ^= bit
    return f'UNKNOWN, {len(active)} encoded rows, {count} decoded candidates'

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--search-seconds", type=int, default=0)
    parser.add_argument("--pair-seeds", action="store_true")
    parser.add_argument("--solver", default="cadical")
    args = parser.parse_args()
    cols = neighborhoods()
    pos,neg = boundary(cols)
    gates,out = column_formula(cols)
    rows = pos+neg
    # Evaluate one bit per test through the entire circuit.
    wires = [sum((r >> i & 1) << j for j,r in enumerate(rows)) for i in range(40)]
    for op,a,b in gates:
        wires.append(wires[a] & wires[b] if op == 'AND' else wires[a] | wires[b])
    assert wires[out] == (1 << len(pos))-1
    digest = hashlib.sha256(b''.join(r.to_bytes(5,'little') for r in rows)).hexdigest()
    print(f'{len(pos)} positive; {len(neg)} negative; {len(gates)} gates pass; row SHA-256 {digest}')
    if args.search_seconds > 0:
        print(search(pos, neg, wires[:40], args.search_seconds, args.solver, args.pair_seeds))
