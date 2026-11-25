"""Search finite AND/OR/NOT DAG budgets using the project's live-wire semantics.

The run starts with a subset of primary inputs. A gate consumes one or two
live wires, optionally retaining each operand for fanout. With t operations
remaining, at most t+1 wires can reach a single output. At equality all
remaining operations must be binary, discard both operands, and be monotone.
The search is numerical. A closed-state count alone is not a Lean proof.
"""
import argparse
from itertools import chain, combinations
from pathlib import Path
from time import monotonic

TABLE_16796 = (4277071584 << 32) + 4276808928


def search(n, target, cap, seconds):
    row_count = 1 << n
    mask = (1 << row_count) - 1
    if not 0 < target < mask:
        raise ValueError("the completeness argument assumes a nonconstant target")
    inputs = [sum(((r >> bit) & 1) << r for r in range(row_count)) for bit in range(n)]
    negative = sorted((r for r in range(row_count) if not (target >> r) & 1),
                      key=int.bit_count, reverse=True)
    closed = set()
    deadline = monotonic() + seconds

    def viable(t, wires):
        if len(wires) > t + 1 or (t == 0 and wires != (target,)):
            return False
        # Rows with the same wire signature must have the same target bit.
        classes = [mask]
        for wire in wires:
            classes = [part for group in classes for part in (group & wire, group & ~wire) if part]
        if any(group & target and group & ~target for group in classes):
            return False
        if len(wires) == t + 1:
            for row in negative:
                covered = 0
                for wire in wires:
                    if not (wire >> row) & 1:
                        covered |= wire
                if target & ~covered:
                    return False
        return True

    def children(t, wires):
        slack = t + 1 - len(wires)
        for i, a in enumerate(wires):
            rest = wires[:i] + wires[i + 1:]
            if slack >= 1:
                for result in (a, mask ^ a):
                    yield (result,) + rest
                    if slack >= 2:
                        yield (result, a) + rest
            for j in range(i + 1, len(wires)):
                b = wires[j]
                rest_pair = wires[:i] + wires[i + 1:j] + wires[j + 1:]
                for result in (a | b, a & b):
                    yield (result,) + rest_pair
                    if slack >= 1:
                        yield (result, a) + rest_pair
                        yield (result, b) + rest_pair
                    if slack >= 2:
                        yield (result, a, b) + rest_pair

    def reachable(t, wires):
        state = (t, wires)
        if state in closed or not viable(t, wires):
            return False
        if t == 0:
            return True
        if monotonic() >= deadline:
            raise TimeoutError
        if any(reachable(t - 1, tuple(sorted(ws))) for ws in children(t, wires)):
            return True
        closed.add(state)
        return False

    starts = chain.from_iterable(combinations(inputs, k) for k in range(n + 1))
    try:
        found = any(reachable(cap, tuple(sorted(ws))) for ws in starts)
    except TimeoutError:
        return 'UNKNOWN', closed
    return ('REACHABLE' if found else 'EXCLUDED'), closed


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--inputs', type=int, choices=range(1, 7), default=6)
    parser.add_argument('--table', type=lambda s: int(s, 0), default=TABLE_16796)
    parser.add_argument('--gates', type=int, required=True)
    parser.add_argument('--seconds', type=float, default=420)
    parser.add_argument('--save-closure', type=Path,
                        help='emit sorted states of a completed exclusion for independent replay')
    args = parser.parse_args()
    if args.gates < 0 or args.seconds <= 0:
        parser.error('the gate cap must be nonnegative and the time budget positive')
    begin = monotonic()
    verdict, closed = search(args.inputs, args.table, args.gates, args.seconds)
    print(f'{verdict} states={len(closed)} seconds={monotonic() - begin:.3f}')
    if args.save_closure and verdict == 'EXCLUDED':
        with args.save_closure.open('w') as output:
            for t, wires in sorted(closed):
                print(t, *wires, file=output)


if __name__ == '__main__':
    main()
