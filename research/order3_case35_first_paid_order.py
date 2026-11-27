"""At h=24 the first paid AND must follow two ORs after the thirteen-gate prefix."""
from itertools import combinations_with_replacement

from order3_case35_first_or import PREFIX13
from order3_case35_preload_density import ROOT, columns, evaluator, verify_sparse
from order3_case35_colored_trace import density


def verify(pool):
    ledger = density(pool, ROOT / "case35-or-trace-density.json")
    if ledger["required_ors"] < 24:
        raise ValueError("expected at least 24 ORs with eight paid ANDs")
    verify_sparse(pool)
    budget = evaluator(pool)
    dominators = [v for v in pool if budget(v, True)[1] > 19]
    guard = pool[32]
    # Any number of guard ANDs can only add one masked copy per value.
    initial = set(pool) | {v & guard for v in pool}
    pairs = list(combinations_with_replacement(sorted(initial), 2))
    no_or = {left & right for left, right in pairs}
    one_or = set()
    for left, right in pairs:
        u = left | right
        for w in initial:
            for v in (u & w, u & w & guard):
                # u already exists; its masked copy can be supplied by a guard AND.
                if v not in initial and v not in (u, u & guard):
                    one_or.add(v)
    positive = (1 << 52) - 1
    residual = {
        v for v in (no_or | one_or) - initial
        if (v & positive).bit_count() >= 3 and all(v & ~d for d in dominators)
    }
    exact = [budget(v, False)[1] for v in residual]
    if any(r <= 19 for r in exact):
        raise ValueError("an early paid output survived exact preloading")
    return len(initial), len(no_or), len(one_or), len(residual), min(exact, default=0)


def constrain(model, rows, min_reads, minimum=2):
    if model.size != 63 or min_reads != 24 or model.prefix[:13] != PREFIX13 or len(rows) != 520:
        raise ValueError("first-paid order needs h=24, size 63 and the thirteen-gate prefix")
    if minimum == 3:
        from order3_case35_two_or_preloads import verify as verify_two
        verify_two(columns(PREFIX13, rows))
    elif minimum == 2:
        verify(columns(PREFIX13, rows))
    else:
        raise ValueError("first-paid threshold must be two or three")
    count = 0
    for is_and, left, right in model.prefix[13:]:
        if count < minimum and is_and and 32 not in (left, right):
            model.clause()
            return
        count += not is_and
    if count >= minimum:
        return
    reached = [count >= n for n in range(minimum+1)]
    for gate in model.gates:
        model.clause(-gate.is_and, gate.left[32], gate.right[32], reached[minimum])
        # A threshold of n requires either n prior ORs, or n-1 and a new OR.
        updated = [True]
        for n in range(1, minimum+1):
            witness = model.fresh()
            model.clause(-witness, reached[n], reached[n-1])
            model.clause(-witness, reached[n], -gate.is_and)
            updated.append(witness)
        reached = updated


if __name__ == "__main__":
    from order3_prefix_search import test_rows
    print("guard closure, no-OR results, new one-OR results, residuals, min residual ORs:")
    print(*verify(columns(PREFIX13, test_rows())))
