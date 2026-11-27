"""OR order at the h=20 boundary after case 35's completed point-seven star."""
from collections import Counter
from functools import lru_cache
from itertools import combinations_with_replacement
import json

from order3_case35_first_or import packing
from order3_case35_star_packings import ROOT, PREFIX13, POINT7, columns
from order3_case35_star_preloads import dominates, eight_paid_floor, verify_all_pairs


def pairs(items):
    return combinations_with_replacement(items, 2)


def guard_unions(base):
    operands = set(base) | {v & base[32] for v in base}
    return sorted({a | b for a,b in pairs(operands)})


@lru_cache(maxsize=2)
def excluded_unions(base, filename, width):
    data = json.loads((ROOT / filename).read_text())
    values = guard_unions(base)
    tests = []
    for j,flags in data["tests"]:
        if len(flags) != width:
            raise ValueError("unexpected packing width")
        tests.append(packing(base, (j,flags)))
    excluded = set()
    for index, pivot, ids in data["witnesses"]:
        if not 0 <= index < len(values) or not 0 <= pivot < 52 or not ids:
            raise ValueError("invalid OR witness")
        value = values[index]
        if value in excluded:
            raise ValueError("duplicate OR witness")
        possible = set()
        for source in (*base, value):
            if source >> pivot & 1:
                possible |= {source} | {x & source for x in possible}
        for key in ids:
            if not 0 <= key < len(tests):
                raise ValueError("invalid packing index")
            j,mask = tests[key]
            if not value >> (52+j) & 1 and (value & mask).bit_count() > 1:
                raise ValueError("preloaded OR invalidates a packing")
            possible = {x for x in possible if not x >> (52+j) & 1 and x & mask}
        if possible:
            raise ValueError("an AND-only pivot leaf is live on every chosen packing")
        excluded.add(value)
    return frozenset(excluded)


@lru_cache(maxsize=1)
def first_survivors(base):
    bad = excluded_unions(base,"case35-point-seven-first-or.json",19)
    return frozenset(guard_unions(base)) - bad


@lru_cache(maxsize=1)
def preload_data(base):
    data = json.loads((ROOT / "case35-point-seven-one-or-preloads.json").read_text())
    families = {}
    for a,b,i,rows,off in data["families"]:
        if any(not 0 <= n < len(base) for n in (a,b,i)):
            raise ValueError("invalid physical operand")
        v = (base[a] | base[b]) & base[i]
        if v in families:
            raise ValueError("duplicate AND preload")
        families[v] = rows,off
    refined = {}
    for a,b,i,mode,rows,off in data["refined"]:
        if any(not 0 <= n < len(base) for n in (a,b,i)) or mode not in (0,1):
            raise ValueError("invalid refined preload")
        u = base[a] | base[b]
        key = (u if mode else None, u & base[i])
        refined[key] = rows,off
    packings = dict(json.loads((ROOT / "case35-point-seven-preloads.json").read_text())["packings"])
    return packings, families, refined


@lru_cache(maxsize=None)
def one_preload(base, union, value):
    packings,families,refined = preload_data(base)
    if union is None:
        rows,off = families[value]
        bound = eight_paid_floor(list(base),value,rows,off,packings,unique_paid_outputs=True)
        if bound >= 20 or (None,value) not in refined:
            return bound
    if (union,value) not in refined:
        return 0
    extra = list(base) if union is None else [*base,union]
    tests,off = refined[union,value]
    return eight_paid_floor(extra,value,[j for j,_ in tests],off,dict(tests),unique_paid_outputs=True)


@lru_cache(maxsize=1)
def old_replacements(base):
    # The prior nine-to-eight deletion checks all initial paid pairs. A masked
    # pair can be recovered by one extra guard AND at zero paid/OR cost.
    verify_all_pairs(base)
    products = {a & b for a,b in pairs(base)}
    return frozenset({0,*base,*products,*(x & base[32] for x in products)})


@lru_cache(maxsize=None)
def after_one(base, union):
    fixed = old_replacements(base)
    stats = Counter()
    # Before another OR or paid AND, wires are old sources, the one new
    # union, or guard-masked copies of either. Two copies of the same union
    # give a copy or a masked copy, already available without a paid gate.
    for x in base:
        value = x & union
        if any(dominates(u,value) for u in (*fixed,union,union & base[32])):
            stats["dominance"] += 1
        elif one_preload(base,None,value) >= 20:
            stats["single prepaid AND"] += 1
        elif one_preload(base,union,value) >= 19:
            # Remove both the earlier OR and the paid gate. Their values
            # are supplied to the remaining circuit as additional inputs.
            stats["prepaid OR and AND"] += 1
        else:
            raise ValueError("a paid gate after one OR has not been excluded")
    return stats


def second_exclusions(base, other):
    union = base[0] | base[other]
    return excluded_unions(base+(union,), f"case35-point-seven-second-or-0-{other}.json",18)


@lru_cache(maxsize=2)
def exclude_first(base, other):
    """Move the candidate OR to the start and exclude every third-OR choice."""
    x = base[0] | base[other]
    if x not in first_survivors(base):
        raise ValueError("unexpected first-OR domain")
    after_one(base, x)
    extended = base + (x,)
    remaining = set(guard_unions(extended)) - second_exclusions(base, other)
    for i, filename in [(7, f"case35-point-seven-third-or-0-{other}-7-13.json"),
                        (42, f"case35-point-seven-third-or-0-{other}-13-42.json")]:
        y = base[13] | base[i]
        if y not in remaining or y not in first_survivors(base):
            raise ValueError("unexpected second OR")
        remaining.remove(y)
        # Each possible paid operand strips to an initial wire, x, or y.
        # Initial-initial pairs are covered by the old ledger. For x-initial
        # or y-initial the one-OR deletion works even when the other OR is
        # present: it uses only the global 19-OR budget and the named union.
        after_one(base, y)
        # For x-y, the already excluded x & base[13] dominates x & y.
        if not dominates(x & base[13], x & y):
            raise ValueError("cross pair has no replacement")
        all_inputs = extended + (y,)
        forbidden = excluded_unions(all_inputs, filename, 17)
        if set(guard_unions(all_inputs)) != forbidden:
            raise ValueError("a third OR can still precede the first paid gate")
    if remaining:
        raise ValueError("uncovered second OR")
    return x


def constrain(model, rows, h):
    if h < 20 or model.size != 63 or model.prefix[:17] != PREFIX13 + POINT7 or len(rows) != 520:
        return
    base = tuple(columns(model.prefix[:17],rows))
    pool = columns(model.prefix,rows)
    forbidden = [exclude_first(base, other) for other in (2,3)]
    first = None
    seen_ors = 0
    bad = excluded_unions(base,"case35-point-seven-first-or.json",19)
    # If any OR equals the excluded column on the 520 rows, replace it by
    # OR(0,3) at slot 18 and renumber its dependents. Size, gate kinds and
    # physical reads of wire 32 are preserved. The same monotone substitution
    # works when the new column dominates the old one on the target rows.
    for i,(op,a,b) in enumerate(model.prefix[17:],43):
        if not op:
            if pool[i] in bad or any(dominates(x,pool[i]) for x in forbidden):
                model.clause()
                return
            if first is None:
                first = pool[i]
                if first not in first_survivors(base):
                    raise ValueError("first OR outside the guard-copy domain")
            seen_ors += 1
        elif 32 not in (a,b) and seen_ors < 2:
            if first is not None:
                after_one(base,first)
            else:
                old_replacements(base)
            model.clause()
            return
    if first is None:
        for u in first_survivors(base):
            after_one(base,u)
    else:
        after_one(base,first)
    # Require two earlier ORs whenever a future paid AND is selected. The
    # auxiliary variables can be true only if the required earlier ORs exist.
    one = seen_ors >= 1
    two = seen_ors >= 2
    for gate in model.gates:
        model.clause(-gate.is_and,gate.left[32],gate.right[32],two)
        next_one, next_two = model.fresh(), model.fresh()
        model.clause(-next_one,one,-gate.is_and)
        model.clause(-next_two,two,one)
        model.clause(-next_two,two,-gate.is_and)
        one,two = next_one,next_two
        # Both fixed physical operands will be available at every suffix gate.
        for other in (2,3):
            model.clause(gate.is_and,-gate.left[0],-gate.right[other])
            model.clause(gate.is_and,-gate.left[other],-gate.right[0])
    if model.gates:
        # Known operand values remain valid at all later times. Apply the
        # value filters to the next gate, including a first or second OR.
        gate = model.gates[0]
        for a,b in pairs(range(len(pool))):
            if (pool[a] | pool[b]) in bad or any(dominates(x,pool[a] | pool[b]) for x in forbidden):
                model.clause(gate.is_and,-gate.left[a],-gate.right[b])
                if a != b:
                    model.clause(gate.is_and,-gate.left[b],-gate.right[a])


if __name__ == "__main__":
    from order3_prefix_search import test_rows
    base = tuple(columns(PREFIX13+POINT7,test_rows()))
    survivors = first_survivors(base)
    stats = Counter()
    for union in survivors:
        stats.update(after_one(base,union))
    print("first OR values",len(guard_unions(base)),"remaining",len(survivors))
    print("one-OR paid attempts (43 sources per value)",dict(stats))
    for other in (2,3):
        extended = base + (base[0] | base[other],)
        second = set(guard_unions(extended)) - second_exclusions(base,other)
        print("second OR after OR(0,%d)" % other, len(guard_unions(extended)), "remaining",len(second))
        exclude_first(base,other)
        print("third OR value domains", [len(guard_unions(extended + (base[13] | base[i],))) for i in (7,42)])
        print("remaining second OR pairs",[(a,b) for a,b in pairs(range(len(extended))) if (extended[a]|extended[b]) in second])
