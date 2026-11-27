"""Replay first-OR exclusions obtained by sharing pivot certificates across prefixes."""
from functools import lru_cache
import json

from order3_case35_or_packing_search import search
from order3_case35_star_preloads import eight_paid_floor
from order3_case35_point_seven_or_order import (ROOT, PREFIX13, POINT7, after_one,
    columns, dominates, excluded_unions, first_survivors, guard_unions,
    old_replacements, pairs, verify_union_data)


@lru_cache(maxsize=2)
def bank(width):
    files = []
    for other in (2,3,4):
        if width == 18:
            files.append(f"case35-point-seven-second-or-0-{other}.json")
        elif width == 17:
            files.extend(f"case35-point-seven-third-or-0-{other}-{suffix}.json"
                         for suffix in ("7-13","13-42"))
        else:
            raise ValueError("unsupported packing width")
    return sorted({(j,tuple(flags)) for f in files
                   for j,flags in json.loads((ROOT / f).read_text())["tests"]})


@lru_cache(maxsize=1)
def extended_third_bank():
    data = json.loads((ROOT / "case35-point-seven-cross-third-bank.json").read_text())
    return sorted(set(bank(17)) | {(j,tuple(flags)) for j,flags in data})


@lru_cache(maxsize=None)
def stage(base, width, *, extended=False):
    tests = []
    for j,flags in (extended_third_bank() if extended else bank(width)):
        mask = sum(1 << i for i in flags)
        if all(x >> (52+j) & 1 or (x & mask).bit_count() <= 1 for x in base[43:]):
            tests.append((j,flags))
    proposal = search(base, tests)
    # Recheck the selected row indices, starting columns and every conjunction
    # used for the pivot, independently of how search chose its witnesses.
    return frozenset(guard_unions(base)) - verify_union_data(base,proposal,width)


@lru_cache(maxsize=1)
def cross_floors(base):
    certs = json.loads((ROOT / "case35-point-seven-cross-unions.json").read_text())
    result = {}
    for a,b,c,d,rows,off in certs:
        if any(not 0 <= i < len(base) for i in (a,b,c,d)):
            raise ValueError("invalid cross-product operand")
        value = (base[a] | base[b]) & (base[c] | base[d])
        if value in result:
            raise ValueError("duplicate cross-product preload")
        result[value] = eight_paid_floor(list(base),value,[j for j,_ in rows],off,
                                         dict(rows),unique_paid_outputs=True)
    return result


def entry(base, x):
    candidates = first_survivors(base)
    if x not in candidates:
        raise ValueError("unexpected first OR")
    after_one(base,x)
    bad = excluded_unions(base,"case35-point-seven-first-or.json",19)
    extended = base + (x,)
    # The lower bound at the original 17-gate state excludes each bad OR
    # anywhere. A duplicate of an available wire can instead be deleted.
    seconds = stage(extended,18) - bad - set(extended)
    for y in seconds:
        if y not in candidates:
            return None
        after_one(base,y)
        cross = x & y
        if not any(dominates(v,cross) for v in old_replacements(base)) and not any(
                dominates(v & x,cross) or dominates(v & y,cross) for v in base):
            if cross_floors(base).get(cross,0) < 20:
                return None
        third_inputs = extended + (y,)
        if stage(third_inputs,17) - bad - set(third_inputs):
            return None
    return len(seconds)


@lru_cache(maxsize=1)
def proved(base):
    rows = json.loads((ROOT / "case35-point-seven-shared-first-pairs.json").read_text())
    closed = set()
    for a,b in rows:
        if not 0 <= a <= b < len(base):
            raise ValueError("invalid first-OR operand")
        x = base[a] | base[b]
        if x in closed or entry(base,x) is None:
            raise ValueError("first OR does not replay")
        closed.add(x)
    return frozenset(closed)


def constrain(model, rows, h):
    if h < 20 or model.size != 63 or model.prefix[:17] != PREFIX13 + POINT7 or len(rows) != 520:
        return
    base = tuple(columns(model.prefix[:17],rows))
    closed = proved(base) | {exclude_two_three(base)} | cross_bank_exclusions(base)
    pool = columns(model.prefix,rows)
    for i,(op,_,_) in enumerate(model.prefix[17:],43):
        if not op and pool[i] in closed:
            model.clause()
            return
    excluded_pairs = [(a,b) for a,b in pairs(range(len(base))) if base[a] | base[b] in closed]
    for gate in model.gates:
        for a,b in excluded_pairs:
            model.clause(gate.is_and,-gate.left[a],-gate.right[b])
            if a != b:
                model.clause(gate.is_and,-gate.left[b],-gate.right[a])


def continuation(base, closed):
    """Return possible second unions and their unresolved third-OR counts for OR(2,3)."""
    x = base[2] | base[3]
    after_one(base,x)
    ext = base + (x,)
    bad = excluded_unions(base,"case35-point-seven-first-or.json",19) | closed
    out = {}
    for y in stage(ext,18) - bad - set(ext):
        initial = ext+(y,)
        remaining = stage(initial,17) - bad - set(initial)
        if y in first_survivors(base):
            after_one(base,y)
            if not remaining and any(dominates(x & v,x & y) or dominates(y & v,x & y) for v in base):
                continue
        out[y] = len(remaining)
    return out


@lru_cache(maxsize=1)
def exclude_two_three(base):
    """Replay the last second union, its paid cross, and its full third-OR domain."""
    x = base[2] | base[3]
    y = base[13] | base[15]
    if continuation(base, proved(base)) != {y: 17}:
        raise ValueError("unexpected frontier after OR(2,3)")
    after_one(base, y)

    record = json.loads((ROOT / "case35-point-seven-2-3-cross.json").read_text())
    a,b,c,d,mode,tests,off = record
    if (a,b,c,d,mode) != (2,3,13,15,0):
        raise ValueError("unexpected prepaid intersection")
    # Delete only the paid AND. Its output is supplied from the start.
    # Both ORs still count against the original 19-OR budget.
    floor = eight_paid_floor(list(base), x & y, [j for j,_ in tests], off,
                             dict(tests), unique_paid_outputs=True)
    if floor < 20:
        raise ValueError("the prepaid cross still fits the OR budget")
    extended = base + (x,y)
    forbidden = excluded_unions(extended, "case35-point-seven-2-3-third-or.json", 17)
    if forbidden != set(guard_unions(extended)):
        raise ValueError("uncovered third OR before the first paid AND")
    return x


@lru_cache(maxsize=1)
def supplemental_crosses(base):
    data = json.loads((ROOT / "case35-point-seven-two-crosses.json").read_text())
    tests,off = data["packings"],data["guard_off"]
    excluded = set()
    for a,b,c,d in data["unions"]:
        if any(i < 0 or i >= len(base) for i in (a,b,c,d)):
            raise ValueError("invalid cross operand")
        value = (base[a] | base[b]) & (base[c] | base[d])
        floor = eight_paid_floor(list(base), value, [j for j,_ in tests], off,
                                 dict(tests), unique_paid_outputs=True)
        if floor < 20:
            raise ValueError("the supplied cross fits the OR budget")
        excluded.add(value)
    return frozenset(excluded)


@lru_cache(maxsize=1)
def cross_bank_exclusions(base):
    previous = proved(base) | {exclude_two_three(base)}
    unavailable = excluded_unions(base, "case35-point-seven-first-or.json", 19) | previous
    pairs_to_check = json.loads((ROOT / "case35-point-seven-cross-first-pairs.json").read_text())
    newly_closed = set()
    for a,b,count in pairs_to_check:
        if not 0 <= a <= b < len(base):
            raise ValueError("invalid first pair")
        x = base[a] | base[b]
        if x not in first_survivors(base) or x in newly_closed or x in previous:
            raise ValueError("unexpected first union")
        after_one(base, x)
        ext = base + (x,)
        seconds = stage(ext,18) - unavailable - set(ext)
        if len(seconds) != count:
            raise ValueError("second-OR count differs from ledger")
        for y in seconds:
            if y not in first_survivors(base):
                raise ValueError("second union needs a new paid-pair census")
            after_one(base,y)
            if not any(dominates(x & v,x & y) or dominates(y & v,x & y) for v in base):
                if x & y not in supplemental_crosses(base):
                    raise ValueError("cross product needs a paid preload")
            inputs = ext + (y,)
            if stage(inputs,17,extended=True) - unavailable - set(inputs):
                raise ValueError("third OR remains possible")
        newly_closed.add(x)
    return frozenset(newly_closed)


if __name__ == "__main__":
    from order3_prefix_search import test_rows
    base = tuple(columns(PREFIX13+POINT7,test_rows()))
    closed = proved(base)
    print("closed first ORs",len(closed),"remaining",len(first_survivors(base)-closed))
    frontier = continuation(base,closed)
    print("after OR(2,3), surviving second raw unions and third-OR counts",
          [(a,b,frontier[base[a]|base[b]]) for a,b in pairs(range(len(base))) if (base[a]|base[b]) in frontier])
    extra = exclude_two_three(base)
    print("after the cross and third-OR replay, remaining first ORs",len(first_survivors(base)-closed-{extra}))
    more = cross_bank_exclusions(base)
    print("other exclusions",len(more),"remaining first ORs",len(first_survivors(base)-closed-{extra}-more))
