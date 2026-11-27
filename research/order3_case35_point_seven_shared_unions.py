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


@lru_cache(maxsize=None)
def stage(base, width):
    tests = []
    for j,flags in bank(width):
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
    closed = proved(base)
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


if __name__ == "__main__":
    from order3_prefix_search import test_rows
    base = tuple(columns(PREFIX13+POINT7,test_rows()))
    closed = proved(base)
    print("closed first ORs",len(closed),"remaining",len(first_survivors(base)-closed))
    frontier = continuation(base,closed)
    print("after OR(2,3), surviving second raw unions and third-OR counts",
          [(a,b,frontier[base[a]|base[b]]) for a,b in pairs(range(len(base))) if (base[a]|base[b]) in frontier])
