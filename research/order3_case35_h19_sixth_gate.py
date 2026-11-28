"""Sixth non-guard operation after A, X, OR(5,10), OR(18,Y) in case 35."""
from concurrent.futures import ProcessPoolExecutor
from hashlib import sha256

from order3_case35_h19_fifth_after_first_or import DEPENDENT, INDEPENDENT
from order3_case35_h19_fifth_gate import (
    FIFTH, FOURTH_LEDGER, LEDGERS, ROOT, dominates, guard_unions, parent_pool, records, verify,
)


def needed():
    b = parent_pool()
    g = b[32]
    a, x = b[3] & b[15], b[12] | b[42]
    y = b[5] | b[10]
    z = b[18] | y
    prior = [*b,a,x,y]
    old = {*prior,z}
    free = old | {v & g for v in old}
    independent = set(guard_unions(prior))
    dependent = {v | u for v in (z,z & g) for u in free}
    pairs = set()
    for w in independent | dependent:
        products = {w & z} if w in independent else set()
        if w in dependent:
            products.update(w & v for v in old | {w})
        for p in products:
            if not any(dominates(s,p) for s in free | {w,w & g}):
                pairs.add((w,p))
    return (len(independent),len(dependent),len(independent | dependent)), pairs


def supplied(products, checked):
    b = parent_pool()
    a, g = b[3] & b[15], b[32]
    wires = {w for c,d,k in checked if k >= 20 and
             any(dominates(u,a) for u in (c,d,c & g,d & g))
             for w in (c,d,c & g,d & g)}
    if not wires:
        raise ValueError("no verified preload for A")
    return {p for p in products if any(dominates(w,p) for w in wires)}


SIXTH = (('case35-h19-sixth-46-00.json.gz', '77541a92aecd558a21f059066bace5ff600d65713910133cd052259adb55171d'),)
INDEX = {
    'case35-h19-dependent-46-00.json.gz': [31, 34, 36, 41, 46, 49, 52, 60, 65, 71, 81, 92, 94, 110],
    'case35-h19-independent-46-00.json.gz': [2, 57, 268, 285, 295, 457],
    'case35-h19-fifth-46-00.json.gz': [0, 1, 7, 8, 9, 11, 12, 22, 31, 32, 34, 37, 38, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 56, 58, 59, 60, 61, 62, 64, 65, 66, 67, 68, 69, 70, 71, 72],
    'case35-h19-dependent-46-01.json.gz': [287, 292, 295, 300],
    'case35-h19-guard-envelope-00.json.gz': [27, 29, 57, 66, 100, 111, 123, 151, 440],
    'case35-h19-independent-46-01.json.gz': [16, 21, 103, 129, 137, 307],
    'case35-h19-independent-46-02.json.gz': [33, 68, 156, 247, 248, 280, 332, 434, 437, 438, 476],
    'case35-h19-independent-46-04.json.gz': [70, 310, 456, 458, 472],
    'case35-h19-guard-fourth.json.gz': [45],
    'case35-h19-independent-46-03.json.gz': [51, 56],
    'case35-h19-independent-46-05.json.gz': [221, 226, 251, 288, 381, 418, 421],
    'case35-h19-independent-46-06.json.gz': [93],
    'case35-h19-sixth-46-00.json.gz': [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12],
}

def replay():
    shape, pairs = needed()
    selected = []
    for name,digest in (*LEDGERS,FOURTH_LEDGER,*FIFTH,*INDEPENDENT,*DEPENDENT,*SIXTH):
        if name not in INDEX:
            continue
        path = ROOT / name
        if sha256(path.read_bytes()).hexdigest() != digest:
            raise ValueError(f"unexpected ledger {name}")
        wanted = set(INDEX[name])
        selected.extend(r for i,r in enumerate(records(path)) if i in wanted)
    with ProcessPoolExecutor(max_workers=4) as pool:
        checked = list(pool.map(verify, selected, chunksize=3))
    hit = supplied({p for _,p in pairs},checked)
    pending = {(w,p) for w,p in pairs if p not in hit}
    print("independent, dependent, distinct fifth ORs",shape)
    print("checked witness pairs",len(checked),"sixth AND residual",len(pending))
    if pending:
        raise ValueError("the fixed sixth-gate exclusion failed")


if __name__ == "__main__":
    replay()
