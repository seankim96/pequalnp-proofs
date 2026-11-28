"""Sixth ordinary AND after two fixed operations and a masked point-pair OR."""
import argparse
from concurrent.futures import ProcessPoolExecutor
from hashlib import sha256
from itertools import combinations
import json
from pathlib import Path

from order3_case35_h19_fifth_after_first_or import products as common_products
from order3_case35_h19_fifth_after_first_or import unexcluded as common_unexcluded
from order3_case35_h19_seventh_point_chain import SEVENTH
from order3_case35_h19_sixth_after_third import (
    DENSE, FAMILY, SEED, checked_parent, dependent_frontier, dominates, guard_unions,
    parent_pool, relevant, serialize_pools, supply_test, third_column, verify,
)


def verified(manifest):
    with ProcessPoolExecutor(max_workers=4) as workers:
        return list(workers.map(verify, relevant(manifest), chunksize=4))


def prefix_sources():
    b = parent_pool()
    return [*b, b[3] & b[15], b[12] | b[42]]


def raw_supplier(column):
    # Redirect directly to a physical non-guard wire, keeping every AND's
    # guard-read classification intact. No new mask is required.
    return next((i for i, w in enumerate(prefix_sources()) if i != 32 and dominates(w, column)), None)


def prove_common(checked):
    # Every independent pair made without the third OR is common to all
    # branches. Replay this whole set once, even if the third OR is redundant.
    n, needed = common_products()
    if common_unexcluded(needed, checked):
        raise ValueError("uncovered product in common independent OR pairs")
    return n * (n + 1) // 2


def census(checked, point, partner, mask=0):
    # Call prove_common with the same checked pool collection before this.
    b = parent_pool()
    old = prefix_sources()
    y = third_column(b, point, partner, mask)
    previous = set(guard_unions(old))
    choices = set(guard_unions([*old, y]))
    extra = sorted(choices - previous)
    g = b[32]
    supplied = supply_test(checked, partner, point, mask)
    independent = set()

    def test(left, right):
        p = left & right
        if not supplied(p) and not any(dominates(w, p) for w in (left, left & g, right, right & g)):
            independent.add(p)

    for i, left in enumerate(extra):
        for right in previous:
            test(left, right)
        for right in extra[:i + 1]:
            test(left, right)
    pairs, triples, dependent = dependent_frontier(checked, partner, point, mask)
    return len(choices), pairs, triples, independent, dependent


def masked_cases():
    b = parent_pool()
    for i, j in combinations(range(13), 2):
        for mask in (1, 2, 3):
            y = third_column(b, i, j, mask)
            yield i, j, mask, y, raw_supplier(y)


POINT_TWO = (
    ("case35-h19-point-two-48-00.json.gz", "b4669e5093efbda5e04a09cfbeca6a17b31128496e7d4e42fa911ebe5caa0956"),
    ("case35-h19-point-two-48-01.json.gz", "c8c84e84adc94fe81dfccd0da849a0a9307fb4032345e1bf0203825900403e55"),
)

PARENT = "c651957585b5559992718c0fb8d854ce7825d062cd17a1703774fd1d23bca884"
FRONTIER = "68d22bb3f42aa7b7d809b427298612c455616fcfcab7781a0617f06289808b7c"


def inherited(cache=None):
    if cache and cache.exists():
        data = cache.read_bytes()
        if sha256(data).hexdigest() != PARENT:
            raise ValueError("unexpected parent cache")
        return [(int(a, 16), int(d, 16), k) for a, d, k in json.loads(data)]
    pools = checked_parent(None) + verified((*SEED, *FAMILY, *DENSE, *SEVENTH))
    data = serialize_pools(pools)
    if sha256(data).hexdigest() != PARENT:
        raise ValueError("the inherited witness ranks did not replay")
    if cache:
        cache.write_bytes(data)
    return pools


def close_point_two(checked):
    import gzip
    path = Path(__file__).parent / "results" / "case35-h19-0-2-sixth-frontier-47.json.gz"
    data = gzip.decompress(path.read_bytes())
    if sha256(data).hexdigest() != FRONTIER:
        raise ValueError("unexpected parent (0,2) frontier")
    products = {int(p, 16) for values in json.loads(data).values() for p in values}
    supplied = supply_test(checked, 2, 0)
    remaining = {p for p in products if not supplied(p)}
    print("OR(0,2) independent/dependent product union:", len(products), "to", len(remaining))
    if remaining:
        raise ValueError("uncovered product in the (0,2) branch")


MASK_COVER = (
    ("case35-h19-mask-cover-48-00.json.gz", "5a41358724ebe1967dc552bfd16cd49cd12148f40dd883a24e1c7039ff7af827"),
    ("case35-h19-mask-cover-48-01.json.gz", "8fb912a141169a13b4c8ec779d9bef199f1da14d07871dc04e23bf1415ee4c27"),
    ("case35-h19-mask-cover-48-02.json.gz", "a3f09cd005d65e261825d1e920adfcb996a5ebff7a52df1250574b55b8c9bcda"),
    ("case35-h19-mask-cover-48-03.json.gz", "3906d9b90a468dcbc6b78a3e477075210e73752c965db890e4039ebefc9cf8cc"),
    ("case35-h19-mask-cover-48-04.json.gz", "8d3d564ff6a1a8a55296050d1d4f60d23048ae2e8539598f99ef74042d725e1d"),
    ("case35-h19-mask-cover-48-05.json.gz", "6cbc45e0951c3644479b746a4ce1d598dec65ddb30e414037e9ebc89ee057b9d"),
    ("case35-h19-mask-cover-48-06.json.gz", "19780d9c6544c7f528d03c9fb80d42a30c8f35caa5fc4dc17856b6e7889a5dfe"),
)


def classify_masked():
    b = parent_pool()
    direct = set()
    counts = [0, 0, 0, 0]
    for i, j, mask, column, source in masked_cases():
        if source is not None:
            counts[mask] += 1
        elif column == (b[i] | b[j]):
            direct.add((i, j))
        else:
            raise ValueError(f"unexpected nonraw masked column at {(i, j, mask)}")
    return counts[1:], direct


def broader_count(closed):
    b = parent_pool()
    old = prefix_sources()
    donors = [w for i, w in enumerate(old) if i != 32]
    known = [b[i] | b[j] for i, j in closed]
    columns = guard_unions(old)
    redundant = sum(any(dominates(w, y) for w in donors) for y in columns)
    covered = sum(any(dominates(w, y) for w in donors + known) for y in columns)
    return len(columns), redundant, covered



CENSUS_COLUMNS = (
    "left", "right", "fourth_or_values", "independent_pairs", "dependent_pairs",
    "independent_products_left", "dependent_triples_left", "dependent_products_left",
    "distinct_products_left", "earlier_donor", "status", "frontier_sha256",
)


def frontier_bytes(ip, dp):
    return json.dumps({"independent": [hex(p) for p in sorted(ip)],
                       "dependent": [hex(p) for p in sorted(dp)]},
                      separators=(",", ":")).encode()


def point_row(checked, i, j):
    n, pairs, triples, ip, dp = census(checked, i, j)
    b = parent_pool()
    donor = raw_supplier(b[i] | b[j])
    count = len(ip | dp)
    status = "covered" if count == 0 else "redirected" if donor is not None else "open"
    data = frontier_bytes(ip, dp)
    row = (i, j, n, n * (n + 1) // 2, pairs, len(ip), triples, len(dp), count,
           "" if donor is None else donor, status, sha256(data).hexdigest())
    return row, data


def write_census(path, rows):
    import csv
    with path.open("w", newline="") as stream:
        writer = csv.writer(stream, lineterminator="\n")
        writer.writerow(CENSUS_COLUMNS)
        writer.writerows(rows)


def replay(scope, cache, pair=None, output=None, table=None):
    checked = inherited(cache) + verified(POINT_TWO)
    close_point_two(checked)
    if scope == "point-two":
        return
    checked += verified(MASK_COVER)
    print("common independent pairs", prove_common(checked))
    counts, direct = classify_masked()
    print("masked layouts redirected to earlier wires", counts)
    if counts != [62, 70, 77] or len(direct) != 23:
        raise ValueError("masked layout classification changed")
    if pair:
        jobs = [tuple(pair)]
    elif scope == "all-points":
        jobs = list(combinations(range(13), 2))
    else:
        jobs = sorted(direct)
    closed = {tuple(sorted((5, i))) for i in range(13) if i != 5}
    rows = []
    for i, j in jobs:
        row, data = point_row(checked, i, j)
        rows.append(row)
        print(dict(zip(CENSUS_COLUMNS, row)), flush=True)
        if row[-2] != "open":
            closed.add((i, j))
        elif (i, j) in direct:
            raise ValueError("uncovered exceptional masked branch")
        if pair and output:
            output.write_bytes(data)
    if table:
        write_census(table, rows)
    if not pair:
        print("all third OR columns, earlier-wire donors, total covered", broader_count(closed))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--parent-cache", type=Path)
    parser.add_argument("--scope", choices=("point-two", "masked", "all-points"), default="masked")
    parser.add_argument("--pair", type=int, nargs=2, choices=range(13))
    parser.add_argument("--write-frontier", type=Path)
    parser.add_argument("--census-csv", type=Path)
    args = parser.parse_args()
    if args.pair and not args.pair[0] < args.pair[1]:
        parser.error("--pair requires two distinct point indices in increasing order")
    if args.write_frontier and not args.pair:
        parser.error("--write-frontier requires --pair")
    if args.pair and args.scope == "point-two":
        parser.error("--pair requires the masked or all-points scope")
    replay(args.scope, args.parent_cache, args.pair, args.write_frontier, args.census_csv)
