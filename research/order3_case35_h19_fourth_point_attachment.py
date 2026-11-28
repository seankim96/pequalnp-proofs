"""Sixth ordinary AND after OR(4,12) and a fourth OR attaching another point."""
import argparse
import gzip
from hashlib import sha256
import json
from pathlib import Path

from order3_case35_h19_masked_point_pairs import (
    MASK_COVER, POINT_TWO, dominates, frontier_bytes, guard_unions, inherited,
    parent_pool, prefix_sources, supply_test, verified,
)

ATTACHMENT = (
    ("case35-h19-point-attachment-48-00.json.gz", "c4cd6d015a779cd447d05d67d6ec18a50f78b59f81f0704914e54b461f38ebd1"),
)


def extension(checked, i, j, t):
    """Enumerate all fifth ORs and all sixth ANDs, including masked operands."""
    base = parent_pool()
    g = base[32]
    third = base[i] | base[j]
    fourth = third | base[t]
    sources = [*prefix_sources(), third, fourth]
    old = set(sources)
    paid = supply_test(checked, j, i)
    fifths = guard_unions(sources)

    def older_donates(p):
        return paid(p) or dominates(fourth, p) or dominates(fourth & g, p)

    pre = {p for a in old for b in old for p in (a & b, a & b & g)
           if not older_donates(p)}
    hit = 0
    residual = set()
    for z in fifths:
        products = pre | {p for a in old | {z} for p in (a & z, a & z & g)
                          if not older_donates(p)}
        remaining = {p for p in products if not dominates(z, p) and not dominates(z & g, p)}
        hit += bool(remaining)
        residual.update(remaining)
    return len(fifths), hit, residual


def replay_attachments(checked, extra, output=None):
    i, j = 4, 12
    ranks = checked + extra
    source = Path(__file__).parent / "results" / "case35-h19-4-12-sixth-frontier-48.json.gz"
    data = gzip.decompress(source.read_bytes())
    if sha256(data).hexdigest() != "c6e70836cb4953711ae71307e8932250b738c5630373a8bc2b225d74128a4866":
        raise ValueError("unexpected original raw pair frontier")
    original = json.loads(data)
    supplied = supply_test(ranks, j, i)
    independent, dependent = (
        {int(s, 16) for s in original[key] if not supplied(int(s, 16))}
        for key in ("independent", "dependent")
    )
    frontier = frontier_bytes(independent, dependent)
    if sha256(frontier).hexdigest() != "987cfe1a9ecee8463edddabb8ce61caa77bd686b4abc1022d2449dff836726de":
        raise ValueError("updated OR(4,12) frontier differs from the checkpoint")
    if output:
        output.write_bytes(frontier)
    print("updated raw frontier", len(independent), len(dependent),
          len(independent | dependent), sha256(frontier).hexdigest(), flush=True)
    for t in range(13):
        if t in (i, j):
            continue
        values, hit, residual = extension(ranks, i, j, t)
        if hit or residual:
            raise ValueError(f"uncovered sixth AND after attaching point {t}")
        print("point, fifth OR columns, columns with residuals, distinct products",
              t, values, hit, len(residual), flush=True)
    return independent, dependent


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--parent-cache", type=Path)
    parser.add_argument("--write-frontier", type=Path)
    args = parser.parse_args()
    checked = inherited(args.parent_cache) + verified(POINT_TWO) + verified(MASK_COVER)
    replay_attachments(checked, verified(ATTACHMENT), args.write_frontier)
