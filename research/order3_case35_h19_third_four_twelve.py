"""Replay the sixth ordinary AND exclusion for the raw third gate OR(4,12)."""
import argparse
import gzip
import json
from hashlib import sha256
from pathlib import Path

from order3_case35_h19_fourth_point_attachment import ATTACHMENT
from order3_case35_h19_masked_point_pairs import (
    MASK_COVER, POINT_TWO, inherited, point_row, prove_common, supply_test, verified,
)

CLOSURE = (
    ("case35-h19-third-four-twelve-49-00.json.gz", "9315a97615b3e2278fccd503ff3a4bc06fb451e6b314be411fdb15e3653de492"),
)


def check(earlier, new):
    root = Path(__file__).parent / "results"
    data = gzip.decompress((root / "case35-h19-4-12-after-attachments-48.json.gz").read_bytes())
    if sha256(data).hexdigest() != "987cfe1a9ecee8463edddabb8ce61caa77bd686b4abc1022d2449dff836726de":
        raise ValueError("unexpected previous frontier")
    candidates = {int(p, 16) for batch in json.loads(data).values() for p in batch}
    supplied = supply_test(new, 12, 4)
    survivors = {p for p in candidates if not supplied(p)}
    ranks = earlier + new
    common = prove_common(ranks)
    row, _ = point_row(ranks, 4, 12)
    print("common pairs", common, "original", len(candidates), "remaining", len(survivors))
    print("fresh enumeration", row)
    if len(candidates) != 638 or survivors or row[8] != 0:
        raise ValueError("the raw third OR still has a surviving product")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--parent-cache", type=Path)
    args = parser.parse_args()
    parent = inherited(args.parent_cache) + verified(POINT_TWO) + verified(MASK_COVER) + verified(ATTACHMENT)
    check(parent, verified(CLOSURE))
