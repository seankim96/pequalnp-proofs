"""Replay sixth ordinary AND exclusions for OR(4,12) and OR(9,12)."""
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


NINE_TWELVE = (
    ("case35-h19-third-nine-twelve-49-00.json.gz", "352266bb40a162c1c76bfb74baf3b5ace0e53f7e8472eaacfc976945a7a91099"),
)


def check(earlier, new, first=4):
    cases = {
        4: ("case35-h19-4-12-after-attachments-48.json.gz", "987cfe1a9ecee8463edddabb8ce61caa77bd686b4abc1022d2449dff836726de", 638),
        9: ("case35-h19-9-12-sixth-frontier-49.json.gz", "3d25a4894a01c2bc2191d00fbf5729da397ca0186118f3270377ee29971b4b57", 1073),
    }
    archive, digest, expected = cases[first]
    root = Path(__file__).parent / "results"
    data = gzip.decompress((root / archive).read_bytes())
    if sha256(data).hexdigest() != digest:
        raise ValueError("unexpected previous frontier")
    candidates = {int(p, 16) for batch in json.loads(data).values() for p in batch}
    supplied = supply_test(new, 12, first)
    survivors = {p for p in candidates if not supplied(p)}
    ranks = earlier + new
    common = prove_common(ranks)
    row, _ = point_row(ranks, first, 12)
    print("common pairs", common, "original", len(candidates), "remaining", len(survivors))
    print("fresh enumeration", row)
    if len(candidates) != expected or survivors or row[8] != 0:
        raise ValueError("the raw third OR still has a surviving product")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--parent-cache", type=Path)
    args = parser.parse_args()
    parent = inherited(args.parent_cache) + verified(POINT_TWO) + verified(MASK_COVER) + verified(ATTACHMENT)
    first = verified(CLOSURE)
    check(parent, first)
    check(parent + first, verified(NINE_TWELVE), 9)
