"""Source-audited rooted BB(6) holdout-list comparison (R001).

Read-only analysis. A roster deletion is not evidence of a machine decision.
The October 24 URL is recorded in the Wiki's 2026-10-25 revision 9543,
mirrored by Yeyito777/bbchallenge-corpus (pageid 36).
"""
from hashlib import sha256
from pathlib import Path
import re
from urllib.request import Request, urlopen

OCT16 = Path("resources/BB6_holdouts_663_2026-10-16.txt")
OCT24_URL = "https://wiki.bbchallenge.org/w/images/4/4c/BB6_holdouts_623.txt"
TRANSITION = re.compile(r"(?:[01][LR][A-F]|---)\Z")


def parse_roots(raw: bytes, expected: int) -> list[str]:
    roots = [line.strip() for line in raw.decode("utf-8-sig").splitlines() if line.strip()]
    assert len(roots) == expected, f"expected {expected} lines, got {len(roots)}"
    assert len(set(roots)) == len(roots), "duplicate rooted transition string"
    for number, root in enumerate(roots, 1):
        states = root.split("_")
        assert len(states) == 6, (number, root)
        assert all(len(state) == 6 and TRANSITION.fullmatch(state[:3])
                   and TRANSITION.fullmatch(state[3:]) for state in states), (number, root)
    return roots


def main() -> None:
    old_raw = OCT16.read_bytes()
    with urlopen(Request(OCT24_URL, headers={"User-Agent": "BB6-research-repro/1.0"}),
                 timeout=35) as response:
        assert response.status == 200
        new_raw = response.read()
    old = parse_roots(old_raw, 663)
    new = parse_roots(new_raw, 623)
    old_set, new_set = set(old), set(new)

    print(f"October 16, 2026: {len(old)} rooted entries, SHA256={sha256(old_raw).hexdigest()}")
    print(f"October 24, 2026: {len(new)} rooted entries, SHA256={sha256(new_raw).hexdigest()}")
    print(f"Source: {OCT24_URL}")
    print(f"Identical rooted entries: {len(old_set & new_set)}")
    print(f"Removed rooted entries: {len(old_set - new_set)}")
    print(f"Added rooted entries: {len(new_set - old_set)}")
    print("BEGIN REMOVED rooted entries (Oct16 1-based line number)")
    for i, machine in enumerate(old, 1):
        if machine not in new_set:
            print(f"{i}\t{machine}")
    print("END REMOVED")
    print("BEGIN ADDED rooted entries (Oct24 1-based line number)")
    for i, machine in enumerate(new, 1):
        if machine not in old_set:
            print(f"{i}\t{machine}")
    print("END ADDED")


if __name__ == "__main__":
    main()
