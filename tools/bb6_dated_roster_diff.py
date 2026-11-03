"""Source-audited rooted BB(6) holdout-list comparison (R001).

Read-only analysis. A roster deletion is not evidence of a machine decision.
The October 24 URL is recorded in the Wiki's 2026-10-25 revision 9543,
mirrored by Yeyito777/bbchallenge-corpus (pageid 36).
"""
from hashlib import sha256
from urllib.error import URLError
from pathlib import Path
import re
from urllib.request import Request, urlopen

OCT16 = Path("resources/BB6_holdouts_663_2026-10-16.txt")
OCT24_URL = "https://wiki.bbchallenge.org/w/images/4/4c/BB6_holdouts_623.txt"
OCT30_URL = "https://wiki.bbchallenge.org/w/images/5/5e/BB6_holdouts_608.txt"
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


    with urlopen(Request(OCT30_URL, headers={"User-Agent": "BB6-research-repro/1.0"}),
                 timeout=35) as response:
        assert response.status == 200
        latest_raw = response.read()
    latest = parse_roots(latest_raw, 608)
    latest_set = set(latest)
    print(f"October 30, 2026: {len(latest)} rooted entries, SHA256={sha256(latest_raw).hexdigest()}")
    print(f"Source: {OCT30_URL}")
    print(f"Oct24 retained: {len(new_set & latest_set)}")
    print(f"Oct24 removed: {len(new_set - latest_set)}")
    print(f"Oct30 added against Oct24: {len(latest_set - new_set)}")
    print(f"Oct16 retained in Oct30: {len(old_set & latest_set)}")
    print(f"Oct16 removed by Oct30: {len(old_set - latest_set)}")
    print(f"Oct30 new against Oct16: {len(latest_set - old_set)}")
    print("BEGIN OCT24 TO OCT30 REMOVED rooted entries (Oct24 1-based line number)")
    for i, machine in enumerate(new, 1):
        if machine not in latest_set:
            print(i, machine, sep=chr(9))
    print("END OCT24 TO OCT30 REMOVED")
    print("BEGIN OCT24 TO OCT30 ADDED rooted entries (Oct30 1-based line number)")
    for i, machine in enumerate(latest, 1):
        if machine not in new_set:
            print(i, machine, sep=chr(9))
    print("END OCT24 TO OCT30 ADDED")

    # Cross-check the archive URLs against the live wiki index.
    wiki_url = "https://wiki.bbchallenge.org/wiki/Holdouts_lists?action=raw"
    try:
        with urlopen(Request(wiki_url, headers={"User-Agent": "BB6-research-repro/1.0"}),
                     timeout=35) as response:
            page = response.read().decode("utf-8-sig")
        print(f"Live page: {wiki_url}, SHA256={sha256(page.encode()).hexdigest()}")
        links = re.findall(
            r"BB6_holdouts_([0-9]+)[.]txt",
            page)
        print(f"Live page BB6 downloadable counts: {links[:12]}")
        for match in re.finditer(r".{0,85}(?:608|October 30).{0,85}", page, re.IGNORECASE):
            print("Live page latest-list hint:", match.group().replace("\\n", " ")[:180])
    except (URLError, TimeoutError) as error:
        print(f"Live page unavailable: {type(error).__name__}: {error}")


if __name__ == "__main__":
    main()
