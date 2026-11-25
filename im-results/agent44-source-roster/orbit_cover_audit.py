#!/usr/bin/env python3
"""Audit S4 images of canonical first-one residuals against safety covers.

Table slots are A0,A1,B0,B1,...,F1. A transition is a three-character
string (write bit, direction, target state), e.g. 1RD. refines(child,parent)
means every assignment in parent is identically present in child.
"""
import itertools
import json
import sys
from collections import defaultdict, Counter

REMOVED_RAW = {66, 70, 80}
PERMS = [(0, 1) + p for p in itertools.permutations((2, 3, 4, 5))]
PERM_NAMES = ["".join(chr(65+x) for x in p) for p in PERMS]
ALL_TRANSITIONS = [f"{w}{d}{chr(65+t)}" for w in "01" for d in "LR" for t in range(6)]


def rename_table(table, p):
    out = [None] * 12
    for old_q in range(6):
        new_q = p[old_q]
        for bit in range(2):
            tr = table[2*old_q + bit]
            if tr is None:
                continue
            write, direction, target = tr[0], tr[1], ord(tr[2]) - 65
            out[2*new_q + bit] = f"{write}{direction}{chr(65+p[target])}"
    return tuple(out)


def refines(child, parent):
    return all(parent[i] is None or child[i] == parent[i] for i in range(12))


def compatible(q, r):
    return all(q[i] is None or r[i] is None or q[i] == r[i] for i in range(12))


def key(table):
    return tuple("" if x is None else x for x in table)


def load_entries(path):
    with open(path, encoding="utf-8") as f:
        data = json.load(f)
    raw_entries = data["entries"] if isinstance(data, dict) else data
    out = []
    for e in raw_entries:
        raw = e.get("raw_residual_index", e.get("raw_index"))
        t = e.get("table")
        if not isinstance(t, list) or len(t) != 12:
            raise ValueError(f"unexpected table shape for raw={raw}: {t!r}")
        out.append({"raw": raw, "canonical": e.get("canonical_index"), "table": tuple(t)})
    return out


def union_cover(q, candidate_ids, entries, memo):
    """Does the union of candidate cylinders cover q? Return (bool,witness)."""
    candidate_ids = tuple(i for i in candidate_ids if compatible(q, entries[i]["table"]))
    memo_key = (q, candidate_ids)
    if memo_key in memo:
        return memo[memo_key]
    if not candidate_ids:
        result = (False, ("no-compatible-candidates",))
        memo[memo_key] = result
        return result

    # A single broader candidate already contains the entire q-cylinder.
    for i in candidate_ids:
        if refines(q, entries[i]["table"]):
            result = (True, ("single-parent", entries[i]["raw"]))
            memo[memo_key] = result
            return result

    # Split a still-free slot that is constrained by at least one candidate.
    slots = [s for s in range(12) if q[s] is None and
             any(entries[i]["table"][s] is not None for i in candidate_ids)]
    if not slots:
        result = (False, ("no-further-split",))
        memo[memo_key] = result
        return result
    slot = max(slots, key=lambda s: len({entries[i]["table"][s] for i in candidate_ids
                                        if entries[i]["table"][s] is not None}))
    for tr in ALL_TRANSITIONS:
        child = list(q)
        child[slot] = tr
        child = tuple(child)
        child_ids = tuple(i for i in candidate_ids
                          if entries[i]["table"][slot] is None or entries[i]["table"][slot] == tr)
        if not child_ids:
            result = (False, ("uncovered-child", slot, tr))
            memo[memo_key] = result
            return result
        ok, witness = union_cover(child, child_ids, entries, memo)
        if not ok:
            result = (False, ("failed-branch", slot, tr, witness))
            memo[memo_key] = result
            return result
    result = (True, ("split-cover", slot))
    memo[memo_key] = result
    return result


def main(path):
    all_entries = load_entries(path)
    unresolved = [e for e in all_entries if e["raw"] not in REMOVED_RAW]
    print(f"roster_entries={len(all_entries)} unresolved={len(unresolved)} "
          f"permutations={len(PERMS)} images={len(unresolved)*len(PERMS)}")

    # Exact orbits among all 124 entries, including the three later witness-covered entries.
    by_orbit = defaultdict(list)
    for e in all_entries:
        orbit_key = min(key(rename_table(e["table"], p)) for p in PERMS)
        by_orbit[orbit_key].append(e)
    exact_reps = [min(group, key=lambda x: x["raw"]) for group in by_orbit.values()]
    orbit_sizes = Counter(len(group) for group in by_orbit.values())
    print(f"exact_orbits={len(exact_reps)} orbit_size_hist={dict(sorted(orbit_sizes.items()))}")
    print(f"exact_representative_raw_indices={sorted(e['raw'] for e in exact_reps)}")

    images = []
    for e in unresolved:
        for pi, p in enumerate(PERMS):
            images.append((e, pi, rename_table(e["table"], p)))

    def cover_report(candidates, label):
        uncovered = []
        cover_hist = Counter()
        for e, pi, img in images:
            matches = [r for r in candidates if refines(img, r["table"])]
            cover_hist[len(matches)] += 1
            if not matches:
                uncovered.append((e, pi, img))
        print(f"{label}: candidates={len(candidates)} single-parent-covered={len(images)-len(uncovered)}/{len(images)} "
              f"cover-count-hist={dict(sorted(cover_hist.items()))}")
        for e, pi, img in uncovered:
            print("  UNCOVERED", {"raw": e["raw"], "canonical": e["canonical"],
                                  "perm": PERM_NAMES[pi], "image": img})
        return uncovered

    cover_report(exact_reps, "exact-orbit representatives")
    uncovered = cover_report(all_entries, "all 124 entries")

    # A broader finite union-cover check for images not covered by one roster cylinder.
    unique_uncovered = {}
    for e, pi, img in uncovered:
        unique_uncovered.setdefault(img, []).append((e["raw"], PERM_NAMES[pi]))
    memo = {}
    union_ok = 0
    for img, origins in unique_uncovered.items():
        ok, witness = union_cover(img, tuple(range(len(all_entries))), all_entries, memo)
        union_ok += int(ok)
        if not ok:
            print("  UNION-COVER-FAIL", {"origins": origins[:6], "image": img, "witness": witness})
    print(f"union-cover: unique-single-parent-gaps={len(unique_uncovered)} "
          f"covered-by-union={union_ok}/{len(unique_uncovered)} memo_states={len(memo)}")

    # q32 diagnostic: raw11 is canonical index 7 in the 124-file.
    q32 = next((e for e in unresolved if e["raw"] == 11), None)
    if q32:
        print("q32 images:")
        for pi, p in enumerate(PERMS):
            img = rename_table(q32["table"], p)
            parents = [r["raw"] for r in all_entries if refines(img, r["table"])]
            print(f"  {PERM_NAMES[pi]} -> parents {parents[:8]}{'...' if len(parents)>8 else ''}")


if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("usage: orbit_cover_audit.py canonical-124.json", file=sys.stderr)
        sys.exit(2)
    main(sys.argv[1])
