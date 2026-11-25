#!/usr/bin/env python3
"""Audit whether S4 images of canonical first-one residuals are covered by representatives.

Table convention: slots A0,A1,B0,B1,...,F1; a transition is a 3-char
string write-bit, direction, target-state (e.g. 1RD). refines(child,parent)
means every assignment in parent is also present identically in child, so
safety of parent implies safety of child.
"""
import itertools, json, sys
from collections import defaultdict, Counter

REMOVED_RAW = {66, 70, 80}
PERMS = [(0, 1) + p for p in itertools.permutations((2, 3, 4, 5))]
PERM_NAMES = ["".join(chr(65+x) for x in p) for p in PERMS]


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


def key(table):
    return tuple("" if x is None else x for x in table)


def load_entries(path):
    with open(path, encoding="utf-8") as f:
        data = json.load(f)
    entries = data["entries"] if isinstance(data, dict) else data
    remove_raw = REMOVED_RAW if len(entries) > 121 else set()
    out = []
    for e in entries:
        raw = e.get("raw_residual_index", e.get("raw_index"))
        if raw in remove_raw:
            continue
        t = e.get("table")
        if not isinstance(t, list) or len(t) != 12:
            raise ValueError(f"unexpected table shape for raw={raw}: {t!r}")
        out.append({"raw": raw, "canonical": e.get("canonical_index"), "table": tuple(t)})
    return out


def main(path):
    entries = load_entries(path)
    print(f"residuals={len(entries)} permutations={len(PERMS)} images={len(entries)*len(PERMS)}")

    # Exact orbit classes among the roster; choose lowest raw index in each.
    by_orbit = defaultdict(list)
    for e in entries:
        orbit_key = min(key(rename_table(e["table"], p)) for p in PERMS)
        by_orbit[orbit_key].append(e)
    exact_reps = [min(group, key=lambda x: x["raw"]) for group in by_orbit.values()]
    orbit_sizes = Counter(len(group) for group in by_orbit.values())
    print(f"exact_orbits={len(exact_reps)} orbit_size_hist={dict(sorted(orbit_sizes.items()))}")
    print(f"exact_representative_raw_indices={sorted(e['raw'] for e in exact_reps)}")

    images = []
    for e in entries:
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
        print(f"{label}: candidates={len(candidates)} covered={len(images)-len(uncovered)}/{len(images)} "
              f"cover-count-hist={dict(sorted(cover_hist.items()))}")
        for e, pi, img in uncovered[:12]:
            print("  UNCOVERED", {"raw": e["raw"], "canonical": e["canonical"],
                                  "perm": PERM_NAMES[pi], "image": img})
        return uncovered

    cover_report(exact_reps, "exact-orbit representatives")
    cover_report(entries, "all roster entries")

    # Greedy set cover over all roster entries (upper bound, not optimality proof).
    cover_sets = []
    for r in entries:
        covered = {i for i, (_, _, img) in enumerate(images) if refines(img, r["table"])}
        cover_sets.append(covered)
    uncovered = set(range(len(images)))
    selected = []
    while uncovered:
        best_i, best_set = max(enumerate(cover_sets), key=lambda it: len(it[1] & uncovered))
        gain = len(best_set & uncovered)
        if gain == 0:
            break
        selected.append(entries[best_i])
        uncovered -= best_set
    print(f"greedy_cover: selected={len(selected)} covered={len(images)-len(uncovered)}/{len(images)} "
          f"raw_indices={[e['raw'] for e in selected]}")
    if uncovered:
        for i in sorted(uncovered)[:12]:
            e, pi, img = images[i]
            print("  GREEDY_UNCOVERED", {"raw": e["raw"], "canonical": e["canonical"],
                                        "perm": PERM_NAMES[pi], "image": img})

    # q32 diagnostic: raw11 is canonical index 7 in the 124-file.
    q32 = next((e for e in entries if e["raw"] == 11), None)
    if q32:
        print("q32 images:")
        for pi, p in enumerate(PERMS):
            img = rename_table(q32["table"], p)
            parents = [r["raw"] for r in entries if refines(img, r["table"])]
            print(f"  {PERM_NAMES[pi]} -> parents {parents[:8]}{'...' if len(parents)>8 else ''}")


if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("usage: orbit_cover_audit.py canonical-124.json", file=sys.stderr)
        sys.exit(2)
    main(sys.argv[1])
