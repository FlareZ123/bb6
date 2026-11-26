#!/usr/bin/env python3
"""Reproduce the metadata-level intersection of upstream one-hole leaves with Canonical58."""

from collections import Counter, defaultdict
from datetime import datetime, timezone
from fractions import Fraction
import csv
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[2]
TSV = ROOT / "im-results/agent10-nov26-cryptids/holdout-source-crosswalk.tsv"
ROSTER_JSON = ROOT / "im-results/agent13-roster-convergence/canonical-124.json"
OUT = Path(__file__).resolve().parent / "crosswalk.json"

EXCLUSIONS = {
    "Combined106": [66, 70, 80, 86, 87, 88, 91, 92, 93, 97, 98, 100, 101, 102, 104, 68, 72, 82],
    "CanonicalTwoParent": [107, 114],
    "Canonical68StableBatch": [60, 109, 110, 111, 117, 121, 123, 125],
    "Canonical65AfterThree": [71, 77, 81],
    "Canonical64Raw120": [120],
    "Canonical59FiveParent": [58, 108, 115, 118, 119],
    "Canonical58Raw113": [113],
}
REMOVED = {n for values in EXCLUSIONS.values() for n in values}
STATE = {c: i for i, c in enumerate("ABCDEF")}
MOVES = [f"{w}{d}{s}" for w in "01" for d in "LR" for s in "ABCDEF"] + ["---"]


def decode_rle(rle):
    blocks = rle.split("_")
    if len(blocks) != 6 or any(len(block) != 6 for block in blocks):
        raise ValueError(f"not a six-state/two-symbol RLE: {rle}")
    table = []
    for block in blocks:
        for token in (block[:3], block[3:]):
            table.append(None if token in ("---", "HHH") else token)
    return table


def encode_rle(table):
    if len(table) != 12:
        raise ValueError("expected 12 transition slots")
    tokens = ["---" if x is None else x for x in table]
    return "_".join(tokens[i] + tokens[i + 1] for i in range(0, 12, 2))


def canonical_address(address, initial_cut=2):
    cut = initial_cut
    for step in address:
        target = STATE[step["move"][-1]]
        if target > cut:
            return False
        cut = max(cut, target + 1)
    return True


def extends_table(parent, child):
    return len(parent) == len(child) and all(
        p is None or p == c for p, c in zip(parent, child)
    )


def expand_one_hole(table):
    holes = [i for i, value in enumerate(table) if value is None]
    if len(holes) != 1:
        raise ValueError(f"expected one hole, found {len(holes)} in {encode_rle(table)}")
    out = set()
    for move in MOVES:
        child = list(table)
        child[holes[0]] = move
        out.add(tuple(child))
    return out


def main():
    raw = json.loads(ROSTER_JSON.read_text())
    entries = raw["entries"]
    canonical = [e for e in entries if canonical_address(e["address"])]
    current = [
        e for e in canonical
        if int(e["raw_residual_index"]) not in REMOVED
    ]
    if len(current) != 58:
        raise AssertionError(f"expected Canonical58 count 58, got {len(current)}")

    # The accepted Canonical58 theorem retains Raw59; Canonical59 consumed Raw118.
    current_ids = [int(e["raw_residual_index"]) for e in current]
    if len(set(current_ids)) != len(current_ids) or 59 not in current_ids or 118 in current_ids:
        raise AssertionError("incorrect Canonical58 identity: expected unique IDs, retained Raw59, removed Raw118")

    with TSV.open(newline="") as handle:
        rows = list(csv.DictReader(handle, delimiter="\t"))
    if len(rows) != 56:
        raise AssertionError(f"expected 56 crosswalk rows, got {len(rows)}")

    groups = defaultdict(lambda: {
        "rows": [],
        "all_completions": set(),
        "nonhalt_completions": set(),
    })
    matches = []
    global_completions = set()
    for row in rows:
        holdout = decode_rle(row["holdout_rle"])
        source = decode_rle(row["source_rle"])
        if holdout != source:
            raise AssertionError(f"holdout/source RLE mismatch: {row['upstream_module']}")
        leaf_holes = [i for i, value in enumerate(holdout) if value is None]
        if len(leaf_holes) != 1:
            raise AssertionError(f"expected one-hole leaf: {row['upstream_module']}")

        all_ancestors = [e for e in canonical if extends_table(e["table"], holdout)]
        current_ancestors = [e for e in current if extends_table(e["table"], holdout)]
        if len(all_ancestors) != 1 or len(current_ancestors) != 1:
            raise AssertionError(
                f"non-unique current ancestor for {row['upstream_module']}: "
                f"all={len(all_ancestors)}, current={len(current_ancestors)}"
            )
        ancestor = current_ancestors[0]
        raw_index = int(ancestor["raw_residual_index"])
        expanded = expand_one_hole(holdout)
        group = groups[raw_index]
        group["rows"].append(row)
        group["all_completions"].update(expanded)
        if row["source_kind"] == "NonHalt":
            group["nonhalt_completions"].update(expanded)
        global_completions.update(expanded)

        matches.append({
            "raw_parent": int(row["raw_parent"]),
            "batch": row["batch"],
            "source_kind": row["source_kind"],
            "upstream_module": row["upstream_module"],
            "upstream_blob_sha": row["blob_sha"],
            "first_use_after_root_time_slot": row["first_use_after_root_time_slot"],
            "holdout_rle": row["holdout_rle"],
            "source_rle": row["source_rle"],
            "leaf_hole_count": 1,
            "current_ancestor": {
                "raw_residual_index": raw_index,
                "canonical_index": int(ancestor["canonical_index"]),
                "holes": int(ancestor["holes"]),
                "address": [x["move"] for x in ancestor["address"]],
                "table_rle": encode_rle(ancestor["table"]),
            },
        })

    summaries = []
    for raw_index, group in sorted(groups.items()):
        first = next(e for e in current if int(e["raw_residual_index"]) == raw_index)
        batch_counts = Counter(row["batch"] for row in group["rows"])
        kind_counts = Counter(row["source_kind"] for row in group["rows"])
        holes = int(first["holes"])
        all_count = len(group["all_completions"])
        nonhalt_count = len(group["nonhalt_completions"])
        total = 25 ** holes
        summaries.append({
            "raw_residual_index": raw_index,
            "canonical_index": int(first["canonical_index"]),
            "holes": holes,
            "address": [x["move"] for x in first["address"]],
            "row_count": len(group["rows"]),
            "batch_counts": dict(sorted(batch_counts.items())),
            "source_kind_counts": dict(sorted(kind_counts.items())),
            "distinct_leaf_completions_all_kinds": all_count,
            "distinct_leaf_completions_nonhalt_only": nonhalt_count,
            "total_parent_completions": total,
            "all_kind_fraction": str(Fraction(all_count, total)),
            "nonhalt_fraction": str(Fraction(nonhalt_count, total)),
            "upstream_modules": sorted(row["upstream_module"] for row in group["rows"]),
        })

    report = {
        "status": "metadata-level routing crosswalk; not a Lean theorem or parent Cover",
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "source_repo_head": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True
        ).strip(),
        "inputs": {
            "crosswalk_tsv": {
                "path": str(TSV.relative_to(ROOT)),
                "git_blob_sha": subprocess.check_output(["git", "hash-object", str(TSV)], cwd=ROOT, text=True).strip(),
            },
            "canonical_124_json": {
                "path": str(ROSTER_JSON.relative_to(ROOT)),
                "git_blob_sha": subprocess.check_output(["git", "hash-object", str(ROSTER_JSON)], cwd=ROOT, text=True).strip(),
            },
        },
        "canonical_address_initial_cut": 2,
        "parent_exclusions": EXCLUSIONS,
        "removed_parent_count": len(REMOVED),
        "canonical_address_roster_count": len(canonical),
        "current_roster_count": len(current),
        "current_roster_raw_indices": sorted(int(e["raw_residual_index"]) for e in current),
        "crosswalk_row_count": len(rows),
        "unique_current_ancestor_match_count": len(matches),
        "unmatched_or_ambiguous_count": 0,
        "unique_leaf_completion_count_global": len(global_completions),
        "group_summaries": summaries,
        "matches": matches,
        "interpretation": [
            "Each TSV row is a one-hole table extending exactly one current Canonical58 residual.",
            "The table-extension mapping is a routing result; the 56 source modules are not thereby locally accepted Covers.",
            "A one-hole cylinder contains 25 completions, while the current residual ancestors have 8-10 holes.",
            "Only Raw140 n4/n5 are identified as locally source-accepted 25-completion NonHalt Covers in the Agent10 dossier; other source statuses must be checked there.",
            "No current residual parent is closed and no Canonical58 count reduction follows from this crosswalk.",
        ],
    }
    OUT.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({
        "output": str(OUT.relative_to(ROOT)),
        "current_roster_count": len(current),
        "crosswalk_rows": len(rows),
        "unique_matches": len(matches),
        "groups": [
            {k: v for k, v in summary.items() if k != "upstream_modules"}
            for summary in summaries
        ],
    }, indent=2))


if __name__ == "__main__":
    main()
