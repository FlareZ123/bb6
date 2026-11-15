#!/usr/bin/env python3
"""Canonicalize exact partial-table leaves under root-preserving BB(6) symmetries.

The group is S_5 on states B..F (A fixed) times L/R reflection.
The source semantics of these transformations is proved in
agent8-coverage-contract/Symmetry.lean. This script enumerates the finite
orbits and exports canonical keys; it does not certify machine outcomes.
"""
from __future__ import annotations

import hashlib
import itertools
import json
import sys
from pathlib import Path

LABELS = "ABCDEF"
GROUP = "S5_fix_A_x_LR_reflection"
GROUP_ORDER = 240


def map_state(q: int, perm: tuple[int, ...]) -> int:
    return 0 if q == 0 else perm[q - 1]


def parse_transition(raw: str):
    if raw == "H":
        return None
    if len(raw) != 4 or raw[0] != "M":
        raise ValueError(f"bad transition code: {raw!r}")
    write, right, nxt = int(raw[1]), int(raw[2]), int(raw[3])
    if write not in (0, 1) or right not in (0, 1) or not 0 <= nxt < 6:
        raise ValueError(f"bad transition code: {raw!r}")
    return (write, right, nxt)


def parse_path(raw: str):
    entries = []
    seen = set()
    if raw:
        for item in raw.split(","):
            slot, trans = item.split(":", 1)
            if len(slot) != 2:
                raise ValueError(f"bad slot code: {slot!r}")
            q, symbol = int(slot[0]), int(slot[1])
            if not 0 <= q < 6 or symbol not in (0, 1):
                raise ValueError(f"bad slot code: {slot!r}")
            if (q, symbol) in seen:
                raise ValueError(f"duplicate branch slot in path: {(q, symbol)}")
            seen.add((q, symbol))
            entries.append((q, symbol, parse_transition(trans)))
    return tuple(entries)


def encode_path(entries) -> str:
    def enc(entry):
        q, symbol, trans = entry
        if trans is None:
            action = "H"
        else:
            write, right, nxt = trans
            action = f"M{write}{right}{nxt}"
        return f"{q}{symbol}:{action}"

    return ";".join(enc(entry) for entry in sorted(entries, key=lambda e: (e[0], e[1])))


def transform(entries, perm, reflect):
    out = []
    for q, symbol, trans in entries:
        q2 = map_state(q, perm)
        if trans is None:
            trans2 = None
        else:
            write, right, nxt = trans
            trans2 = (write, right ^ int(reflect), map_state(nxt, perm))
        out.append((q2, symbol, trans2))
    return tuple(out)


PERMS = tuple(itertools.permutations(range(1, 6)))
assert len(PERMS) == 120
TRANSFORMS = tuple((perm, reflect) for perm in PERMS for reflect in (False, True))
assert len(TRANSFORMS) == GROUP_ORDER


def canonicalize(entries):
    best = None
    best_transform = None
    orbit = set()
    for perm, reflect in TRANSFORMS:
        key = encode_path(transform(entries, perm, reflect))
        orbit.add(key)
        if best is None or key < best:
            best = key
            best_transform = (perm, reflect)
    orbit_size = len(orbit)
    assert orbit_size > 0 and GROUP_ORDER % orbit_size == 0
    perm, reflect = best_transform
    witness = {
        "old_to_new_state_labels": [LABELS[map_state(q, perm)] for q in range(6)],
        "left_right_reflection": reflect,
    }
    return best, orbit_size, witness


def transition_json(trans):
    if trans is None:
        return {"halt": True}
    write, right, nxt = trans
    return {
        "halt": False,
        "write": write,
        "direction": "R" if right else "L",
        "next_state": LABELS[nxt],
    }


def build_record(status, weight, entries):
    depth = len(entries)
    expected = 25 ** (12 - depth)
    if weight != expected:
        raise ValueError(
            f"cylinder mass mismatch: got {weight}, expected {expected} at depth {depth}"
        )
    table = [None] * 12
    branch_path = []
    assigned = set()
    for q, symbol, trans in entries:
        idx = 2 * q + symbol
        if idx in assigned:
            raise ValueError("duplicate slot")
        assigned.add(idx)
        table[idx] = transition_json(trans)
        branch_path.append({
            "slot": f"{LABELS[q]}/{symbol}",
            "transition": transition_json(trans),
        })
    free_slots = [
        f"{LABELS[q]}/{symbol}"
        for q in range(6)
        for symbol in (0, 1)
        if 2 * q + symbol not in assigned
    ]
    key, orbit_size, witness = canonicalize(entries)
    return {
        "terminal_status": "certified" if status == "C" else "open",
        "root": {"state": "A", "head": 0, "tape": "all-zero"},
        "branch_depth": depth,
        "branch_path": branch_path,
        "partial_table_A0_A1_B0_B1_C0_C1_D0_D1_E0_E1_F0_F1": table,
        "free_slots": free_slots,
        "compatible_raw_completions": weight,
        "root_preserving_symmetry": {
            "group": GROUP,
            "group_order": GROUP_ORDER,
            "canonical_key": key,
            "orbit_size": orbit_size,
            "stabilizer_size": GROUP_ORDER // orbit_size,
            "canonicalizing_transform": witness,
        },
    }


def main():
    if len(sys.argv) != 4:
        raise SystemExit(
            "usage: canonicalize_residual_frontier.py INPUT.tsv REPORT.txt OUTPUT_PREFIX"
        )
    source, report_path, prefix = map(Path, sys.argv[1:])
    report_lines = report_path.read_text().strip().splitlines()
    if len(report_lines) != 2:
        raise ValueError("Lean report file must contain certified and open mass on two lines")
    expected_certified, expected_open = map(int, report_lines)

    output = Path(str(prefix) + ".jsonl")
    summary_path = Path(str(prefix) + "-summary.json")
    groups = {}
    seen_paths = set()
    certified_mass = open_mass = 0
    certified_count = open_count = total_count = 0

    input_hash = hashlib.sha256(source.read_bytes()).hexdigest()
    with source.open() as src, output.open("w") as dst:
        header = src.readline().rstrip("\n")
        if header != "status\tweight\tpath":
            raise ValueError(f"unexpected manifest header: {header!r}")
        for line_no, line in enumerate(src, 2):
            line = line.rstrip("\n")
            if not line:
                continue
            status, raw_weight, raw_path = line.split("\t", 2)
            if status not in ("C", "O"):
                raise ValueError(f"bad status on line {line_no}: {status!r}")
            weight = int(raw_weight)
            entries = parse_path(raw_path)
            path_key = encode_path(entries)
            if path_key in seen_paths:
                raise ValueError(f"duplicate terminal path at line {line_no}: {path_key}")
            seen_paths.add(path_key)
            record = build_record(status, weight, entries)
            dst.write(json.dumps(record, separators=(",", ":")) + "\n")
            total_count += 1

            sym = record["root_preserving_symmetry"]
            key = sym["canonical_key"]
            group = groups.setdefault(key, {
                "canonical_key": key,
                "orbit_size": sym["orbit_size"],
                "leaves": 0,
                "certified_leaves": 0,
                "open_leaves": 0,
                "certified_mass": 0,
                "open_mass": 0,
            })
            if group["orbit_size"] != sym["orbit_size"]:
                raise ValueError("inconsistent orbit size within one canonical class")
            group["leaves"] += 1
            if status == "C":
                certified_count += 1
                certified_mass += weight
                group["certified_leaves"] += 1
                group["certified_mass"] += weight
            else:
                open_count += 1
                open_mass += weight
                group["open_leaves"] += 1
                group["open_mass"] += weight

    total_mass = certified_mass + open_mass
    if total_mass != 25 ** 12:
        raise ValueError(f"manifest mass does not conserve 25^12: {total_mass}")
    if certified_mass != expected_certified or open_mass != expected_open:
        raise ValueError(
            f"manifest/report mismatch: manifest=({certified_mass},{open_mass}), "
            f"Lean=({expected_certified},{expected_open})"
        )

    group_rows = sorted(
        groups.values(),
        key=lambda g: (-g["open_mass"], -g["open_leaves"], g["canonical_key"]),
    )
    mixed = [g for g in group_rows if g["certified_leaves"] and g["open_leaves"]]
    partial_open_orbits = [
        g for g in group_rows if g["open_leaves"] and g["leaves"] < g["orbit_size"]
    ]
    full_open_orbits = [
        g for g in group_rows if g["open_leaves"] and g["leaves"] == g["orbit_size"]
    ]
    summary = {
        "schema": "bb6-residual-frontier-v1",
        "source_manifest_sha256": input_hash,
        "root": {"state": "A", "head": 0, "tape": "all-zero"},
        "audit_parameters": {
            "bound": 6,
            "finite_ray_limit": 6,
            "physical_scan_limit": 12,
            "exact_lasso_limit": 12,
            "entry_prefix_limit": 2,
            "macro_limit": 4,
            "tree_depth": 4,
        },
        "terminal_leaves": total_count,
        "certified_leaves": certified_count,
        "open_leaves": open_count,
        "certified_raw_table_mass": certified_mass,
        "open_raw_table_mass": open_mass,
        "total_raw_table_mass": total_mass,
        "certified_fraction": certified_mass / total_mass,
        "open_fraction": open_mass / total_mass,
        "root_preserving_symmetry_group": GROUP,
        "symmetry_group_order": GROUP_ORDER,
        "distinct_partial_table_symmetry_classes": len(groups),
        "mixed_status_symmetry_classes": len(mixed),
        "open_classes_with_incomplete_orbit_coverage": len(partial_open_orbits),
        "open_classes_with_full_orbit_coverage": len(full_open_orbits),
        "mixed_status_examples": mixed[:25],
        "largest_open_classes": group_rows[:50],
        "mass_matches_lean_report": True,
        "mass_matches_full_raw_universe": True,
        "note": (
            "Symmetry keys are exhaustive finite computations under S5 fixing A "
            "and L/R reflection; source-level semantic preservation is proved in "
            "agent8-coverage-contract/Symmetry.lean. Class grouping is metadata "
            "and does not replace disjoint raw-cylinder accounting."
        ),
    }
    summary_path.write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps({
        key: summary[key] for key in (
            "terminal_leaves",
            "certified_leaves",
            "open_leaves",
            "certified_raw_table_mass",
            "open_raw_table_mass",
            "total_raw_table_mass",
            "distinct_partial_table_symmetry_classes",
            "mixed_status_symmetry_classes",
            "open_classes_with_incomplete_orbit_coverage",
            "open_classes_with_full_orbit_coverage",
        )
    }, indent=2))
    print(f"MANIFEST_JSONL={output}")
    print(f"SUMMARY_JSON={summary_path}")


if __name__ == "__main__":
    main()
