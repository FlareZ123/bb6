#!/usr/bin/env python3
"""Candidate crosswalk from pinned Cryptids BB(6) modules to the live canonical76 frontier.

This script compares source-table RLEs under all 24 state permutations fixing A and B.
It is a routing aid, not a Lean proof: matches must still be imported, adapted, and
kernel-audited before they can close a residual.
"""
from __future__ import annotations

import argparse
import collections
import hashlib
import itertools
import json
import pathlib
import re
import sys

LETTERS = "ABCDEF"
MOVE_RE = re.compile(r"^[01][LR][A-F]$")


def parse_rle(stem: str) -> list[str] | None:
    if not stem.startswith("M_"):
        return None
    tokens = stem[2:].split("_")
    if len(tokens) != 12:
        return None
    if any(t not in {"HHH", "---"} and not MOVE_RE.fullmatch(t) for t in tokens):
        return None
    return tokens


def parse_export(path: pathlib.Path) -> list[dict]:
    records = []
    for line_no, line in enumerate(path.read_text().splitlines(), 1):
        if not line or line.startswith("kind\t"):
            continue
        fields = line.split("\t")
        if len(fields) != 3:
            raise ValueError(f"{path}:{line_no}: expected 3 TSV fields, got {len(fields)}")
        kind, address, table = fields
        tokens = table.split("_")
        if len(tokens) != 12:
            raise ValueError(f"{path}:{line_no}: expected 12 table entries, got {len(tokens)}")
        if any(t not in {"HHH", "---"} and not MOVE_RE.fullmatch(t) for t in tokens):
            raise ValueError(f"{path}:{line_no}: invalid table token")
        records.append({
            "kind": kind,
            "address": [] if address == "-" else address.split(","),
            "table": tokens,
            "holes": sum(t == "---" for t in tokens),
        })
    counts = collections.Counter(r["kind"] for r in records)
    if counts.get("BASE76", 0) != 76:
        raise ValueError(f"expected 76 BASE76 rows, got {counts.get('BASE76', 0)}")
    if counts.get("REMAINING112", 0) != 112:
        raise ValueError(f"expected 112 REMAINING112 rows, got {counts.get('REMAINING112', 0)}")
    return records


def rename_token(token: str, perm: tuple[int, ...]) -> str:
    if token in {"HHH", "---"}:
        return token
    return token[:2] + LETTERS[perm[LETTERS.index(token[2])]]


def rename_table(tokens: list[str], perm: tuple[int, ...]) -> list[str]:
    out = [""] * 12
    for q in range(6):
        for bit in range(2):
            out[2 * perm[q] + bit] = rename_token(tokens[2 * q + bit], perm)
    return out


def compatible(parent: list[str], source: list[str]) -> bool:
    return all(p == "---" or p == s for p, s in zip(parent, source))


def first_hole_route(parent: list[str], source: list[str]) -> dict:
    """Follow ordinary source moves through first holes until halt or a singleton."""
    work = list(parent)
    path_moves: list[str] = []
    while "---" in work:
        i = work.index("---")
        token = source[i]
        if token == "---":
            return {"match_type": "source_incomplete", "path_moves": path_moves, "halt_slot": i}
        if token == "HHH":
            trailing = [j for j in range(i + 1, 12) if work[j] == "---"]
            if trailing:
                return {
                    "match_type": "halt_before_trailing_holes",
                    "path_moves": path_moves,
                    "halt_slot": i,
                    "trailing_holes": trailing,
                }
            return {
                "match_type": "one_hole_leaf",
                "path_moves": path_moves,
                "halt_slot": i,
            }
        work[i] = token
        path_moves.append(token)
    return {
        "match_type": "singleton_completion",
        "path_moves": path_moves,
        "halt_slot": next((i for i, t in enumerate(source) if t == "HHH"), None),
    }


def slot_name(i: int | None) -> str | None:
    if i is None:
        return None
    return f"{LETTERS[i // 2]}{i % 2}"


def collect_sources(root: pathlib.Path) -> list[dict]:
    sources = []
    for path in sorted(root.rglob("M_*.lean")):
        parts = set(path.parts)
        if "NonHalt" in parts:
            kind = "NonHalt"
        elif "Halt" in parts:
            kind = "Halt"
        else:
            continue
        tokens = parse_rle(path.stem)
        if tokens is None:
            continue
        text = path.read_text(errors="replace")
        theorem_hint = (
            "is_not_halt" if re.search(r"\b(?:theorem|def)\s+is_not_halt\b", text)
            else "is_halt" if re.search(r"\b(?:theorem|def)\s+is_halt\b", text)
            else "unlocated"
        )
        rel = path.relative_to(root)
        module = "BusyBeaver.BB6." + ".".join(rel.with_suffix("").parts)
        sources.append({
            "module": module,
            "path": str(rel),
            "kind": kind,
            "tokens": tokens,
            "theorem_hint": theorem_hint,
            "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
        })
    return sources


def run(args: argparse.Namespace) -> dict:
    parents = parse_export(args.roster_tsv)
    sources = collect_sources(args.cryptids_root)
    counts = collections.Counter(s["kind"] for s in sources)
    theorem_counts = collections.Counter(s["theorem_hint"] for s in sources)
    if args.expected_source_count == 191 and (counts["NonHalt"] != 159 or counts["Halt"] != 32):
        raise ValueError(f"pinned catalogue class drift: expected NonHalt=159,Halt=32, got {dict(counts)}")
    if args.expected_source_count is not None and len(sources) != args.expected_source_count:
        raise ValueError(
            f"pinned source catalogue drift: expected {args.expected_source_count}, got {len(sources)} "
            f"(NonHalt={counts['NonHalt']}, Halt={counts['Halt']})"
        )

    perms = [(0, 1, *tail) for tail in itertools.permutations(range(2, 6))]
    grouped: dict[tuple, dict] = {}
    for parent_index, parent in enumerate(parents):
        parent_id = f"{parent['kind']}:{','.join(parent['address']) or '-'}"
        for source in sources:
            for perm in perms:
                renamed = rename_table(source["tokens"], perm)
                if not compatible(parent["table"], renamed):
                    continue
                route = first_hole_route(parent["table"], renamed)
                if route["match_type"] in {"source_incomplete", "halt_before_trailing_holes"}:
                    continue
                path_moves = route["path_moves"]
                leaf_address = parent["address"] + path_moves
                key = (
                    source["module"], parent_id, route["match_type"],
                    ",".join(leaf_address), route.get("halt_slot"),
                )
                entry = grouped.setdefault(key, {
                    "source_module": source["module"],
                    "source_path": source["path"],
                    "source_kind": source["kind"],
                    "theorem_hint": source["theorem_hint"],
                    "source_sha256": source["sha256"],
                    "parent_kind": parent["kind"],
                    "parent_address": parent["address"],
                    "parent_holes": parent["holes"],
                    "match_type": route["match_type"],
                    "leaf_address": leaf_address,
                    "halt_slot": slot_name(route.get("halt_slot")),
                    "permutations": [],
                })
                perm_text = "".join(LETTERS[perm[i]] for i in range(6))
                if perm_text not in entry["permutations"]:
                    entry["permutations"].append(perm_text)

    matches = list(grouped.values())
    leaf_by_parent: dict[str, dict[str, set[str]]] = {}
    for m in matches:
        if m["match_type"] != "one_hole_leaf":
            continue
        if m["source_kind"] == "NonHalt" and m["theorem_hint"] != "is_not_halt":
            continue
        if m["source_kind"] == "Halt" and m["theorem_hint"] != "is_halt":
            continue
        pid = f"{m['parent_kind']}:{','.join(m['parent_address']) or '-'}"
        leaf_by_parent.setdefault(pid, {"NonHalt": set(), "Halt": set()})[m["source_kind"]].add(
            ",".join(m["leaf_address"])
        )

    parent_summaries = []
    for parent in parents:
        pid = f"{parent['kind']}:{','.join(parent['address']) or '-'}"
        found = leaf_by_parent.get(pid, {"NonHalt": set(), "Halt": set()})
        expected = 24 ** max(parent["holes"] - 1, 0) if parent["holes"] else 1
        nonhalt_count = len(found["NonHalt"])
        halt_count = len(found["Halt"])
        parent_summaries.append({
            "parent_id": pid,
            "holes": parent["holes"],
            "expected_one_hole_leaves_if_all_ordinary_prefixes_are_split": expected,
            "distinct_nonhalt_one_hole_leaves": nonhalt_count,
            "distinct_halt_one_hole_candidates": halt_count,
            "one_hole_parent_has_nonhalt_candidate": bool(parent["holes"] == 1 and nonhalt_count >= 1),
            "full_nonhalt_leaf_match_coverage": bool(parent["holes"] > 0 and nonhalt_count >= expected),
        })

    summary = {
        "status": "candidate_crosswalk_only",
        "source_root": str(args.cryptids_root),
        "source_commit": args.source_commit,
        "source_modules": len(sources),
        "source_kind_counts": dict(counts),
        "source_theorem_hint_counts": dict(theorem_counts),
        "root_fixing_permutations_checked": len(perms),
        "frontier_parent_records": len(parents),
        "frontier_record_counts": dict(collections.Counter(p["kind"] for p in parents)),
        "distinct_source_parent_route_candidates": len(matches),
        "source_parent_permutation_hits": sum(len(m["permutations"]) for m in matches),
        "one_hole_leaf_matches": sum(m["match_type"] == "one_hole_leaf" for m in matches),
        "singleton_completion_matches": sum(m["match_type"] == "singleton_completion" for m in matches),
        "nonhalt_one_hole_leaf_matches": sum(m["match_type"] == "one_hole_leaf" and m["source_kind"] == "NonHalt" and m["theorem_hint"] == "is_not_halt" for m in matches),
        "halt_one_hole_candidates": sum(m["match_type"] == "one_hole_leaf" and m["source_kind"] == "Halt" and m["theorem_hint"] == "is_halt" for m in matches),
        "parents_with_one_hole_nonhalt_candidates": sum(p["one_hole_parent_has_nonhalt_candidate"] for p in parent_summaries),
        "parents_with_full_nonhalt_leaf_match_coverage": sum(p["full_nonhalt_leaf_match_coverage"] for p in parent_summaries),
        "parent_summaries": parent_summaries,
        "matches": matches,
        "caveat": (
            "Filename RLE matching under A/B-fixing permutations is only candidate routing. "
            "Every match still requires source theorem import, exact table/permutation proof, "
            "first-hole address proof, and a kernel-checked Cover adapter. Halt candidates "
            "also require an explicit primitive-step bound."
        ),
    }
    return summary


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--roster-tsv", type=pathlib.Path, required=True)
    ap.add_argument("--cryptids-root", type=pathlib.Path, required=True)
    ap.add_argument("--out", type=pathlib.Path, required=True)
    ap.add_argument("--source-commit", required=True)
    ap.add_argument("--expected-source-count", type=int, default=191)
    args = ap.parse_args()
    summary = run(args)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps({k: v for k, v in summary.items() if k not in {"matches", "parent_summaries"}}, indent=2))


if __name__ == "__main__":
    main()
