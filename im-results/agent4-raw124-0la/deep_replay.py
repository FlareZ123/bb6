#!/usr/bin/env python3
"""Deepen the exact residual tables from a Raw124 fast-cut artifact.

Each residual is reclassified by the same C++ fast_partition engine at a
higher cap. The resulting trees are later spliced into the Lean Audit tree by
replay_fast_cut_deep.py. This is deterministic exhaustive computation, not
itself a proof until the generated Lean tree is source-checked.
"""
from __future__ import annotations

import argparse
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[2]
FAST_SOURCE = ROOT / "im-results" / "agent2-tnf-raw124" / "fast_partition.cpp"


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def walk(tree, counts: Counter, opens: list[str]) -> None:
    tag = tree[0]
    if tag in ("last", "cycle"):
        counts[tag] += 1
    elif tag == "open":
        counts["open"] += 1
        opens.append(tree[1].replace("_", ""))
    elif tag == "split":
        counts["split"] += 1
        assert len(tree[3]) == 24
        for child in tree[3]:
            walk(child, counts, opens)
    else:
        raise ValueError(f"unknown fast_partition node: {tag!r}")


def run_one(index: int, table: str, exe: Path, out: Path,
            cap: int, lookback: int):
    with tempfile.TemporaryDirectory(prefix=f"residual-{index:05d}-", dir=out) as td:
        prefix = Path(td) / "tree"
        proc = subprocess.run(
            [str(exe), table, str(cap), str(lookback), str(prefix)],
            check=True, capture_output=True, text=True,
        )
        tree_path = Path(str(prefix) + ".json")
        tree_bytes = tree_path.read_bytes()
        tree = json.loads(tree_bytes)
        return index, table.replace("_", ""), tree, proc.stdout.strip(), sha(tree_bytes)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("remaining", type=Path,
                        help="Raw124New0LA.remaining from the partial-cut artifact")
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--cap", type=int, default=6_766_859)
    parser.add_argument("--lookback", type=int, default=32)
    parser.add_argument("--workers", type=int, default=2)
    args = parser.parse_args()

    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    tables = [line.strip() for line in args.remaining.read_text().splitlines() if line.strip()]
    normalized = [t.replace("_", "") for t in tables]
    assert len(normalized) == len(set(normalized)), "duplicate residual tables"
    assert tables, "empty residual list"

    exe = out / "fast_partition"
    subprocess.run(
        ["g++", "-O3", "-std=c++20", str(FAST_SOURCE), "-o", str(exe)],
        check=True, capture_output=True, text=True,
    )

    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        results = list(pool.map(
            lambda pair: run_one(pair[0], pair[1], exe, out, args.cap, args.lookback),
            enumerate(tables),
        ))

    trees = {table: tree for _, table, tree, _, _ in results}
    assert len(trees) == len(tables)
    counts: Counter = Counter()
    open_tables: list[str] = []
    root_kinds: Counter = Counter()
    for tree in trees.values():
        root_kinds[tree[0]] += 1
        walk(tree, counts, open_tables)
    assert len(open_tables) == len(set(open_tables)), "duplicate deep open leaves"

    per_root = [
        {"index": i, "table": table, "root": tree[0],
         "stdout": stdout, "tree_sha256": tree_hash}
        for i, table, tree, stdout, tree_hash in results
    ]
    deep = {
        "bound": args.cap,
        "lookback": args.lookback,
        "source": "im-results/agent2-tnf-raw124/fast_partition.cpp",
        "source_sha256": sha(FAST_SOURCE.read_bytes()),
        "trees": trees,
    }
    deep_bytes = json.dumps(deep, separators=(",", ":")).encode()
    (out / "deep.json").write_bytes(deep_bytes)
    (out / "deep.remaining").write_text("\n".join(open_tables) + ("\n" if open_tables else ""))
    summary = {
        "input_count": len(tables),
        "root_kinds": dict(root_kinds),
        "nested_node_counts": dict(counts),
        "remaining_open_count": len(open_tables),
        "remaining_open_sha256": sha((out / "deep.remaining").read_bytes()),
        "deep_json_sha256": sha(deep_bytes),
        "cap": args.cap,
        "lookback": args.lookback,
        "workers": args.workers,
        "per_root": per_root,
    }
    (out / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps({k: v for k, v in summary.items() if k != "per_root"}, indent=2), flush=True)


if __name__ == "__main__":
    main()
