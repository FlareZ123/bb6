#!/usr/bin/env python3
"""Reproducible Raw124 F1=0LA candidate partition and six-state FAR discovery.

This is discovery only. The fast partition is not a proof; every FAR hit and
every residual must later be connected to an original-source Lean Audit tree.
"""
from __future__ import annotations

import hashlib
import json
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
RAW124 = REPO / "im-results" / "agent2-tnf-raw124"
FAR_SOURCE = REPO / "im-results" / "agent11-tnf-raw86" / "search.cpp"
PARENT = "1RB---_1RC---_0RD---_1LD1RE_---1LF_---0LA"
CAP = 3000
LOOKBACK = 32


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def run(args: list[str], *, cwd: Path, stdout_path: Path | None = None,
        input_text: str | None = None) -> str:
    result = subprocess.run(
        args, cwd=cwd, input=input_text, text=True,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=True,
    )
    if stdout_path is not None:
        stdout_path.write_text(result.stdout)
    return result.stdout


def main() -> None:
    out = Path(sys.argv[1]).resolve()
    out.mkdir(parents=True, exist_ok=True)
    work = out / "work"
    work.mkdir(exist_ok=True)

    fast = work / "fast_partition"
    far_search = work / "far_search"
    run(["g++", "-O3", "-std=c++20", str(RAW124 / "fast_partition.cpp"),
         "-o", str(fast)], cwd=REPO, stdout_path=out / "compile-fast.log")

    prefix = out / "F1-0LA"
    stats = run([str(fast), PARENT, str(CAP), str(LOOKBACK), str(prefix)],
                cwd=REPO, stdout_path=out / "partition.log")
    tree = Path(str(prefix) + ".json").read_bytes()
    open_bytes = Path(str(prefix) + ".open").read_bytes()
    opens = open_bytes.decode().splitlines()
    assert len(opens) == len(set(opens)), "duplicate open table"
    assert len(tree) > 0 and json.loads(tree), "empty or invalid partition tree"

    run(["g++", "-O3", "-std=c++20", str(FAR_SOURCE),
         "-o", str(far_search)], cwd=REPO, stdout_path=out / "compile-far.log")
    far_input = "".join(f"{i} {table.replace('_', '')}\n"
                        for i, table in enumerate(opens))
    far_text = run([str(far_search), "6"], cwd=REPO,
                   stdout_path=out / "far-search.log", input_text=far_input)
    far_rows: dict[int, str] = {}
    for line in far_text.splitlines():
        fields = line.split()
        if len(fields) == 2 and fields[0].isdigit():
            i = int(fields[0])
            assert i not in far_rows, f"duplicate FAR index {i}"
            far_rows[i] = fields[1]
    assert all(0 <= i < len(opens) for i in far_rows)
    hard = [i for i in range(len(opens)) if i not in far_rows]

    (out / "F1-0LA.far").write_text(
        "".join(f"{i} {far_rows[i]}\n" for i in sorted(far_rows)))
    (out / "F1-0LA.hard").write_text(
        "".join(f"{i} {opens[i]}\n" for i in hard))

    summary = {
        "table": PARENT,
        "cap": CAP,
        "lookback": LOOKBACK,
        "completion_count": 25 ** 5,
        "tree_sha256": sha(tree),
        "open_sha256": sha(open_bytes),
        "far_sha256": sha((out / "F1-0LA.far").read_bytes()),
        "open_count": len(opens),
        "far_count": len(far_rows),
        "hard_count": len(hard),
        "hard_indices": hard,
        "partition_stdout": stats.strip(),
    }
    (out / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2), flush=True)


if __name__ == "__main__":
    main()
