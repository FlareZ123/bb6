#!/usr/bin/env python3
"""Batch FAR5 coverage test for additional Raw49 root cylinders in the C1=0LA branch."""
import json
import os
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
WORK = Path(sys.argv[1]).resolve()
INDICES = [int(x) for x in sys.argv[2:]] or [1, 3, 4, 6, 7, 8]
CUT = WORK / "cut"
FAR_SOURCE = ROOT.parent / "agent19-raw40-cut" / "farbank.cpp"
FAR_BINARY = WORK / "farbank"
FAR_INPUT = WORK / "child-batch.in"
FAR_OUTPUT = WORK / "child-batch.far"
FAR_LOG = WORK / "child-batch.log"
KNOWN_PROVEN = {
    "1RB---_1RC---_0RD0RC_1LD1RC_------_------",
    "1RB0RC_1RC---_0RD0RA_1LD1RC_------_------",
    "1RB---_1RC0RC_0RD0RB_1LD1RC_------_------",
    "1RB---_1RC---_0RD0RE_1LD1RC_---0RC_------",
    "1RB0LB_1RC0RE_0RD0LA_1LD1RC_1LF0RF_1LA---",
    "1RB0RA_1RC0LE_0RD0LA_1LD1RC_1LC0LF_1LE---",
    "1RB0RA_1RC0RE_0RD0LA_1LD1RC_1LF---_0LF0LD",
    "1RB0RA_1RC1RE_0RD0LA_1LD1RC_1LF---_1LD0LF",
}


def main():
    assert CUT.is_file() and (WORK / "r49.open").is_file()
    root_opens = (WORK / "r49.open").read_text().splitlines()
    assert len(root_opens) == 125
    subprocess.run(["g++", "-std=c++20", "-O3", str(FAR_SOURCE), "-o", str(FAR_BINARY)], check=True)

    entries = []
    by_parent = {}
    for idx in INDICES:
        assert 0 <= idx < len(root_opens) and idx not in (0, 2, 5)
        prefix = WORK / "trials" / str(idx)
        subprocess.run([str(CUT), root_opens[idx], "1000", "32", "6", str(prefix)], check=True,
                       stdout=(WORK / f"child-{idx}-cut.log").open("w"))
        opens_path = Path(str(prefix) + ".open")
        opens = opens_path.read_text().splitlines() if opens_path.exists() else []
        by_parent[idx] = opens
        for local_id, table in enumerate(opens):
            global_id = len(entries)
            entries.append((global_id, idx, local_id, table))

    with FAR_INPUT.open("w") as f:
        for global_id, idx, local_id, table in entries:
            f.write(f"{global_id} {table.replace('_', '')}\n")
    with FAR_INPUT.open("r") as inp, FAR_OUTPUT.open("w") as out, FAR_LOG.open("w") as err:
        subprocess.run([str(FAR_BINARY), "5"], stdin=inp, stdout=out, stderr=err, check=True)

    bank = {}
    for line in FAR_OUTPUT.read_text().splitlines():
        if line.strip():
            global_id_s, code = line.split()
            global_id = int(global_id_s)
            assert 0 <= global_id < len(entries) and global_id not in bank
            bank[global_id] = code

    summaries = []
    covered = []
    for idx in INDICES:
        opens = by_parent[idx]
        local_bank = {}
        missing = []
        proven = []
        for global_id, parent_idx, local_id, table in entries:
            if parent_idx != idx:
                continue
            if global_id in bank:
                local_bank[local_id] = bank[global_id]
            if table in KNOWN_PROVEN:
                proven.append(table)
            if global_id not in bank and table not in KNOWN_PROVEN:
                missing.append(table)
        far_path = WORK / "trials" / f"{idx}.far"
        far_path.write_text("".join(f"{i} {code}\n" for i, code in sorted(local_bank.items())))
        generated = False
        error = ""
        if not missing:
            try:
                subprocess.run([sys.executable, str(WORK / "gen_child.py"), str(idx)],
                               cwd=WORK, check=True, capture_output=True, text=True)
                generated = True
                covered.append(idx)
            except subprocess.CalledProcessError as e:
                error = (e.stderr or e.stdout or str(e))[-2000:]
        summaries.append({
            "index": idx,
            "open_count": len(opens),
            "far_count": len(local_bank),
            "known_proven_count": len(set(proven)),
            "missing_count": len(missing),
            "missing_tables": missing[:30],
            "lean_module_generated": generated,
            "generator_error": error,
        })

    (WORK / "child-batch-summary.json").write_text(json.dumps({
        "indices": INDICES,
        "total_child_open": len(entries),
        "total_far5": len(bank),
        "covered_parent_indices": covered,
        "parents": summaries,
    }, indent=2) + "\n")
    (WORK / "new_children.txt").write_text("".join(f"Raw49C{i}All\n" for i in covered))
    print(json.dumps({"total_child_open": len(entries), "total_far5": len(bank),
                      "covered_parent_indices": covered, "parents": summaries}, sort_keys=True))
    output = os.environ.get("GITHUB_OUTPUT")
    if output:
        with open(output, "a") as f:
            f.write(f"covered_count={len(covered)}\n")
            f.write(f"covered_indices={'-'.join(map(str, covered)) or 'none'}\n")
            f.write(f"child_open_count={len(entries)}\n")
            f.write(f"far5_count={len(bank)}\n")


if __name__ == "__main__":
    main()
