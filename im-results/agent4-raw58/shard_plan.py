#!/usr/bin/env python3
"""Disjoint Raw58 source-proof shards; all 24 moves per heavy child retained."""
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
REPO = ROOT.parents[1]
CONFIG = ROOT / "shard_groups.json"
GROUPS = json.loads(CONFIG.read_text())["groups"]


def run(*args):
    subprocess.run([str(x) for x in args], cwd=REPO, check=True)


def plan():
    expected = {"Raw58MoreCut2", "Raw58LEData", "Raw58RFData", "Raw58LE1Data"}
    expected |= {f"Raw58{k}Kid{i:02}" for k in ("LF", "LF1") for i in range(24)}
    roots = [x for g in GROUPS.values() for x in g]
    if len(roots) != len(set(roots)) or set(roots) != expected:
        raise ValueError("missing, extra or duplicate root in shard plan")


def prepare(group, work):
    roots = GROUPS[group]
    work.mkdir(parents=True, exist_ok=True)
    py = sys.executable
    run(py, REPO / "im-results/agent13-coverage/unpack.py")
    run(py, REPO / "im-results/agent31-three-hole-tnf/generate_sweeps.py")
    run(py, REPO / "im-results/agent31-three-hole-tnf/generate_four_hole.py")
    if group == "cut":
        run(py, ROOT / "generate.py")
        run(py, ROOT / "generate_more.py", "RD", "LC1", "RE1", "RC", "LA1", "LB1", "RF1")
        theorems = ["BB6.Agent4Raw58MoreCut2.parent_dichotomy"]
    else:
        child = group.split("-")[0].upper()
        run(py, ROOT / "generate_more.py", child)
        extra = ["--late-proofs", ROOT / "lf1_late_proofs.json"] if child == "LF1" else []
        run(py, REPO / "im-results/agent10-tnf-multipump/chunk_checks.py",
            ROOT, f"Raw58{child}", "--limit", "180", *extra)
        if child in ("LF", "LF1"):
            theorems = []
            for root in roots:
                p = ROOT / (root + ".lean")
                idx = root[-2:]
                with p.open("a") as f:
                    f.write(f"\n#print axioms BB6.Agent4Raw58{child}.check{idx}\n")
                theorems.append(f"BB6.Agent4Raw58{child}.check{idx}")
            # The assembly source is not compiled in these shards; all three
            # independently generated copies must match before final checking.
            (work / f"Raw58{child}Data.lean").write_bytes(
                (ROOT / f"Raw58{child}Data.lean").read_bytes())
        else:
            theorems = [f"BB6.Agent4Raw58{child}.all_completions"]
    (work / "roots.txt").write_text("\n".join(str(ROOT / (x + ".lean")) for x in roots) + "\n")
    (work / "theorems.txt").write_text("\n".join(theorems) + "\n")


def fetch_pinned(pins_path, downloads):
    pins = json.loads(pins_path.read_text())
    if set(pins) != set(GROUPS):
        raise ValueError("pins must cover the exact shard plan")
    downloads.mkdir(parents=True, exist_ok=False)
    for group, p in pins.items():
        revision = p["revision"]
        run_id = str(p["run_id"])
        if not re.fullmatch(r"[0-9a-f]{40}", revision) or not run_id.isdecimal():
            raise ValueError(f"invalid pin for {group}")
        run("git", "cat-file", "-e", revision + "^{commit}")
        artifact = f"raw58-shard-{group}"
        run("gh", "run", "download", run_id, "--name", artifact, "--dir", downloads / artifact)


def restore_data(downloads):
    for child in ("LF", "LF1"):
        name = f"Raw58{child}Data.lean"
        copies = [(downloads / f"raw58-shard-{child.lower()}-{suffix}" / name).read_bytes()
                  for suffix in "abc"]
        if any(c != copies[0] for c in copies[1:]):
            raise ValueError(f"inconsistent assembly source {name}")
        target = ROOT / name
        if target.exists() and target.read_bytes() != copies[0]:
            raise ValueError(f"checkout conflicts with {name}")
        target.write_bytes(copies[0])


if __name__ == "__main__":
    plan()
    op, *args = sys.argv[1:]
    if op == "prepare":
        prepare(args[0], Path(args[1]))
    elif op == "fetch":
        fetch_pinned(Path(args[0]), Path(args[1]))
    elif op == "restore-data":
        restore_data(Path(args[0]))
    elif op == "plan":
        print(json.dumps(GROUPS, indent=2))
    else:
        raise ValueError(op)
