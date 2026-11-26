#!/usr/bin/env python3
"""Build independently reusable, source-checked Raw57 proof dependency cuts."""
from __future__ import annotations

import argparse
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
AGENT1 = "im-results/agent1-raw57"
AGENT6 = "im-results/agent6-raw57-ra"

EARLY = ("0RB", "0RC", "1RB", "1RC", "1RE", "0RE", "0RF")
MIDDLE_AGENT1 = ("0LB", "0LC", "0LD", "1RA", "1RF")
RESIDUAL_A = ("1LA", "1LB", "1LE")
RESIDUAL_B = ("0LF", "1LF")
EARLY_ROOTS = (
    f"{AGENT6}/Raw57RAData.lean",
    *(f"{AGENT6}/Raw57{c[1:]}{c[0]}Data.lean" for c in EARLY),
    f"{AGENT1}/Raw57ParentBridge.lean",
)
MIDDLE_ROOTS = (
    *(f"{AGENT1}/Raw57{c[1:]}{c[0]}Data.lean" for c in MIDDLE_AGENT1),
    f"{AGENT6}/Raw57LC1Data.lean",
)
RESIDUAL_A_ROOTS = tuple(
    f"{AGENT1}/Raw57{c[1:]}{c[0]}Data.lean" for c in RESIDUAL_A
)
RESIDUAL_B_ROOTS = tuple(
    f"{AGENT1}/Raw57{c[1:]}{c[0]}Data.lean" for c in RESIDUAL_B
)

def run(args: list[str]) -> None:
    print("+", " ".join(args), flush=True)
    subprocess.run(args, cwd=ROOT, check=True)

def generate(group: str) -> tuple[list[str], list[str]]:
    run([sys.executable, f"{AGENT6}/generate.py"])
    if group == "early":
        for child in EARLY:
            run([sys.executable, f"{AGENT6}/generate_sibling.py", child])
        return list(EARLY_ROOTS), [
            f"{AGENT6}/generate.py", f"{AGENT6}/generate_sibling.py",
            f"{AGENT6}/siblings.json", f"{AGENT1}/Raw57ParentBridge.lean",
            f"{AGENT6}/Raw57Easy.lean",
        ]
    if group == "middle":
        for child in MIDDLE_AGENT1:
            run([sys.executable, f"{AGENT1}/generate_sibling.py", child])
        run([sys.executable, f"{AGENT6}/generate_sibling.py", "1LC"])
        return list(MIDDLE_ROOTS), [
            f"{AGENT1}/generate_sibling.py", f"{AGENT1}/siblings.json",
            f"{AGENT6}/generate.py", f"{AGENT6}/generate_sibling.py",
            f"{AGENT6}/siblings.json",
        ]
    if group == "residual-a":
        for child in RESIDUAL_A:
            run([sys.executable, f"{AGENT1}/generate_sibling.py", child])
        return list(RESIDUAL_A_ROOTS), [
            f"{AGENT1}/generate_sibling.py", f"{AGENT1}/siblings.json",
            f"{AGENT1}/Raw57ParentBridge.lean",
        ]
    if group == "residual-b":
        run([sys.executable, f"{AGENT1}/m882885_certificate.py"])
        for child in RESIDUAL_B:
            run([sys.executable, f"{AGENT1}/generate_sibling.py", child])
        return list(RESIDUAL_B_ROOTS), [
            f"{AGENT1}/generate_sibling.py", f"{AGENT1}/siblings.json",
            f"{AGENT1}/m882885_certificate.py",
        ]
    raise ValueError(f"unknown Raw57 cut group: {group}")

def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("group", choices=("early", "middle", "residual-a", "residual-b"))
    parser.add_argument("--jobs", type=int, default=4)
    args = parser.parse_args()

    roots, provenance = generate(args.group)
    # Include all tracked JSON specifications consumed transitively by these
    # deterministic generators; the module manifest separately hashes sources.
    tracked = subprocess.run(
        ["git", "ls-files", f"{AGENT1}/*.json", f"{AGENT6}/*.json"],
        cwd=ROOT, check=True, capture_output=True, text=True,
    ).stdout.splitlines()
    provenance.extend(p for p in tracked if p not in provenance)

    artifact_root = Path("/tmp") / f"raw57-cut-{args.group}"
    shutil.rmtree(artifact_root, ignore_errors=True)
    precompiled = artifact_root / "precompiled"
    precompiled.mkdir(parents=True)
    manifest = artifact_root / "manifest.json"
    log = artifact_root / "compile.log"
    command = [
        sys.executable, "tools/lean_compile_closure.py",
        "--workdir", str(precompiled),
        "--jobs", str(args.jobs),
        "--manifest", str(manifest),
        "--label", f"Raw57 {args.group} reusable proof cut",
        "--artifact-name", f"raw57-cut-{args.group}",
    ]
    for path in sorted(set(provenance)):
        command.extend(["--provenance-input", path])
    command.extend(roots)
    print("ROOTS:", *roots, sep="\n  ", flush=True)
    print("PROVENANCE:", *sorted(set(provenance)), sep="\n  ", flush=True)
    print("+", " ".join(command), flush=True)
    with log.open("w", encoding="utf-8") as output:
        completed = subprocess.run(
            command, cwd=ROOT, check=False, stdout=output, stderr=subprocess.STDOUT
        )
    tail = log.read_text(encoding="utf-8", errors="replace").splitlines()[-100:]
    print("\n".join(tail), flush=True)
    print(
        f"[raw57-cut-{args.group}] roots={len(roots)} manifest={manifest} "
        f"olean_count={sum(1 for _ in precompiled.rglob('*.olean'))} "
        f"returncode={completed.returncode}",
        flush=True,
    )
    if completed.returncode:
        raise SystemExit(completed.returncode)

if __name__ == "__main__":
    main()
