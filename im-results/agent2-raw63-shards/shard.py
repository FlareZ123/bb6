#!/usr/bin/env python3
"""Shard Raw63's existing complete witness tree with the proven prefix checker."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(HERE.parent / "agent32-raw124-0le"))
from legacy_shards import merge, schedule

PREFIX = "raw63-prefix"
PARENT = "1RB---_1RC1LA_0RD---_1LD1RE_---0LB_------"


def digest(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def run(path, *args):
    subprocess.run([sys.executable, str(ROOT / path), *map(str, args)], check=True)


def prepare(generated):
    generated.mkdir(parents=True, exist_ok=False)
    run("im-results/agent13-coverage/unpack.py")
    run("im-results/agent48-raw63-counter/emit_counter.py")
    run("im-results/agent10-tnf-multipump/generate.py", "63")
    run("im-results/agent48-prefix-audit/switch_generated_checks.py", "63")
    source = HERE.parent / "agent10-tnf-multipump"
    kids = [f"Raw63Kid{i:02}" for i in range(24)]
    for name in ["Raw63Base", "Raw63Pumps", "Raw63Data", *kids]:
        shutil.copy2(source / (name + ".lean"), generated)
    shutil.copy2(HERE.parent / "agent48-raw63-counter/Agent48Raw63Counter.lean", generated)
    shutil.copy2(HERE / "Raw63ParentCover.lean", generated)
    groups = [[] for _ in range(6)]
    loads = [0] * len(groups)
    for name in sorted(kids, key=lambda n: -(generated / (n + ".lean")).stat().st_size):
        i = min(range(len(groups)), key=loads.__getitem__)
        groups[i].append(name)
        loads[i] += (generated / (name + ".lean")).stat().st_size
    assert sorted(sum(groups, [])) == sorted(kids)
    (generated / "schedule.json").write_text(json.dumps({
        "branch": "63", "final": "Raw63ParentCover", "groups": groups,
        "sources": {p.name: digest(p) for p in sorted(generated.glob("*.lean"))},
    }, indent=2) + "\n")
    print("Raw63 shard loads:", loads, flush=True)


def compile_roots(roots, generated, core, work, final=False):
    args = [sys.executable, str(ROOT / "tools/lean_compile_closure.py"),
            "--source-root", str(generated), "--source-root", str(core),
            "--workdir", str(work), "--jobs", "2",
            "--precompiled-manifest", str(core / "manifest.json"),
            "--precompiled-dir", str(core), "--manifest", str(work / "manifest.json")]
    overrides = {}
    for base in (core, generated):
        for p in sorted(base.rglob("*.lean")):
            mod = ".".join(p.relative_to(base).with_suffix("").parts)
            if mod in overrides:
                assert digest(p) == digest(overrides[mod]), mod
            overrides[mod] = p
    for mod, p in sorted(overrides.items()):
        args += ["--override", f"{mod}={p}"]
    if final:
        args += ["--label", "raw63-prefix-parent", "--theorem", "BB6.Agent2Raw63.literal_cover",
                 "--parent-table", PARENT, "--weighted-bound", "358",
                 "--artifact-name", "raw63-prefix-parent-certified",
                 "--provenance-input", str(HERE / "shard.py"),
                 "--provenance-input", str(generated / "schedule.json")]
    subprocess.run(args + [str(root) for root in roots], check=True)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("action", choices=("prepare", "core", "shard", "assemble"))
    ap.add_argument("--generated", required=True, type=Path)
    ap.add_argument("--core", type=Path)
    ap.add_argument("--work", type=Path)
    ap.add_argument("--shard", type=int)
    ap.add_argument("--inputs", type=Path)
    ap.add_argument("--merged", type=Path)
    a = ap.parse_args()
    g = a.generated.resolve()
    if a.action == "prepare":
        prepare(g)
        return
    s = schedule(g)
    if a.action == "core":
        compile_roots([g / "Raw63Base.lean",
                       HERE.parent / "agent48-prefix-audit/ZipPrefixAudit.lean"],
                      g, a.core, a.work)
    elif a.action == "shard":
        compile_roots([g / (name + ".lean") for name in s["groups"][a.shard]],
                      g, a.core, a.work)
    else:
        merge(a.inputs, a.merged, g, prefix=PREFIX)
        compile_roots([g / (s["final"] + ".lean")], g, a.merged, a.work, final=True)


if __name__ == "__main__":
    main()
