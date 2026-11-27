#!/usr/bin/env python3
"""Shard Raw61/Raw63/Raw67's existing complete witness tree with the proven prefix checker."""
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

PARENTS = {
    "61": ("1RB---_1RC0LA_0RD---_1LD1RE_---0LB_------", "1962", "Agent31Raw61"),
    "63": ("1RB---_1RC1LA_0RD---_1LD1RE_---0LB_------", "358", "Agent2Raw63"),
    "67": ("1RB---_1RC1LB_0RD---_1LD1RE_---0LB_------", "808", "Agent10Raw67"),
}


def digest(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def run(path, *args):
    subprocess.run([sys.executable, str(ROOT / path), *map(str, args)], check=True)


def prepare(generated, raw):
    generated.mkdir(parents=True, exist_ok=False)
    run("im-results/agent13-coverage/unpack.py")
    if raw == "61":
        for emitter in ("tripling", "recursive_unary", "residue_unary", "multiphase", "d120", "language353", "a244"):
            run(f"im-results/agent48-raw61/emit_{emitter}.py")
        for name in ("All", "Tripling", "RecursiveUnary", "ResidueUnary", "Multiphase", "D120", "Language353", "A244"):
            shutil.copy2(HERE.parent / "agent48-raw61" / f"Agent48Raw61{name}.lean", generated)
    elif raw == "63":
        run("im-results/agent48-raw63-counter/emit_counter.py")
        shutil.copy2(HERE.parent / "agent48-raw63-counter/Agent48Raw63Counter.lean", generated)
    run("im-results/agent10-tnf-multipump/generate.py", raw)
    run("im-results/agent48-prefix-audit/switch_generated_checks.py", raw)
    source = HERE.parent / "agent10-tnf-multipump"
    kids = [f"Raw{raw}Kid{i:02}" for i in range(24)]
    for name in [f"Raw{raw}{n}" for n in ("Base", "Pumps", "Data")] + kids:
        shutil.copy2(source / (name + ".lean"), generated)
    if raw == "67":
        for name in ("Raw67Recursive", "Raw67Attainment", "Raw67ParentCover"):
            shutil.copy2(source / (name + ".lean"), generated)
    else:
        shutil.copy2(HERE / f"Raw{raw}ParentCover.lean", generated)
    groups = [[] for _ in range(6)]
    loads = [0] * len(groups)
    for name in sorted(kids, key=lambda n: -(generated / (n + ".lean")).stat().st_size):
        i = min(range(len(groups)), key=loads.__getitem__)
        groups[i].append(name)
        loads[i] += (generated / (name + ".lean")).stat().st_size
    assert sorted(sum(groups, [])) == sorted(kids)
    (generated / "schedule.json").write_text(json.dumps({
        "branch": raw, "final": f"Raw{raw}ParentCover", "groups": groups,
        "sources": {p.name: digest(p) for p in sorted(generated.glob("*.lean"))},
    }, indent=2) + "\n")
    print(f"Raw{raw} shard loads:", loads, flush=True)


def compile_roots(roots, generated, core, work, raw, final=False):
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
        parent, bound, namespace = PARENTS[raw]
        args += ["--label", f"raw{raw}-prefix-parent", "--theorem", f"BB6.{namespace}.literal_cover",
                 "--parent-table", parent, "--weighted-bound", bound,
                 "--artifact-name", f"raw{raw}-prefix-parent-certified",
                 "--provenance-input", str(HERE / "shard.py"),
                 "--provenance-input", str(generated / "schedule.json")]
    subprocess.run(args + [str(root) for root in roots], check=True)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("action", choices=("prepare", "core", "shard", "assemble"))
    ap.add_argument("--raw", choices=PARENTS, default="63")
    ap.add_argument("--generated", required=True, type=Path)
    ap.add_argument("--core", type=Path)
    ap.add_argument("--work", type=Path)
    ap.add_argument("--shard", type=int)
    ap.add_argument("--inputs", type=Path)
    ap.add_argument("--merged", type=Path)
    a = ap.parse_args()
    g = a.generated.resolve()
    if a.action == "prepare":
        prepare(g, a.raw)
        return
    s = schedule(g)
    assert s["branch"] == a.raw
    if a.action == "core":
        compile_roots([g / f"Raw{a.raw}Base.lean",
                       HERE.parent / "agent48-prefix-audit/ZipPrefixAudit.lean"],
                      g, a.core, a.work, a.raw)
    elif a.action == "shard":
        compile_roots([g / (name + ".lean") for name in s["groups"][a.shard]],
                      g, a.core, a.work, a.raw)
    else:
        merge(a.inputs, a.merged, g, prefix=f"raw{a.raw}-prefix")
        compile_roots([g / (s["final"] + ".lean")], g, a.merged, a.work, a.raw, final=True)


if __name__ == "__main__":
    main()
