#!/usr/bin/env python3
"""Plan bounded, dependency-closed Raw123 compilation with one shared core."""
from collections import Counter
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tarfile

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
PLAN = HERE / "generated" / "shard-plan.json"
PREFIX = "A25Raw123Shard_"
TARGET = "A25Raw123Data"
ARTIFACT = "raw123-shard"
sys.path.insert(0, str(REPO / "tools"))


def closure(graph, roots):
    reached = set()
    pending = list(roots)
    while pending:
        name = pending.pop()
        if name not in reached:
            reached.add(name)
            pending.extend(graph[name])
    return reached


def make_groups(graph, weights, count=24):
    leaves = sorted(n for n, deps in graph.items()
                    if n.startswith(PREFIX)
                    and not any(d.startswith(PREFIX) for d in deps))
    if not leaves:
        raise ValueError("no generated leaf-shard roots")
    closures = {n: closure(graph, [n]) for n in leaves}
    multiplicities = Counter(d for c in closures.values() for d in c)
    # Apportion shared cost; greedily balance by deterministic LPT.
    costs = {n: sum(max(1, weights[d] // multiplicities[d]) for d in c)
             for n, c in closures.items()}
    bins = [[] for _ in range(min(count, len(leaves)))]
    loads = [0] * len(bins)
    for n in sorted(leaves, key=lambda n: (-costs[n], n)):
        i = min(range(len(bins)), key=lambda i: (loads[i], i))
        bins[i].append(n)
        loads[i] += costs[n]
    groups = {f"{i:02d}": sorted(b) for i, b in enumerate(bins) if b}
    shared_counts = Counter(d for roots in groups.values()
                            for d in closure(graph, roots))
    shared = {d for d, n in shared_counts.items() if n > 1}
    shared_roots = sorted(shared - {d for n in shared for d in graph[n]})
    if not shared_roots:
        raise ValueError("expected common Raw123 checker dependencies")
    assert closure(graph, shared_roots) == shared
    assert sorted(n for roots in groups.values() for n in roots) == leaves
    return groups, shared_roots


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def prepare(bundle):
    import lean_compile_closure as lc
    spec = json.loads((HERE / "spec.json").read_text())
    assert not spec["unresolved"] and spec["weightedTarget"] == 9109
    index = lc.module_index()
    sources, graph = {}, {}
    pending = [TARGET]
    while pending:
        name = pending.pop()
        if name in sources:
            continue
        path = lc.resolve_source(name, index)
        sources[name] = path
        graph[name] = lc.parse_imports(path)
        pending.extend(graph[name])
    groups, core_roots = make_groups(
        graph, {n: p.stat().st_size for n, p in sources.items()})
    plan = {
        "artifact_prefix": ARTIFACT,
        "groups": groups,
        "core_roots": core_roots,
        "graph": graph,
        "sources": {n: {"path": str(p.relative_to(REPO)), "sha256": sha(p)}
                    for n, p in sorted(sources.items())},
    }
    PLAN.write_text(json.dumps(plan, indent=2, sort_keys=True) + "\n")
    with tarfile.open(bundle, "w:gz") as archive:
        for p in sorted(set(sources.values()) | {PLAN}):
            archive.add(p, arcname=str(p.relative_to(REPO)), recursive=False)
    print(f"Prepared {len(sources)} modules; {len(groups)} groups; "
          f"{len(closure(graph, core_roots))} common modules")


def read_plan():
    plan = json.loads(PLAN.read_text())
    for info in plan["sources"].values():
        if sha(REPO / info["path"]) != info["sha256"]:
            raise ValueError(f"source bundle mismatch: {info['path']}")
    return plan


def compile_group(group, work, precompiled=None):
    plan = read_plan()
    graph = plan["graph"]
    if group == "core":
        roots = plan["core_roots"]
        artifact = "raw123-core"
    elif group == "parent":
        roots = [TARGET]
        artifact = "raw123-parent-proof"
    else:
        roots = plan["groups"][group]
        artifact = f"{ARTIFACT}-{group}"
    argv = [
        sys.executable, "tools/lean_compile_closure.py",
        "--workdir", str(work), "--jobs", "4",
        "--manifest", str(work / "manifest.json"),
        "--label", artifact, "--artifact-name", artifact,
    ]
    for path in (
        "im-results/agent25-raw123/generate.py",
        "im-results/agent25-raw123/spec.json",
        "im-results/agent25-raw123/Raw123RecursiveBatch.lean.zlib.b64",
        "im-results/agent25-raw123/Raw1235465.lean.xz.b64",
        "im-results/agent25-raw123/unpack5465.py",
        "im-results/agent25-raw123/plan_shards.py",
        "im-results/agent2-tnf-raw99/enumerate.cpp",
        "im-results/agent8-tnf-six/bank.cpp",
        "im-results/agent1-ngram/ngram.cpp",
        "im-results/agent1-ngram/emit_ngram.py",
        "im-results/agent32-raw59/ngram_asym.cpp",
        "im-results/agent32-raw59/generate_asym.py",
        "im-results/agent31-three-hole-tnf/generate_sweeps.py",
        "im-results/agent31-three-hole-tnf/generate_four_hole.py",
        "im-results/agent10-tnf-multipump/multi.py",
        "im-results/agent16-raw118/bidfa_emit.py",
        "im-results/agent13-coverage/unpack.py",
        "im-results/agent13-coverage/BB6Coverage.lean.xz.b64",
        str(PLAN.relative_to(REPO)),
        "im-results/agent4-raw109/merge_shards.py",
        "im-results/agent4-raw109/audit_axioms.py",
        "tools/lean_compile_closure.py",
        ".github/workflows/agent25-raw123.yml",
    ):
        argv.extend(["--provenance-input", path])
    if precompiled is not None:
        argv.extend(["--precompiled-dir", str(precompiled),
                     "--precompiled-manifest", str(precompiled / "manifest.json")])
    if group == "parent":
        argv.extend([
            "--theorem", "BB6.Agent25Raw123.all123",
            "--parent-table", "1RB---_1RC---_0RD---_1LD1RE_---0RF_------",
            "--weighted-bound", "9109",
        ])
    argv.extend(plan["sources"][n]["path"] for n in roots)
    subprocess.run(argv, cwd=REPO, check=True)
    if precompiled is not None:
        meta = json.loads((work / "manifest.json").read_text())["precompiled_core"]
        actual = set(meta["reused_modules"])
        expected = (set(n for rs in plan["groups"].values() for n in rs)
                    if group == "parent"
                    else closure(graph, roots) & closure(graph, plan["core_roots"]))
        if not expected <= actual:
            raise ValueError(f"missing reused modules: {sorted(expected - actual)}")


if __name__ == "__main__":
    mode = sys.argv[1]
    if mode == "prepare":
        prepare(Path(sys.argv[2]))
    elif mode == "matrix":
        print(json.dumps({"group": sorted(read_plan()["groups"])}, separators=(",", ":")))
    elif mode == "compile":
        compile_group(sys.argv[2], Path(sys.argv[3]),
                      Path(sys.argv[4]) if len(sys.argv) > 4 else None)
    else:
        raise SystemExit(f"unknown mode {mode}")
