#!/usr/bin/env python3
"""Schedule the existing frozen q0 proof; never change its mathematical claims."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil

IDENTITY = ("source_sha256", "project_imports", "olean_sha256",
            "import_closure_sha256", "module_identity_sha256", "olean_path")

def sha(path):
    h = hashlib.sha256()
    with path.open("rb") as f:
        for block in iter(lambda: f.read(1048576), b""):
            h.update(block)
    return h.hexdigest()

def imports(path):
    return [m for line in path.read_text().splitlines()
            if (match := re.match(r"^import\s+(.+)$", line))
            for m in match.group(1).split()]

def partition(directory, count):
    manifest = json.loads((directory / "manifest.json").read_text())
    stem = "Agent5Q0Coarse" + str(manifest["id"])
    names = set(manifest["modules"])
    assert stem in names and count > 0
    core = {m for m in names if m == stem + "Base" or m.startswith(stem + "Long")}
    graph = {m: imports(directory / (m + ".lean")) for m in names}
    external = {d for ds in graph.values() for d in ds if d not in names}
    sub = names - core - {stem}
    # Schedule terminal submodules independently, even when the parent has
    # one very large direct subtree. The final join checks internal nodes.
    leaves = {m for m in sub if not set(graph[m]) & sub}
    groups = [[] for _ in range(count)]
    loads = [0] * count
    sizes = {m: (directory / (m + ".lean")).stat().st_size for m in sub}
    for m in sorted(leaves, key=lambda m: (-sizes[m], m)):
        i = min(range(count), key=lambda i: (loads[i], i))
        groups[i].append(m)
        loads[i] += sizes[m]
    assert set().union(*(set(g) for g in groups)) == leaves
    (directory / (stem + "Core.lean")).write_text(
        "".join("import " + m + "\n" for m in sorted(core | external)))
    for i, roots in enumerate(groups):
        (directory / ("shard-" + str(i) + ".txt")).write_text(
            "".join(m + "\n" for m in sorted(roots)))
    print(json.dumps({"parent": stem, "bound": manifest["bound"],
                      "remaining": manifest["remaining"],
                      "terminal_submodules": len(leaves),
                      "internal_submodules": len(sub - leaves),
                      "groups": [{"roots": g, "bytes": n}
                                 for g, n in zip(groups, loads)]}))

def read_manifest(folder):
    return json.loads((folder / "manifest.json").read_text())

def thin(core, shard):
    base = {e["module"]: e for e in read_manifest(core)["modules"]}
    for e in read_manifest(shard)["modules"]:
        b = base.get(e["module"])
        if b is None:
            continue
        assert all(e[k] == b[k] for k in IDENTITY), e["module"]
        obj = shard / e["olean_path"]
        assert sha(obj) == e["olean_sha256"]
        obj.unlink()

def merge(core, shards, output):
    output.mkdir(parents=True, exist_ok=False)
    base = read_manifest(core)
    merged = {}
    for folder in [core, *shards]:
        data = read_manifest(folder)
        assert data["schema_version"] == base["schema_version"] == 1
        assert data["lean_version"] == base["lean_version"]
        assert data["lean_binary"]["sha256"] == base["lean_binary"]["sha256"]
        assert data["proof_source_revision"] == base["proof_source_revision"]
        for e in data["modules"]:
            m = e["module"]
            rel = Path(e["olean_path"])
            assert not rel.is_absolute() and ".." not in rel.parts
            if m in merged:
                assert all(e[k] == merged[m][k] for k in IDENTITY), m
            else:
                merged[m] = e
            obj = folder / rel
            dst = output / rel
            if obj.exists():
                assert sha(obj) == e["olean_sha256"], m
                if not dst.exists():
                    dst.parent.mkdir(parents=True, exist_ok=True)
                    shutil.copy2(obj, dst)
            assert dst.is_file() and sha(dst) == e["olean_sha256"], m
    for e in merged.values():
        assert set(e["project_imports"]) <= set(merged), e["module"]
    base["modules"] = list(merged.values())
    base["module_count"] = len(merged)
    base["label"] = "q0 sharded precompiled union; not the final Cover"
    (output / "manifest.json").write_text(json.dumps(base, indent=2) + "\n")
    print("Merged", len(merged), "modules with exact matching identities")

def main():
    p = argparse.ArgumentParser()
    sub = p.add_subparsers(dest="mode", required=True)
    q = sub.add_parser("partition")
    q.add_argument("directory", type=Path)
    q.add_argument("count", type=int)
    q = sub.add_parser("thin")
    q.add_argument("core", type=Path)
    q.add_argument("shard", type=Path)
    q = sub.add_parser("merge")
    q.add_argument("core", type=Path)
    q.add_argument("output", type=Path)
    q.add_argument("shards", type=Path, nargs="*")
    a = p.parse_args()
    if a.mode == "partition":
        partition(a.directory, a.count)
    elif a.mode == "thin":
        thin(a.core, a.shard)
    else:
        merge(a.core, a.shards, a.output)

if __name__ == "__main__":
    main()
