#!/usr/bin/env python3
"""Partition an existing Raw42 eight-shard assembly into smaller source-closed jobs.

This is strictly a scheduling transformation: no certificate, transition table,
root, checker, or bound is weakened. The original 8 groups are split into
subgroups, and merge_shards.py checks their exact union and source identity.
"""
import argparse
import json
from pathlib import Path


def plan(generated: Path, branch: str, count: int):
    cfg = json.loads((generated / "shards.json").read_text())
    assert set(cfg["groups"]) == {str(k) for k in range(8)}
    assert count >= 2
    all_roots = [r for rs in cfg["groups"].values() for r in rs]
    assert len(all_roots) == len(set(all_roots)) and all_roots

    cache = {}
    visiting = set()

    def closure(mod):
        if mod in cache:
            return cache[mod]
        if mod in visiting:
            raise ValueError("generated import cycle: " + mod)
        visiting.add(mod)
        src = generated / (mod + ".lean")
        if not src.is_file():
            visiting.remove(mod)
            return frozenset()
        deps = set()
        for line in src.read_text().splitlines():
            if line.startswith("import "):
                for dep in line.split()[1:]:
                    deps.update(closure(dep))
        visiting.remove(mod)
        cache[mod] = frozenset({mod} | deps)
        return cache[mod]

    def weight(modules):
        return sum((generated / (m + ".lean")).stat().st_size for m in modules)

    out = {}
    profiles = {}
    for group in sorted(cfg["groups"], key=int):
        roots = cfg["groups"][group]
        assert roots
        n = min(count, len(roots))
        groups = [[] for _ in range(n)]
        unions = [set() for _ in range(n)]
        for r in sorted(roots, key=lambda r: (-weight(closure(r)), r)):
            deps = set(closure(r))
            i = min(range(n), key=lambda j: (weight(unions[j] | deps), len(groups[j]), j))
            groups[i].append(r)
            unions[i].update(deps)
        assert all(groups)
        for i, rs in enumerate(groups):
            key = "g" + group + "p" + str(i)
            out[key] = sorted(rs)
            profiles[key] = {"original_group": group, "closure_bytes": weight(unions[i]),
                             "module_count": len(unions[i]), "root_count": len(rs)}

    flattened = [r for rs in out.values() for r in rs]
    assert len(flattened) == len(all_roots)
    assert set(flattened) == set(all_roots)
    return {
        "artifact_prefix": "raw42-split-" + branch,
        "groups": out,
        "original_artifact_prefix": cfg["artifact_prefix"],
        "original_groups": cfg["groups"],
        "part_profiles": profiles,
        "parent_branch": branch,
        "allow_mixed_revisions": True,
    }


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("generated", type=Path)
    ap.add_argument("branch", choices=["0LE", "1LE", "1RE"])
    ap.add_argument("out", type=Path)
    ap.add_argument("--parts-per-group", type=int, default=4)
    a = ap.parse_args()
    p = plan(a.generated, a.branch, a.parts_per_group)
    a.out.write_text(json.dumps(p, indent=2, sort_keys=True) + "\n")
    print("Exact original roots:", len({r for roots in p["groups"].values() for r in roots}))
    print("Dependency-closed parts:", len(p["groups"]))
    print("PARTS=" + json.dumps(list(p["groups"])))


if __name__ == "__main__":
    main()
