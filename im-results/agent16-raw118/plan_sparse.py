#!/usr/bin/env python3
"""Partition the exact Raw118 sparse certificate imports into bounded CI groups."""
from pathlib import Path
import json
import re
import sys

HERE = Path(__file__).resolve().parent


def plan(root: Path, work: Path, count: int = 12) -> dict:
    manifest = json.loads((root / "Raw118Sparse.json").read_text())
    ng = {int(i): (int(v[0]), int(v[1])) for i, v in json.loads(
        (work / "candidates.json").read_text())["ngram"].items()}
    assert len(ng) == 679 and sum(n for _, n in ng.values()) == 635684
    assert set(manifest["indices"]) == set(ng)
    roots = manifest["modules"]
    assert len(set(roots)) == len(roots)
    expected_imports = [f"import {name}" for name in roots]
    assert (root / "Raw118Sparse.lean").read_text().splitlines() == expected_imports
    weights = []
    seen = set()
    for name in roots:
        source = (root / f"{name}.lean").read_text()
        indices = {int(i) for i in re.findall(
            r"^namespace BB6\.Agent47SparseNGram\.Raw118Sparse(\d+)$", source, re.M)}
        assert indices and indices <= set(ng) and not (seen & indices), (name, indices)
        seen |= indices
        weights.append((sum((ng[i][0] + 1) * ng[i][1] for i in indices), name, indices))
    assert seen == set(ng)
    assert 0 < count <= len(roots)
    groups = [[] for _ in range(count)]
    costs = [0] * count
    for item in sorted(weights, key=lambda x: (-x[0], x[1])):
        j = min(range(count), key=lambda k: (costs[k], k))
        groups[j].append(item)
        costs[j] += item[0]
    config = {"artifact_prefix": "raw118-sparse-shard", "groups": {}}
    metadata = []
    for j, items in enumerate(groups):
        name = f"Raw118SparseShard{j:02}"
        gid = f"{j:02}"
        assert items
        members = sorted(name for _, name, _ in items)
        indices = sorted(i for _, _, ids in items for i in ids)
        (root / f"{name}.lean").write_text("\n".join(f"import {m}" for m in members) + "\n")
        config["groups"][gid] = [name]
        metadata.append({"group": gid, "module": name, "modules": members, "indices": indices,
                         "states": sum(ng[i][1] for i in indices), "cost": costs[j]})
    assert sorted(i for group in metadata for i in group["indices"]) == sorted(ng)
    assert sum(g["states"] for g in metadata) == 635684
    config["metadata"] = metadata
    (root / "Raw118SparsePlan.json").write_text(json.dumps(config, indent=2) + "\n")
    for group in metadata:
        print(f"{group['module']}: {len(group['indices'])} leaves, {group['states']} states, cost {group['cost']}")
    return config


if __name__ == "__main__":
    plan(HERE, Path(sys.argv[1]))
