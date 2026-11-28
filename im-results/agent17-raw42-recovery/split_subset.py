#!/usr/bin/env python3
"""Split an exact root subset from an existing Raw42 split plan.

Used to recover only a failed logical shard while preserving the already
accepted sibling artifacts.  Roots are unchanged; each output part is a
dependency-closed source subset, and merge_shards.py authenticates their union.
"""
import json
import sys
from pathlib import Path

generated = Path(sys.argv[1]).resolve()
source_plan = json.loads(Path(sys.argv[2]).read_text())
source_part = sys.argv[3]
requested_parts = int(sys.argv[4])
artifact_prefix = sys.argv[5]
output = Path(sys.argv[6]).resolve()

roots = list(source_plan["groups"][source_part])
if not roots:
    raise ValueError(f"source part {source_part} has no roots")
parts = min(requested_parts, len(roots))
if parts < 2:
    raise ValueError("subset cannot be split")

def imports(module):
    source = generated / (module + ".lean")
    if not source.is_file():
        return []
    out = []
    for line in source.read_text().splitlines():
        if line.startswith("import "):
            out.extend(line.split()[1:])
    return out

memo = {}
def closure(module):
    if module in memo:
        return memo[module]
    source = generated / (module + ".lean")
    if not source.is_file():
        memo[module] = frozenset()
        return memo[module]
    seen = {module}
    for dep in imports(module):
        seen.update(closure(dep))
    memo[module] = frozenset(seen)
    return memo[module]

def bytes_of(modules):
    return sum((generated / (m + ".lean")).stat().st_size for m in modules)

root_closures = {r: closure(r) for r in roots}
order = sorted(roots, key=lambda r: (-bytes_of(root_closures[r]), r))
groups = [[] for _ in range(parts)]
unions = [set() for _ in range(parts)]
for root in order:
    rc = set(root_closures[root])
    target = min(
        range(parts),
        key=lambda i: (bytes_of(unions[i] | rc), len(groups[i]), i),
    )
    groups[target].append(root)
    unions[target].update(rc)

plan = {
    "artifact_prefix": artifact_prefix,
    "groups": {str(i): sorted(xs) for i, xs in enumerate(groups)},
    "allow_mixed_revisions": True,
    "source_part": source_part,
    "source_roots": sorted(roots),
    "part_generated_closure_bytes": {
        str(i): bytes_of(unions[i]) for i in range(parts)
    },
    "part_generated_module_counts": {
        str(i): len(unions[i]) for i in range(parts)
    },
}
if any(not xs for xs in plan["groups"].values()):
    raise ValueError("split produced empty part")
output.write_text(json.dumps(plan, indent=2, sort_keys=True) + "\n")
print(json.dumps(plan, indent=2, sort_keys=True))
