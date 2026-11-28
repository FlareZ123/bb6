#!/usr/bin/env python3
"""Split one oversized Raw42 recovery shard into dependency-closed subshards.

The generated Raw42 sources already define independent bottom-level roots.
This planner preserves those roots exactly, estimates each root's generated
import closure, and greedily balances the roots across a requested number of
parts.  The existing merge_shards.py later authenticates and reunites the
parts before the final child Cover is recompiled.
"""
import json
import sys
from pathlib import Path

generated = Path(sys.argv[1]).resolve()
group = sys.argv[2]
requested_parts = int(sys.argv[3])
artifact_prefix = sys.argv[4]
output = Path(sys.argv[5]).resolve()

cfg = json.loads((generated / "shards.json").read_text())
roots = list(cfg["groups"][group])
if not roots:
    raise ValueError(f"group {group} has no roots")
parts = min(requested_parts, len(roots))
if parts < 2:
    raise ValueError(f"group {group} has only {len(roots)} root(s); cannot split")

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

if any(not xs for xs in groups):
    raise ValueError("split produced an empty part")

plan = {
    "artifact_prefix": artifact_prefix,
    "groups": {str(i): sorted(xs) for i, xs in enumerate(groups)},
    "allow_mixed_revisions": True,
    "source_group": group,
    "source_roots": sorted(roots),
    "part_generated_closure_bytes": {
        str(i): bytes_of(unions[i]) for i in range(parts)
    },
    "part_generated_module_counts": {
        str(i): len(unions[i]) for i in range(parts)
    },
}
output.write_text(json.dumps(plan, indent=2, sort_keys=True) + "\n")
print(json.dumps({
    "parts": list(plan["groups"]),
    "root_count": len(roots),
    "closure_bytes": plan["part_generated_closure_bytes"],
    "module_counts": plan["part_generated_module_counts"],
}, sort_keys=True))
