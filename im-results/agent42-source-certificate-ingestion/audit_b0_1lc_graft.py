#!/usr/bin/env python3
"""Fail closed unless the B0=1LC weighted 109-parent graft is source-compiled."""
import json
import pathlib
import re
import sys

log_path = pathlib.Path(sys.argv[1] if len(sys.argv) > 1 else "/tmp/a13-heldleaf109.log")
log = log_path.read_text(encoding="utf-8")
if "sorryAx" in log or "native_decide" in log:
    raise SystemExit("forbidden sorryAx/native_decide in B0=1LC graft closure")

allowed = {"propext", "Classical.choice", "Quot.sound"}
profiles = {}
for name, raw in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log):
    profiles[name] = {x.strip() for x in raw.split(",") if x.strip()}
for name in re.findall(r"'([^']+)' does not depend on any axioms", log):
    profiles[name] = set()

required = {
    "BB6.Agent14B01LCGraft.witnessAudit_exhaustive",
    "BB6.Agent14B01LCGraft.witnessAudit_mass_conserves",
    "BB6.Agent14B01LCGraft.parent_is_exact_109_member",
    "BB6.Agent14B01LC109Graft.otherRoster_count",
    "BB6.Agent14B01LC109Graft.refinedRootDichotomy",
    "BB6.Agent14B01LC109Graft.cover_of_108_and_parentAudit",
    "BB6.Agent14B01LC109Graft.exact_from_108_and_parentAudit",
    "BB6.Agent42B01LC109SourceConsumer.q2800_held_leaf_weighted_at_champion_score",
    "BB6.Agent42B01LC109SourceConsumer.b0_1lc_parent_cover_from_41_boxes",
    "BB6.Agent42B01LC109SourceConsumer.cover_reduced_roster_from_108_and_41_boxes",
    "BB6.Agent42B01LC109SourceConsumer.exact_from_108_and_41_boxes",
    "BB6.Agent42B01LC109SourceConsumer.refined_obligation_count",
    "BB6.Agent42B01LC109SourceConsumer.b0_1lc_mass_conservation",
}
missing = sorted(required - profiles.keys())
if missing:
    raise SystemExit("missing theorem axiom profiles: " + ", ".join(missing))
bad = {
    name: sorted(profiles[name] - allowed)
    for name in sorted(required)
    if profiles[name] - allowed
}
if bad:
    raise SystemExit("unexpected theorem axioms: " + json.dumps(bad, sort_keys=True))

report = {
    "required_theorems": sorted(required),
    "allowed_axioms": sorted(allowed),
    "profiles": {name: sorted(profiles[name]) for name in sorted(required)},
    "result": "accepted conditional weighted B0=1LC parent consumer",
}
print(json.dumps(report, indent=2, sort_keys=True))
