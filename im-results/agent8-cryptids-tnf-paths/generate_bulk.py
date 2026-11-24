#!/usr/bin/env python3
"""Generate independently kernel-checkable Lean paths, optionally with source proof grafts."""
import argparse
import csv
import re
from pathlib import Path

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("output", type=Path)
parser.add_argument("--start", type=int, default=1)
parser.add_argument("--end", type=int, default=151)
parser.add_argument("--source", action="store_true")
args = parser.parse_args()
with Path(__file__).with_name("bulk-manifest.tsv").open() as f:
    rows = list(csv.DictReader(f, delimiter="\t"))
assert 1 <= args.start <= args.end <= len(rows)
selected = list(enumerate(rows, 1))[args.start-1:args.end]
imports = ["import FirstHolePath"]
if args.source:
    imports += ["import CryptidsTapeAdapter"]
    imports += ["import BusyBeaver.BB6.NonHalt.M_" + row["rle"] for _, row in selected]
out = imports + ["", "set_option maxRecDepth 12000", "set_option maxHeartbeats 0",
                 "namespace BB6.Agent8TNFPath.Bulk",
                 "open BB6Coverage BB6.Agent8TNFPath BB6.Agent47WeightedHalt"]
if args.source:
    out += ["open BB6.ConjectureBridge"]
for i, row in selected:
    rle = row["rle"]
    slots = [s for group in rle.split("_") for s in re.findall(r"HHH|[01][LR][A-F]", group)]
    assert len(slots) == 12 and slots.count("HHH") == 1 and slots[0] == "1RB"
    boolstr = lambda x: "true" if x else "false"
    moves = ["none" if s == "HHH" else
             f"some ⟨{boolstr(s[0]=='1')}, {boolstr(s[1]=='R')}, {ord(s[2])-65}⟩"
             for s in slots]
    visits = [tuple(map(int, s.split(":"))) for s in row["first_visits_after_root"].split(",")]
    assert len(visits) == 10 and len({s for _, s in visits}) == 10
    assert all(0 < s < 12 for _, s in visits)
    schedule = ", ".join(f"({n}, ({s//2}, {boolstr(s%2)}))" for n, s in visits)
    out += [f"\n-- {rle}; upstream blob {row['git_blob_sha']}",
            f"def m{i} : Machine := fun s => ([{', '.join(moves)}] : List (Option Move))[2*s.1.val + (if s.2 then 1 else 0)]?.getD none",
            f"def schedule{i} : List (Nat × Slot) := [{schedule}]",
            f"theorem path{i} : FirstHolePath (forgetHaltRows m{i}) 6 := checked_from_root _ schedule{i} (by decide)",
            f"#print axioms path{i}"]
    if args.source:
        ns = "BusyBeaver.M_" + rle
        out += [f"def source{i} : ConjectureMachines.Machine 6 2 := {ns}.machine",
                f"theorem sourceEq{i} : toAgent8 source{i} = m{i} := by",
                "  funext s; rcases s with ⟨q,b⟩; fin_cases q <;> cases b <;> rfl",
                f"theorem never{i} : NeverHalts m{i} := by",
                f"  rw [← sourceEq{i}]",
                f"  exact not_halts_to_agent8 source{i} ((ConjectureMachines.isNotHalt_toBB_iff_not_halts source{i}).mp (by",
                f"    first | simpa [source{i}] using {ns}.is_not_halt | simpa [source{i}] using {ns}.is_does_not_halt))",
                f"#print axioms never{i}"]
out += ["end BB6.Agent8TNFPath.Bulk", ""]
args.output.write_text("\n".join(out))
