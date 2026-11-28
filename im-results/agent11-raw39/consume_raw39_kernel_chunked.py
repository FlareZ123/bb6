#!/usr/bin/env python3
"""Join accepted Raw39's exact parent proof into the accepted Canonical40 quotient.

Unlike the strict object merger, this consumer can encounter genuinely
different object files under the same module name. It never picks a winner:
the affected dependency cone of the already source-certified Raw39 proof is
renamed and checked declaration-by-declaration by Lean's kernel replay. A
bounded number of source modules per checkpoint avoids thousands of full
repeated imports. The final canonical 40→39 theorem is source elaborated and
its complete transitive axiom profile audited.

Success is a global theorem with 39 residual Covers; it is NOT BB(6) solved.
"""
import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
sys.path.insert(0, str(HERE))
from consume_raw39_after_canonical40 import (
    ALLOWED, canonical_source, accepted_parent, sha)
from chunked_kernel_replay import relocate_chunked

TARGETS = [
    "BB6.Agent11Raw39Canonical40Bridge.literal_eq_source",
    "BB6.Agent11Raw39Canonical40Bridge.parent_unique_in_roster40",
    "BB6.Agent11Raw39Canonical40Bridge.weighted_cover",
    "BB6.Agent11Raw39Canonical40Bridge.cover_at_champion_threshold",
    "BB6.Agent11Raw39Canonical39Successor.count39",
    "BB6.Agent11Raw39Canonical39Successor.raw39_cover",
    "BB6.Agent11Raw39Canonical39Successor.sound_integrated",
    "BB6.Agent11Raw39Canonical39Successor.exact_at_champion_score",
]


def compile_stage_kernel(work, linked):
    helper = REPO / "im-results/agent32-raw59/kernel-slice"
    toolroot = work / "kernel-tool"
    toolroot.mkdir()
    shutil.copy2(helper / "KernelStage.lean", toolroot / "KernelStage.lean")
    prefix = Path(subprocess.check_output(
        ["lean", "--print-prefix"], text=True).strip())
    env = dict(os.environ, LEAN_SYSROOT=str(prefix), LEAN_PATH=str(linked))
    subprocess.run(["lean", "-c", "KernelStage.c", "KernelStage.lean"],
                   cwd=toolroot, env=env, check=True)
    subprocess.run(["leanc", "-O2", "-o", "kernelstage", "KernelStage.c"],
                   cwd=toolroot, env=env, check=True)
    return toolroot / "kernelstage"


def generated_bridge(work, staged_root, names, namespace="A11Raw39Slice"):
    parent_name = "BB6.Agent11Raw39AcceptedSix.p39"
    if parent_name in names:
        parent_name = namespace + "." + parent_name
    certified_bound = namespace + ".BB6.Agent11Raw39Closed.parent_bound"
    text = f"""import Raw39Canonical40Membership
import {staged_root}

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent11Raw39Canonical40Bridge
open BB6Coverage BB6.Agent13BlankDelay
open BB6.Agent31FourHoleRoster

abbrev p : PartialMachine := BB6.Agent11Raw39Canonical40Membership.p

theorem literal_eq_source : p = {parent_name} :=
  sameTable_sound (by decide)

theorem parent_unique_in_roster40 :
    (BB6.Agent31Canonical40Extra57.roster40.filter
      (fun e => sameTable e.2 p)).length = 1 :=
  BB6.Agent11Raw39Canonical40Membership.parent_present

theorem weighted_cover (B : Nat) (hB : 28311 ≤ B) :
    Cover (WeightedBound B) p := by
  rw [literal_eq_source]
  apply Cover.leaf
  intro m hm k d hk hd
  exact Nat.le_trans ({certified_bound} m hm k d hk hd) hB

theorem cover_at_champion_threshold :
    Cover (WeightedBound 6766859) p :=
  weighted_cover 6766859 (by decide)

#print axioms literal_eq_source
#print axioms parent_unique_in_roster40
#print axioms weighted_cover
#print axioms cover_at_champion_threshold

end BB6.Agent11Raw39Canonical40Bridge
"""
    source = work / "Raw39Canonical40Bridge.lean"
    source.write_text(text)
    return source


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--work", type=Path, required=True)
    ap.add_argument("--onele-run", type=int, default=46114235329)
    ap.add_argument("--chunk-size", type=int, default=64)
    args = ap.parse_args()
    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    evidence = work / "evidence"
    evidence.mkdir()
    parent_linked, parent = accepted_parent(work / "parent", args.onele_run)
    if parent["bound"] != 28311 or len(parent["producers"]) != 11:
        raise RuntimeError("wrong all-child Raw39 parent source certificate")
    canonical, predecessor = canonical_source(work / "canonical")
    stage_tool = compile_stage_kernel(work, canonical)
    producer = sorted(parent_linked.glob("*.olean"))
    report, stage_objects, names = relocate_chunked(
        producer_files=producer, base=canonical, work=work / "raw39-staged",
        root_module="Raw39CompleteJoin",
        root_names=["BB6.Agent11Raw39Closed.parent_bound"],
        prefix="A11Raw39Slice",
        tool=stage_tool,
        comparator_batch=HERE / "CompareKernelImportsBatch.lean",
        chunk_size=args.chunk_size)
    if not report["complete"] or (
        "BB6.Agent11Raw39Closed.parent_bound" not in names):
        raise RuntimeError("Raw39 parent theorem not kernel replayed")
    copied = []
    for f in sorted(stage_objects.glob("*.olean")):
        dest = canonical / f.name
        if dest.exists():
            if sha(dest) != sha(f):
                raise RuntimeError("unresolved staged import collision: " + f.name)
        else:
            shutil.copy2(f, dest)
            copied.append(f.name)

    # Use the same accepted Canonical40 semantic root, not an index crosswalk.
    sys.path.insert(0, str(HERE.parent / "agent50-raw47-canonical41"))
    import consume_after_canonical40 as ca
    c = ca.c
    bridge = generated_bridge(work, report["staged_root"], names)
    a = TARGETS[:4]
    root1, profile1 = c.u.compile_one(bridge, canonical, evidence, a)
    root2, profile2 = c.u.compile_one(
        HERE / "Raw39Canonical39Successor.lean",
        canonical, evidence, TARGETS[4:])
    profiles = dict(profile1)
    profiles.update(profile2)
    if set(profiles) != set(TARGETS) or not all(
        set(x) <= ALLOWED for x in profiles.values()):
        raise RuntimeError("missing/unapproved global axiom audit")
    accepted = {
        "claim": "source-accepted Raw39 all-completions Cover consumed into Canonical40; 39 residual Covers",
        "predecessor": predecessor,
        "parent": parent,
        "staged_root": report["staged_root"],
        "kernel_replay": {
            "mode": report["mode"], "chunk_size": report["chunk_size"],
            "affected_modules": report["affected_modules"],
            "selected_declarations": report["selected_declarations"],
            "kernel_comparison": report["kernel_comparison"],
            "chunks": len(report["chunks"]),
            "copied_modules": copied,
        },
        "theorems": profiles,
        "roots": {root1.name: sha(root1), root2.name: sha(root2)},
        "source_revision": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=REPO, text=True).strip(),
        "onele_run": args.onele_run,
    }
    (evidence / "canonical39-raw39-accepted.json").write_text(
        json.dumps(accepted, indent=2, sort_keys=True) + "\n")
    print("PASS: Raw39 complete parent consumed into Canonical40; 39 retained Covers", flush=True)


if __name__ == "__main__":
    main()
