#!/usr/bin/env python3
"""Source-certify the Raw39 one-child global reduction, or full Canonical39 cut.

The producer proofs and the accepted Canonical40 lineage are independently
reconstructed, with source revisions/compiler/manifest hashes checked by their
existing consumers. Identical module names may be merged only if their .olean
bytes are identical. Unlike a hand-written list of 40 raw indices, the
Canonical40 objects are the actual accepted quotient theorem.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
sys.path.insert(0, str(HERE.parent / "agent50-raw47-canonical41"))
import consume_after_canonical40 as ca

c = ca.c
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
TEN_TARGETS = [
    "BB6.Agent11Raw39SoleObligation.literal_source_equality",
    "BB6.Agent11Raw39SoleObligation.parent_bound_of_oneLE",
    "BB6.Agent11Raw39SoleObligation.parent_cover_of_oneLE",
    "BB6.Agent11Raw39SoleObligation.exact_at_champion_if_oneLE",
]
FULL_TARGETS = [
    "BB6.Agent11Raw39Canonical40Bridge.literal_eq_source",
    "BB6.Agent11Raw39Canonical40Bridge.parent_unique_in_roster40",
    "BB6.Agent11Raw39Canonical40Bridge.weighted_cover",
    "BB6.Agent11Raw39Canonical40Bridge.cover_at_champion_threshold",
    "BB6.Agent11Raw39Canonical39Successor.count39",
    "BB6.Agent11Raw39Canonical39Successor.raw39_cover",
    "BB6.Agent11Raw39Canonical39Successor.sound_integrated",
    "BB6.Agent11Raw39Canonical39Successor.exact_at_champion_score",
]

def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def ensure(x, detail):
    if not x:
        raise RuntimeError(detail)

def canonical_source(work):
    """Recover accepted Canonical40 and source-check the Raw39 cut in place."""
    work.mkdir(parents=True, exist_ok=False)
    evidence=work/"evidence"
    evidence.mkdir()
    linked,_,_,base_report=c.base.verify_base(work,c.base.BASE_RUN)
    sharp=c.resume.restore_sharp(work,linked,base_report)
    ready,_,ready_pin=c.extra.restore_ready(work,linked,sharp,46031670976)
    ensure(ready["remaining_residual_count"]==46,"wrong Canonical53 predecessor")
    prior41,pin41=c.restore_extra(work,linked,ready,ready_pin)
    ensure(prior41["remaining_residual_count"]==41,"wrong Canonical41 predecessor")
    prior40,pin40=ca.restore_canonical40(work,linked,prior41,pin41)
    ensure(prior40["remaining_residual_count"]==40,"wrong Canonical40 predecessor")
    targets=[
        "BB6.Agent11Raw39Canonical40Membership.parent_present",
        "BB6.Agent11Raw39Canonical40Membership.distinct_from_raw47",
    ]
    source=HERE/"Raw39Canonical40Membership.lean"
    root,profiles=c.u.compile_one(source,linked,evidence,targets)
    ensure(all(set(v)<=ALLOWED for v in profiles.values()),"nonstandard membership axioms")
    conditional=[
        "BB6.Agent11Raw39Canonical40Conditional.parent_count40",
        "BB6.Agent11Raw39Canonical40Conditional.parent_root",
        "BB6.Agent11Raw39Canonical40Conditional.parents_pairwise_distinct",
        "BB6.Agent11Raw39Canonical40Conditional.parents_root",
        "BB6.Agent11Raw39Canonical40Conditional.count39",
        "BB6.Agent11Raw39Canonical40Conditional.removed_parent_absent",
        "BB6.Agent11Raw39Canonical40Conditional.conditional_sound",
        "BB6.Agent11Raw39Canonical40Conditional.conditional_exact_at_champion",
    ]
    root2,profiles2=c.u.compile_one(
        HERE/"Raw39Canonical40Conditional.lean",linked,evidence,conditional)
    ensure(all(set(v)<=ALLOWED for v in profiles2.values()),"nonstandard conditional axioms")
    return linked, {"canonical40":pin40,
                    "membership":{k:v for k,v in profiles.items()},
                    "conditional":{k:v for k,v in profiles2.items()},
                    "membership_sha256":sha(root),"conditional_sha256":sha(root2)}

def accepted_parent(work,onele_run):
    work.mkdir(parents=True,exist_ok=False)
    # Runner requires the work folder not to exist; use a nested fresh path.
    out=work/"accepted"
    args=[sys.executable,str(HERE/"assemble_accepted_parent.py"),
          "--work",str(out)]
    if onele_run:
        args.extend(["--onele-run",str(onele_run)])
    else:
        args.append("--ten-only")
    subprocess.run(args,check=True,cwd=REPO)
    receipt=json.loads((out/"evidence"/"parent-accepted.json").read_text())
    expected=(11 if onele_run else 10)
    ensure(len(receipt["producers"])==expected,"wrong accepted child count")
    return out/"linked",receipt

def merge_objects(dest,canonical,parent,evidence):
    dest.mkdir()
    inventory={}
    conflicts=[]
    for root,tag in ((canonical,"canonical40"),(parent,"raw39-parent")):
        for f in sorted(root.glob("*.olean")):
            obj=dest/f.name
            h=sha(f)
            if obj.exists():
                if sha(obj)!=h:
                    conflicts.append({
                        "module":f.name,"canonical_sha256":sha(obj),
                        "raw39_sha256":h})
                else:
                    inventory.setdefault(f.name,[]).append(tag)
            else:
                shutil.copy2(f,obj)
                inventory[f.name]=[tag]
    (evidence/"object-merge.json").write_text(
        json.dumps({"canonical_count":len(list(canonical.glob("*.olean"))),
                    "raw39_count":len(list(parent.glob("*.olean"))),
                    "merged_count":len(inventory),"conflicts":conflicts},
                   indent=2,sort_keys=True)+"\n")
    ensure(not conflicts,
           "source/object namespace collisions (see evidence/object-merge.json): "
           +", ".join(x["module"] for x in conflicts[:20]))
    return len(inventory)

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--work",type=Path,required=True)
    ap.add_argument("--onele-run",type=int,
                    help="successful complete 1LE source run; omit for ten-child reduction")
    a=ap.parse_args()
    work=a.work.resolve()
    work.mkdir(parents=True,exist_ok=False)
    evidence=work/"evidence"
    evidence.mkdir()
    parent,receipt=accepted_parent(work/"parent",a.onele_run)
    canonical,pin=canonical_source(work/"canonical")
    linked=work/"linked"
    n=merge_objects(linked,canonical,parent,evidence)

    targets=FULL_TARGETS if a.onele_run else TEN_TARGETS
    if a.onele_run:
        roots=[HERE/"Raw39Canonical40Bridge.lean",
               HERE/"Raw39Canonical39Successor.lean"]
        claim="source-accepted Raw39 whole parent and Canonical40 to 39 reduction"
    else:
        roots=[HERE/"Raw39SoleObligation.lean"]
        claim="source-accepted 39 global Covers plus sole Raw39 A1=1LE premise"
    profiles={}
    built={}
    for source in roots:
        names=[t for t in targets if t.split(".")[1].startswith(source.stem.replace("Raw39","Raw39",1))]
        # The explicit module targets above are authoritative; all requested
        # transitive claims are checked at the last source if a file is shared.
        if not names:
            names=[t for t in targets if source.stem in t]
        ensure(names,"no target declarations for "+str(source))
        root,ax=c.u.compile_one(source,linked,evidence,names)
        profiles.update(ax)
        built[root.name]=sha(root)
    ensure(set(profiles)==set(targets),
           "missing printed theorem profiles: "+str(set(targets)-set(profiles)))
    ensure(all(set(v)<=ALLOWED for v in profiles.values()),
           "unapproved Lean axiom profile")
    result={"claim":claim,
            "source_revision":subprocess.check_output(
                ["git","rev-parse","HEAD"],cwd=REPO,text=True).strip(),
            "canonical40_predecessor":pin,
            "raw39_parent":receipt,
            "onele_run":a.onele_run,
            "merged_source_objects":n,
            "theorems":profiles,
            "root_objects":built}
    (evidence/"global-raw39.json").write_text(
        json.dumps(result,indent=2,sort_keys=True)+"\n")
    print("PASS: "+claim,flush=True)

if __name__=="__main__":
    main()
