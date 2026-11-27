#!/usr/bin/env python3
"""Consume the *accepted* Raw47 local parent on the accepted Raw57 Canonical40.

Required proof chain:
  source Canonical41 -> accepted Raw57 successor (40) -> accepted Raw47 (39)
The target theorem is an *iff conditional on all 39 surviving Covers*.
This tool never treats a residual count or prepared trace as a global bound.
"""
import argparse
import json
import re
from pathlib import Path
import shutil
import subprocess

import consume as c

RAW57_RUN = 46075158700
RAW57_ARTIFACT = 15234886499
RAW57_DIGEST = "d1547d32ca4668d250978f288c827287cadd425eef9c8e0c230802d313177207"
RAW57_NS = "BB6.Agent31Canonical40Extra57"
TARGET_NS = "BB6.Agent50Canonical39Raw47"


def restore_canonical40(work, linked, canonical41, predecessor_pin):
    """Restore exact accepted predecessor objects, with hash-locked provenance."""
    run, item, pin = c.extra.artifact(RAW57_RUN, "canonical40-raw57-thin-delta")
    assert item["id"] == RAW57_ARTIFACT
    assert pin[2] == RAW57_DIGEST
    folder = work / "canonical40-raw57"
    folder.mkdir()
    dirs = c.a68.download(pin, folder)
    metadata = folder / "metadata" / str(item["id"])
    matches = list(metadata.rglob("delta.json"))
    assert len(matches) == 1, matches
    report = json.loads(matches[0].read_text())
    assert report["status"] == "source-accepted Raw57 successor of Canonical41"
    assert report["source_revision"] == run["head_sha"]
    assert report["previous_delta"] == predecessor_pin
    assert report["previous_root_sha256"] == canonical41["root_sha256"]
    assert report["previous_residual_count"] == 41
    assert report["remaining_residual_count"] == 40
    assert report["exact_at_champion_score"] == RAW57_NS + ".exact_at_champion_score"
    assert report["exact_at_champion_score"] in report["axioms"]
    assert all(set(v) <= c.ALLOWED for v in report["axioms"].values())
    assert report["parent"]["label"] == "raw57"
    assert report["parent"]["theorem"] == "BB6.Agent31Raw57.literal_cover"
    objects = report["delta_objects"]
    observed = {}
    for directory in dirs:
        for file in directory.glob("*.olean"):
            if file.name in observed:
                assert c.a68.sha(observed[file.name]) == c.a68.sha(file), file.name
                continue
            observed[file.name] = file
    assert set(objects) == set(observed), (set(objects)-set(observed),set(observed)-set(objects))
    assert objects[report["root"]] == report["root_sha256"]
    for name,digest in objects.items():
        assert name == Path(name).name
        assert c.a68.sha(observed[name]) == digest, name
        dest = linked / name
        assert not dest.exists(), name
        shutil.copy2(observed[name],dest)
    return report, {"run_id": RAW57_RUN, "artifact_id": item["id"],
                    "artifact_sha256": pin[2],
                    "root_sha256": report["root_sha256"]}


def preflight_membership(work, linked, evidence):
    """Kernel-check source table belongs exactly once to accepted roster40."""
    source=work/"Raw47Canonical40Membership.lean"
    source.write_text("""import Canonical40Extra57
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent50Raw47Canonical40Membership
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6.Agent47CanonicalFrontier
open BB6.Agent31FourHoleRoster

def p : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,2⟩)
  | _,_ => none

theorem parent_present :
    (BB6.Agent31Canonical40Extra57.roster40.filter
      (fun e => sameTable e.2 p)).length = 1 := by decide
#print axioms parent_present
end BB6.Agent50Raw47Canonical40Membership
""")
    root, profile = c.u.compile_one(source, linked, evidence,
        ["BB6.Agent50Raw47Canonical40Membership.parent_present"])
    assert set(profile["BB6.Agent50Raw47Canonical40Membership.parent_present"]) <= c.ALLOWED
    root.unlink()
    print("PASS: Raw47 exactly once in accepted Raw57 Canonical40",flush=True)


def generate_source(prior, work):
    # Reuse the exact accepted conditional-consumer skeleton; regenerate
    # source with a different parent, rather than trusting index positions.
    # Raw59 was already eliminated by the previous Canonical41 predecessor.
    annotated=dict(prior)
    annotated["accepted"]=["59"]
    old, old_ns, names = c.extra.generate(["57"],annotated,RAW57_NS,work)
    assert old_ns == "BB6.Agent31Canonical39Extra57"
    text=old.read_text()
    assert "import Raw57ParentCover" in text
    assert "BB6.Agent31Raw57.literalParent" in text
    text=text.replace("import Raw57ParentCover","import Raw47Complete")
    text=text.replace(old_ns,TARGET_NS)
    text=text.replace("BB6.Agent31Raw57.literalParent",
                      "BB6.Agent50Raw47Depth3Cut.parent")
    text=re.sub(r"\bp57\b|\bp57_",lambda m:"p47_" if m.group(0)=="p57_" else "p47",text)
    start=text.index("theorem p47_cover :")
    end=text.index("\nabbrev readyParents :",start)
    text=text[:start]+(
        "theorem p47_cover : Cover (WeightedBound 6766859) p47 :=\n"
        "  BB6.Agent50Raw47Complete.cover_at 6766859 (by decide)\n"
    )+text[end:]
    assert "Raw57" not in text and "p57" not in text
    root=work/"Canonical39Raw47.lean"
    root.write_text(text)
    old.unlink()
    return root, [name.replace(old_ns,TARGET_NS).replace("p57_","p47_") for name in names]


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--work",type=Path,required=True)
    ap.add_argument("--raw47-run-id",type=int,required=True)
    args=ap.parse_args()
    work=args.work.resolve()
    work.mkdir(parents=True,exist_ok=False)
    delta=work/"canonical39-raw47-delta"
    evidence=delta/"evidence"
    objects=delta/"objects"
    evidence.mkdir(parents=True)
    objects.mkdir()

    linked,_,_,base_report=c.base.verify_base(work,c.base.BASE_RUN)
    sharp=c.resume.restore_sharp(work,linked,base_report)
    ready,_,ready_pin=c.extra.restore_ready(work,linked,sharp,46031670976)
    assert ready["remaining_residual_count"]==46
    prior41,pin41=c.restore_extra(work,linked,ready,ready_pin)
    assert prior41["remaining_residual_count"]==41

    prior,pin40=restore_canonical40(work,linked,prior41,pin41)
    preflight_membership(work,linked,evidence)
    parentdir=work/"raw47"
    parentdir.mkdir()
    spec,dirs=c.restore_parent(args.raw47_run_id,parentdir,evidence)
    copied,audit=[],{}
    c.selected.add_family(spec,dirs,linked,copied,audit)
    source,names=generate_source(prior,work)
    root,profiles=c.u.compile_one(source,linked,evidence,names)
    assert TARGET_NS+".exact_at_champion_score" in profiles
    assert all(set(v)<=c.ALLOWED for v in profiles.values())
    copied.append(root)

    hashes={}
    for src in copied:
        dst=objects/src.name
        assert not dst.exists(),dst
        shutil.copy2(src,dst)
        hashes[dst.name]=c.a68.sha(dst)
    report={
        "status":"source-accepted Raw47 successor of Canonical40",
        "previous_delta":pin40,
        "previous_root_sha256":prior["root_sha256"],
        "previous_residual_count":40,
        "remaining_residual_count":39,
        "parent":spec,
        "link_audit":audit,
        "axioms":profiles,
        "root":root.name,
        "root_sha256":hashes[root.name],
        "delta_objects":hashes,
        "source_revision":subprocess.check_output(["git","rev-parse","HEAD"],text=True).strip(),
        "exact_at_champion_score":TARGET_NS+".exact_at_champion_score"
    }
    c.save_json(delta/"delta.json",report)
    shutil.rmtree(parentdir)
    print("PASS: Raw47 consumed on accepted Canonical40; 39 Covers remain",flush=True)


if __name__=="__main__":
    main()
