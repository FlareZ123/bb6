#!/usr/bin/env python3
"""Consume source-accepted Raw47 exact weighted Cover on Canonical41.

A new global quotient reduction is claimed only after the original-source
producer, its entire Lean import closure, unique roster membership, all
kernel imports, and the final fixed-score theorem pass.
"""
import argparse
import json
import re
from pathlib import Path
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
SIBLINGS = HERE.parent
sys.path.insert(0, str(SIBLINGS / "agent29-raw57-consumer"))
sys.path.insert(0, str(SIBLINGS / "agent2-ready-union"))
from consume_after_canonical41 import restore_extra
import extra_ready_union as extra
import resume_ready_union as resume

u, a68, base, selected = extra.u, extra.a68, extra.base, extra.selected
EXTRA_NS = "BB6.Agent31Canonical41Extra63R61R67R59R122"
PARENT_NS = "BB6.Agent50Raw47Complete"
PARENT_TABLE = "1RB---_1RC---_0RD---_1LD0RC_------_------"
BOUND = 143977
TARGET = 6766859
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}

def save_json(path, doc):
    path.write_text(json.dumps(doc, indent=2, sort_keys=True) + "\n")

def restore_parent(run_id, work, evidence):
    run, item, pin = extra.artifact(run_id, "raw47-lifted1212")
    dirs = a68.download(pin, work)
    manifests = []
    for path in (work / "metadata" / str(item["id"])).rglob("manifest.json"):
        doc = json.loads(path.read_text())
        if (doc.get("claim") or {}).get("theorem") == PARENT_NS + ".cover":
            manifests.append((path, doc))
    assert len(manifests) == 1, [(str(x),m.get("claim")) for x,m in manifests]
    path, doc = manifests[0]
    assert doc["proof_source_revision"] == run["head_sha"]
    assert doc["claim"]["parent_table"] == PARENT_TABLE
    assert doc["claim"]["weighted_bound"] == BOUND
    assert doc["artifact_name"] == "raw47-lifted1212"
    assert any(x["module"] == "Raw47Complete" for x in doc["roots"])
    assert "4.36.0-rc2" in doc["lean_version"]
    prefix = Path(subprocess.check_output(["lean","--print-prefix"],text=True).strip())
    assert doc["lean_binary"]["sha256"] == a68.sha(prefix / "bin" / "lean")
    allowed = {v["module"] + ".olean": v["olean_sha256"] for v in doc["modules"]}
    assert len(allowed) == doc["module_count"]
    for d in dirs:
        for f in d.glob("*.olean"):
            assert f.name in allowed and a68.sha(f) == allowed[f.name], f
    save_json(evidence / "raw47-source-manifest.json", doc)
    return {"label":"raw47","root":"Raw47Complete","run_id":run_id,
            "artifact_id":item["id"],"artifact_sha256":pin[2],
            "revision":run["head_sha"],"theorem":PARENT_NS + ".cover",
            "bound":BOUND,"table":PARENT_TABLE}, dirs

def generate_source(prior, work):
    # Reuse the accepted one-parent roster-removal skeleton, with the
    # Raw47 complete source Cover instead of the unrelated Raw57 theorem.
    old, old_ns, names = extra.generate(["57"], prior, EXTRA_NS, work)
    text = old.read_text()
    assert old_ns == "BB6.Agent31Canonical40Extra57"
    assert "import Raw57ParentCover" in text
    assert "BB6.Agent31Raw57.literalParent" in text
    text = text.replace("import Raw57ParentCover", "import Raw47Complete")
    text = text.replace("BB6.Agent31Canonical40Extra57",
                        "BB6.Agent50Canonical40Raw47")
    text = text.replace("BB6.Agent31Raw57.literalParent",
                        "BB6.Agent50Raw47Depth3Cut.parent")
    text = re.sub(r"\bp57\b|\bp57_", lambda m:
                  "p47_" if m.group(0) == "p57_" else "p47", text)
    start = text.index("theorem p47_cover :")
    end = text.index("\nabbrev readyParents :", start)
    text = text[:start] + (
        "theorem p47_cover : Cover (WeightedBound 6766859) p47 :=\n"
        "  BB6.Agent50Raw47Complete.cover_at 6766859 (by decide)\n"
    ) + text[end:]
    assert "Raw57" not in text and "p57" not in text
    generated = work / "Canonical40Raw47.lean"
    generated.write_text(text)
    old.unlink()
    return generated, "BB6.Agent50Canonical40Raw47", [
        name.replace(old_ns, "BB6.Agent50Canonical40Raw47").
             replace("p57_", "p47_") for name in names]

def preflight_membership(work, linked, evidence):
    # Check actual Canonical41 membership before downloading the large
    # Raw47 object closure, using a literal five-transition table.
    source = work / "Raw47CanonicalMembership.lean"
    source.write_text("""import Canonical41Extra63R61R67R59R122
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent50Raw47Membership
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
    (BB6.Agent31Canonical41Extra63R61R67R59R122.roster41.filter
      (fun e => sameTable e.2 p)).length = 1 := by decide
#print axioms parent_present
end BB6.Agent50Raw47Membership
""")
    root, profile = u.compile_one(source, linked, evidence, [
        "BB6.Agent50Raw47Membership.parent_present"])
    assert set(profile["BB6.Agent50Raw47Membership.parent_present"]) <= ALLOWED
    root.unlink()
    print("PASS: Raw47 occurs exactly once in Canonical41", flush=True)

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--work", type=Path, required=True)
    ap.add_argument("--raw47-run-id", type=int, required=True)
    args = ap.parse_args()
    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    delta = work / "canonical40-raw47-delta"
    evidence = delta / "evidence"
    objects = delta / "objects"
    evidence.mkdir(parents=True)
    objects.mkdir()

    linked, _, _, base_report = base.verify_base(work, base.BASE_RUN)
    sharp = resume.restore_sharp(work, linked, base_report)
    ready, ready_ns, ready_pin = extra.restore_ready(
        work, linked, sharp, 46031670976)
    assert ready["remaining_residual_count"] == 46
    prior, prior_pin = restore_extra(work, linked, ready, ready_pin)
    assert prior["remaining_residual_count"] == 41
    preflight_membership(work, linked, evidence)

    parentdir = work / "raw47"
    parentdir.mkdir()
    spec, dirs = restore_parent(args.raw47_run_id, parentdir, evidence)
    copied, audit = [], {}
    selected.add_family(spec, dirs, linked, copied, audit)

    source, ns, names = generate_source(prior, work)
    root, profiles = u.compile_one(source, linked, evidence, names)
    assert ns + ".exact_at_champion_score" in profiles
    assert all(set(v) <= ALLOWED for v in profiles.values())
    copied.append(root)
    hashes = {}
    for src in copied:
        dest = objects / src.name
        assert not dest.exists(), dest
        shutil.copy2(src, dest)
        hashes[dest.name] = a68.sha(dest)
    report = {
        "status": "source-accepted Raw47 successor of Canonical41",
        "previous_delta": prior_pin,
        "previous_root_sha256": prior["root_sha256"],
        "previous_residual_count": 41,
        "remaining_residual_count": 40,
        "parent": spec,
        "link_audit": audit,
        "axioms": profiles,
        "root": root.name,
        "root_sha256": hashes[root.name],
        "delta_objects": hashes,
        "source_revision": subprocess.check_output(
            ["git","rev-parse","HEAD"],text=True).strip(),
        "exact_at_champion_score": ns + ".exact_at_champion_score",
    }
    save_json(delta / "delta.json", report)
    shutil.rmtree(parentdir)
    print("PASS: Raw47 consumed directly from Canonical41; 40 Covers remain",
          flush=True)

if __name__=="__main__":
    main()
