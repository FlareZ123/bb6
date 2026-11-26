"""Select compatible, independently certified parents without rebuilding Raw59."""
import argparse
import json
import os
from pathlib import Path
import re
import shutil
import subprocess

import assemble_canonical59_five_parent as five

a63, a68, champion = five.a63, five.a68, five.champion
HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
MEM = "BB6.Agent31Canonical59Membership"
NS = "BB6.Agent32CanonicalSelected"
LABELS = ("raw119", "raw115", "raw58", "raw108", "raw118", "raw113")
RAW118_SPEC = {
    "label": "raw118",
    "run_id": 45812415227,
    "revision": "b2e050ea75b4633f06ce836375a4260135ed500c",
    "artifact_id": 15120592642,
    "artifact_name": "raw118-parent-proof",
    "digest": "226a16e1181a456a2f6eddfb785b3882abde05d462837fffcb4b3ba47dfe2053",
    "root": "Raw118Complete",
    "theorem": "BB6.Agent1Raw118Complete.parent_cover",
    "table": "1RB---_1RC---_0RD---_1LD1RE_---0LE_------",
    "bound": 756496,
    "size": 531464312,
}
RAW113_SPEC = {
    "label": "raw113",
    "run_id": 45802897709,
    "revision": "e91b9703f6dd7657d16bb9d428181a657ad14fff",
    "artifact_id": 15108067526,
    "artifact_name": "raw113-parent-proof",
    "digest": "7d3ac590a7b9e562e430a00148616dc37d3eb0304fd1b20e9e3cbd07c611f865",
    "root": "Raw113ParentExact",
    "theorem": "BB6.Agent25Raw113.cover113",
    "table": "1RB---_1RC---_0RD---_1LD1RE_---1RC_------",
    "bound": 2674,
    "size": 175456215,
}
OPENS = """
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31StableParentBatch
open BB6.Agent31Canonical59Membership
open BB6ChampionArithmetic
"""


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def gate(log, names):
    assert not re.search(r"sorryAx|native_decide", log), "forbidden proof mechanism"
    return a68.gate(log, names)


def candidate_source(spec, previous):
    p = spec["label"][3:]
    membership_imports = []
    membership_names = []
    if p == "118":
        source = "abbrev p118Source : PartialMachine := BB6.Agent16Raw118.parent"
        eq = """theorem p118_source_eq : p118 = p118Source := by
  rfl

"""
        cover = """theorem p118_cover : Cover (WeightedBound 6766859) p118 := by
  rw [p118_source_eq]
  exact BB6.Agent1Raw118Complete.parent_cover_monotone (by decide)

"""
        membership_imports = ["Raw118Canonical64Membership"]
        membership_names = [
            "BB6.Agent16Raw118Canonical64Membership.p118_eq_raw118_parent",
            "BB6.Agent16Raw118Canonical64Membership.p118_root",
            "BB6.Agent16Raw118Canonical64Membership.p118_parent_count64",
        ]
    elif p == "113":
        source = "abbrev p113Source : PartialMachine := BB6.Agent25Raw113.p113"
        eq = """theorem p113_source_eq : p113 = p113Source := by
  exact sameTable_sound (by decide)

"""
        cover = """theorem p113_cover : Cover (WeightedBound 6766859) p113 := by
  rw [p113_source_eq]
  exact BB6.Agent25Raw113.cover113 6766859 (by decide)

"""
        membership_names = [
            MEM + ".p113_count64",
            MEM + ".p113_root",
        ]
    else:
        text = (HERE / "Canonical59FiveParentIntegrated.lean").read_text()
        source = re.search(r"^abbrev p" + p + r"Source :.*$", text, re.M).group()
        eq = re.search(r"^theorem p" + p + r"_source_eq :.*?\n\n", text, re.M | re.S).group()
        cover = re.search(r"^theorem p" + p + r"_cover :.*?\n\n", text, re.M | re.S).group()
    if p == "59":
        source = source.replace("BB6.Agent32Raw59.p59", "A32Raw59Slice.BB6.Agent32Raw59.p59")
        cover = cover.replace("BB6.Agent32Raw59Exact.cover", "A32Raw59Slice.BB6.Agent32Raw59Exact.cover")
    module = "CanonicalSelectedRaw" + p
    namespace = NS + "Raw" + p
    imports = ["Canonical59FiveParentMembership", *membership_imports,
               "Raw59KernelSlice" if p == "59" else spec["root"],
               "TM63RawUpperInterface", "ChampionScoreLowerBound", *previous]
    names = [namespace + ".p" + p + "_source_eq", namespace + ".p" + p + "_cover"]
    if p == "118":
        names += membership_names
    elif p == "113":
        names += membership_names
    else:
        names += [MEM + ".p" + p + "_count64"]
    opens = OPENS + (
        "\nopen BB6.Agent16Raw118Canonical64Membership\n" if p == "118" else ""
    )
    body = "".join("import " + x + "\n" for x in imports)
    body += "\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n"
    body += "\nnamespace " + namespace + "\n" + opens + "\n"
    body += source + "\n\n" + eq + cover
    body += "".join("#print axioms " + x + "\n" for x in names)
    body += "\nend " + namespace + "\n"
    return module, body, names

def final_source(accepted):
    ids = [x["label"][3:] for x in accepted]
    namespace = NS + "Integrated"
    body = "import Raw118Canonical64Membership\n" if "118" in ids else ""
    body += "".join("import CanonicalSelectedRaw" + p + "\n" for p in ids)
    body += "\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n"
    opens = OPENS + (
        "\nopen BB6.Agent16Raw118Canonical64Membership\n" if "118" in ids else ""
    )
    body += "\nnamespace " + namespace + "\n" + opens
    body += "\ndef selectedParents : List PartialMachine := [" + ",".join("p" + p for p in ids) + "]\n"
    body += """
noncomputable def rosterSelected :=
  removeParents selectedParents BB6.Agent3Canonical64Raw120.roster64

"""
    if "59" in ids:
        body += """
theorem raw59_consumed :
    (rosterSelected.filter (fun e => sameTable e.2 p59)).length = 0 := by decide
"""
    else:
        body += """
theorem raw59_retained :
    (rosterSelected.filter (fun e => sameTable e.2 p59)).length = 1 := by decide
"""
    body += """

theorem parents_pairwise_distinct :
    List.Pairwise (fun p q => sameTable p q = false) selectedParents := by decide
"""
    body += "\ntheorem countSelected : rosterSelected.length = " + str(64-len(ids)) + " := by decide\n"
    body += """
theorem parents_root :
    ∀ p ∈ selectedParents, p initialSlot = some (some ⟨true,true,1⟩) := by
  intro p hp
  simp only [selectedParents, List.mem_cons, List.not_mem_nil, or_false] at hp
"""
    cases = "  rcases hp with " + " | ".join("rfl" for _ in ids)
    body += cases + "\n"
    for p in ids:
        if p == "118":
            body += "  · exact BB6.Agent16Raw118Canonical64Membership.p118_root\n"
        elif p == "113":
            body += "  · exact BB6.Agent31Canonical59Membership.p113_root\n"
        else:
            body += "  · decide\n"
    body += """
theorem parents_cover :
    ∀ p ∈ selectedParents, Cover (WeightedBound 6766859) p := by
  intro p hp
  simp only [selectedParents, List.mem_cons, List.not_mem_nil, or_false] at hp
"""
    body += cases + "\n"
    for p in ids:
        body += "  · exact " + NS + "Raw" + p + ".p" + p + "_cover\n"
    body += """
theorem sound_integrated :
    ∀ m, compatible root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ rosterSelected, TNFQuotientCompatible e.2 m := by
  apply removeParents_sound
    (parents := selectedParents)
    (roster := BB6.Agent3Canonical64Raw120.roster64)
    BB6.Agent3Canonical64Raw120.sound64_integrated
    parents_root
    parents_cover

theorem exact_at_target (B : Nat) (hB : 6766859 ≤ B)
    (hLeaves : ∀ e ∈ rosterSelected, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB sound_integrated hLeaves champ

theorem exact_at_champion_score
    (hLeaves : ∀ e ∈ rosterSelected,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2) :
    BB6.Coverage.ExactBB6 (proposedTM63Moves + 7) :=
  exact_at_target (proposedTM63Moves + 7)
    BB6.Agent38ChampionThreshold.champion_score_ge_6766859
    hLeaves
    BB6Coverage.Agent48DirectRoot.champion_raw_witness
"""
    names = [namespace + "." + n for n in (
        ("raw59_consumed" if "59" in ids else "raw59_retained"), "parents_pairwise_distinct", "countSelected",
        "parents_root", "parents_cover", "sound_integrated", "exact_at_target",
        "exact_at_champion_score")]
    for p in ids:
        if p == "118":
            names += [
                "BB6.Agent16Raw118Canonical64Membership.p118_eq_raw118_parent",
                "BB6.Agent16Raw118Canonical64Membership.p118_root",
                "BB6.Agent16Raw118Canonical64Membership.p118_parent_count64",
            ]
        elif p == "113":
            names += [MEM + ".p113_count64", MEM + ".p113_root"]
        else:
            names += [MEM + ".p" + p + "_count64"]
    names += ["BB6Coverage.Agent48DirectRoot.champion_raw_witness",
              "BB6.Agent38ChampionThreshold.champion_score_ge_6766859"]
    body += "\n" + "".join("#print axioms " + x + "\n" for x in names)
    body += "\nend " + namespace + "\n"
    return body, names

def add_family(spec, dirs, linked, copied, audit):
    prefix = Path(subprocess.check_output(["lean", "--print-prefix"], text=True).strip())
    result = subprocess.check_output(
        ["lean", "--run", str(HERE / "WalkImportClosure.lean"),
         str(prefix / "lib" / "lean"), str(len(dirs)), *map(str, dirs), spec["root"]],
        text=True)
    files = sorted(set(Path(x) for x in result.splitlines()))
    assert files and all(p.suffix == ".olean" and p.is_file() and p.parent in dirs for p in files)
    assert any(p.name == spec["root"] + ".olean" for p in files)
    audit["objects"] = []
    audit["collisions"] = []
    comparator = HERE.parent / "agent13-raw125" / "CompareKernelImports.lean"
    for p in files:
        dest = linked / p.name
        digest = a68.sha(p)
        audit["objects"].append({"module": p.name, "path": str(p), "sha256": digest})
        if dest.exists():
            chosen = a68.sha(dest)
            if chosen != digest:
                result = subprocess.run(["lean", "--run", str(comparator), str(dest), str(p)],
                                        text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
                audit["collisions"].append({"module": p.name, "chosen": chosen, "other": digest,
                                            "equal": result.returncode == 0,
                                            "comparison": result.stdout.strip()})
                assert result.returncode == 0, "incompatible kernel declarations: " + p.name
        else:
            copied.append(dest)
            shutil.copy2(p, dest)



def relocate_raw59(spec, dirs, linked, copied, audit, work, env):
    """Replay the accepted proof declarations, then use the normal consumer gate."""
    prefix = Path(subprocess.check_output(["lean", "--print-prefix"], text=True).strip())
    result = subprocess.check_output(
        ["lean", "--run", str(HERE / "WalkImportClosure.lean"),
         str(prefix / "lib" / "lean"), str(len(dirs)), *map(str, dirs), spec["root"]],
        text=True)
    files = sorted(set(Path(x) for x in result.splitlines()))
    assert files and all(p.suffix == ".olean" and p.is_file() and p.parent in dirs for p in files)
    assert any(p.name == spec["root"] + ".olean" for p in files)
    audit["objects"] = [{"module": p.name, "sha256": a68.sha(p)} for p in files]
    scratch = work / "raw59-slice"
    scratch.mkdir()
    src = HERE.parent / "agent32-raw59" / "kernel-slice" / "KernelSlice.lean"
    shutil.copy2(src, scratch / "KernelSlice.lean")
    slice_env = dict(env, LEAN_SYSROOT=str(prefix))
    subprocess.run(["lean", "-c", "KernelSlice.c", "KernelSlice.lean"],
                   cwd=scratch, env=slice_env, check=True)
    subprocess.run(["leanc", "-O2", "-o", "kernelslice", "KernelSlice.c"],
                   cwd=scratch, env=slice_env, check=True)
    base = ["Std", "Frontier", "WeightedTNF", "TNFPilot", "BlockFAR2"]
    assert all((linked / (m + ".olean")).is_file() for m in base[1:])
    (scratch / "base.txt").write_text("\n".join(base) + "\n")
    (scratch / "roots.txt").write_text("BB6.Agent32Raw59Exact.cover\nBB6.Agent32Raw59.p59\n")
    (scratch / "objects.txt").write_text("\n".join(map(str, files)) + "\n")
    dest = linked / "Raw59KernelSlice.olean"
    assert not dest.exists()
    copied.append(dest)
    with (work / "raw59-kernel-slice.log").open("w") as log:
        subprocess.run([str(scratch / "kernelslice"), "base.txt", "roots.txt", "objects.txt",
                        "Raw59KernelSlice", "A32Raw59Slice", str(dest)],
                       cwd=scratch, env=slice_env, stdout=log, stderr=subprocess.STDOUT, check=True)
    log = (work / "raw59-kernel-slice.log").read_text()
    print(log, flush=True)
    assert dest.is_file() and "PASS: saved" in log
    assert "ROOT BB6.Agent32Raw59Exact.cover -> A32Raw59Slice.BB6.Agent32Raw59Exact.cover" in log
    assert "ROOT BB6.Agent32Raw59.p59 -> A32Raw59Slice.BB6.Agent32Raw59.p59" in log
    audit["relocation"] = {"output_sha256": a68.sha(dest), "source_sha256": a68.sha(src),
                           "base": base, "log": log}



def relocate_raw59_staged(spec, dirs, linked, copied, audit, work, env):
    """Memory-bounded import-cone relocation using independent kernel stages."""
    import sys
    helper = HERE.parent / "agent32-raw59" / "kernel-slice"
    sys.path.insert(0, str(helper))
    from stage_relocate import relocate
    prefix = Path(subprocess.check_output(["lean", "--print-prefix"], text=True).strip())
    result = subprocess.check_output(
        ["lean", "--run", str(HERE / "WalkImportClosure.lean"),
         str(prefix / "lib" / "lean"), str(len(dirs)), *map(str, dirs), spec["root"]],
        text=True)
    files = sorted(set(Path(x) for x in result.splitlines()))
    assert files and all(p.suffix == ".olean" and p.is_file() and p.parent in dirs for p in files)
    scratch = work / "raw59-stage-tool"
    scratch.mkdir()
    shutil.copy2(helper / "KernelStage.lean", scratch / "KernelStage.lean")
    stage_env = dict(env, LEAN_SYSROOT=str(prefix))
    subprocess.run(["lean", "-c", "KernelStage.c", "KernelStage.lean"],
                   cwd=scratch, env=stage_env, check=True)
    subprocess.run(["leanc", "-O2", "-o", "kernelstage", "KernelStage.c"],
                   cwd=scratch, env=stage_env, check=True)
    report, objects, names = relocate(
        producer_files=files, base=linked, work=work / "raw59-staged",
        root_module=spec["root"], root_names=["BB6.Agent32Raw59Exact.cover"],
        prefix="A32Raw59Slice", tool=scratch / "kernelstage",
        comparator=HERE.parent / "agent13-raw125" / "CompareKernelImports.lean")
    assert report["complete"]
    for p in sorted(objects.glob("*.olean")):
        dest = linked / p.name
        assert not dest.exists()
        copied.append(dest)
        shutil.copy2(p, dest)
    source = scratch / "Raw59KernelSlice.lean"
    text = "import " + report["staged_root"] + "\n"
    if "BB6.Agent32Raw59.p59" not in names:
        text += "\nnamespace A32Raw59Slice.BB6.Agent32Raw59\n"
        text += "abbrev p59 := _root_.BB6.Agent32Raw59.p59\nend A32Raw59Slice.BB6.Agent32Raw59\n"
    text += "\n#print axioms A32Raw59Slice.BB6.Agent32Raw59Exact.cover\n"
    source.write_text(text)
    dest = linked / "Raw59KernelSlice.olean"
    assert not dest.exists()
    copied.append(dest)
    log = a68.compile_module(source, dest, env, work / "raw59-staged-root.log")
    profiles = gate(log, ["A32Raw59Slice.BB6.Agent32Raw59Exact.cover"])
    audit["relocation"] = {"mode": "staged", "report": report, "output_sha256": a68.sha(dest),
                           "source_sha256": a68.sha(source), "axioms": profiles}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--work", type=Path, required=True)
    ap.add_argument("--parents", nargs="+", choices=(*LABELS, "raw59"), default=list(LABELS))
    args = ap.parse_args()
    assert len(set(args.parents)) == len(args.parents)
    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    generated = work / "generated"
    generated.mkdir()
    version = subprocess.check_output(["lean", "--version"], text=True).strip()
    assert "4.36.0-rc2" in version
    parts = a63.download_canonical64_parts(work)
    imports = champion.reconstruct_champion_imports(work)
    champion_build, champion_log, champion_manifest = champion.compile_champion_closure(work, imports)
    families = a63.canonical64_families(parts) + [
        ("champion", [champion_build], ["TM63RawUpperInterface", "ChampionScoreLowerBound"])]
    linked = work / "linked"
    a68.link_reachable([x[1] for x in families], work, linked, families=families)
    env = dict(os.environ, LEAN_PATH=str(linked))
    canonical64, _, base_axioms = a63.compile_canonical64(linked, env, work)
    membership = HERE / "Canonical59FiveParentMembership.lean"
    log = a68.compile_module(membership, linked / (membership.stem + ".olean"),
                             env, work / "membership.log")
    gate(log, [MEM + ".p" + label[3:] + "_count64" for label in args.parents if label != "raw118"] +
         [MEM + ".p59_count64"])
    accepted, rejected, previous, audits = [], [], [], []
    specs = {spec["label"]: spec for spec in five.PARENTS}
    specs["raw118"] = RAW118_SPEC
    specs["raw113"] = RAW113_SPEC
    for label in args.parents:
        spec = specs[label]
        copied = []
        audit = {"label": label}
        audits.append(audit)
        module, source, names = candidate_source(spec, previous)
        path = generated / (module + ".lean")
        path.write_text(source)
        output = linked / (module + ".olean")
        assert not output.exists()
        try:
            dirs, metadata = five.download_parent(spec, work)
            if label == "raw59":
                if os.environ.get("BB6_RAW59_RELOCATION") == "staged":
                    relocate_raw59_staged(spec, dirs, linked, copied, audit, work, env)
                else:
                    relocate_raw59(spec, dirs, linked, copied, audit, work, env)
            else:
                add_family(spec, dirs, linked, copied, audit)
            if label == "raw118":
                membership_source = ROOT / "im-results" / "agent16-raw118" / "Raw118Canonical64Membership.lean"
                membership_output = linked / "Raw118Canonical64Membership.olean"
                assert not membership_output.exists()
                copied.append(membership_output)
                membership_log = a68.compile_module(
                    membership_source, membership_output, env, work / "raw118-membership.log"
                )
                membership_profiles = gate(membership_log, [
                    "BB6.Agent16Raw118Canonical64Membership.p118_eq_raw118_parent",
                    "BB6.Agent16Raw118Canonical64Membership.p118_root",
                    "BB6.Agent16Raw118Canonical64Membership.p118_parent_count64",
                ])
                audit["membership_axioms"] = membership_profiles
                audit["membership_source_sha256"] = a68.sha(membership_source)
            log = a68.compile_module(path, output, env, work / (label + ".log"))
            profiles = gate(log, names)
        except (AssertionError, subprocess.CalledProcessError, OSError, ValueError) as exc:
            output.unlink(missing_ok=True)
            for dest in reversed(copied):
                dest.unlink(missing_ok=True)
            rejected.append({"label": label, "reason": str(exc)})
            audit["accepted"] = False
            print("RETAINED", label, str(exc), flush=True)
        else:
            accepted.append(dict(metadata, axioms=profiles,
                                 source_sha256=a68.sha(path), olean_sha256=a68.sha(output)))
            previous.append(module)
            audit["accepted"] = True
            print("ACCEPTED", label, flush=True)
        write_json(work / "selected-link-audit.json", audits)
        write_json(work / "selected-progress.json", {"accepted": accepted, "rejected": rejected})
    assert accepted, "no parent passed the compatibility and proof gates"
    source, names = final_source(accepted)
    path = generated / "CanonicalSelectedParentIntegrated.lean"
    path.write_text(source)
    output = linked / (path.stem + ".olean")
    log = a68.compile_module(path, output, env, work / "selected-integration.log")
    profiles = gate(log, names)
    report = {
        "status": "kernel-checked conditional quotient reduction",
        "base_residual_count": 64,
        "remaining_residual_count": 64 - len(accepted),
        "accepted": accepted, "rejected": rejected, "raw59_retained": not any(x["label"] == "raw59" for x in accepted),
        "common_weighted_floor": 6766859,
        "exact_at_champion_score": NS + "Integrated.exact_at_champion_score",
        "axioms": profiles, "canonical64_axioms": base_axioms,
        "canonical64_olean_sha256": a68.sha(canonical64),
        "canonical64_artifact_id": a63.CANONICAL64_ARTIFACT,
        "canonical65_pin": a63.CANONICAL65_PIN, "raw120_pin": a63.RAW120_PIN,
        "champion_manifest_sha256": a68.sha(champion_manifest),
        "base_link_audit_sha256": a68.sha(work / "reachable-link-audit.json"),
        "selected_link_audit_sha256": a68.sha(work / "selected-link-audit.json"),
        "source_sha256": a68.sha(path), "olean_sha256": a68.sha(output),
        "source_revision": subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip(),
        "lean_version": version,
    }
    write_json(work / "selected-integration.json", report)
    print(json.dumps(report, indent=2), flush=True)


if __name__ == "__main__":
    main()
