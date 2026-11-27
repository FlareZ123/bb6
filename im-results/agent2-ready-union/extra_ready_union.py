#!/usr/bin/env python3
"""Consume additional accepted parents on the actual accepted ready-subset lineage."""
import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess

import resume_ready_union as resume
from assemble_canonical59_raw59_graft import add_raw59

u, a68, base, selected = resume.u, resume.a68, resume.base, resume.selected
HERE, REPO = resume.HERE, resume.REPO
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
PARENTS = {
    "63": ("BB6.Agent2Raw63", 358, "1RB---_1RC1LA_0RD---_1LD1RE_---0LB_------"),
    "61": ("BB6.Agent31Raw61", 1962, "1RB---_1RC0LA_0RD---_1LD1RE_---0LB_------"),
    "67": ("BB6.Agent10Raw67", 808, "1RB---_1RC1LB_0RD---_1LD1RE_---0LB_------"),
}
RUNS = {"63": 45948590270, "61": 46032302566, "67": 46034483043, "59": 45897242410}


def artifact(run_id, name):
    run = a68.api_json(f"repos/{REPO}/actions/runs/{run_id}")
    if run["conclusion"] != "success":
        raise ValueError(f"producer {run_id} not accepted: {run['status']}/{run['conclusion']}")
    result = a68.api_json(f"repos/{REPO}/actions/runs/{run_id}/artifacts")
    matches = [x for x in result["artifacts"] if x["name"] == name and not x["expired"]]
    assert len(matches) == 1, (run_id, name)
    item = matches[0]
    assert item["digest"].startswith("sha256:")
    return run, item, (item["id"], run_id, item["digest"].removeprefix("sha256:"))


def restore_ready(work, linked, prior, run_id):
    run, item, spec = artifact(run_id, "canonical-ready-resumed-thin-delta")
    dirs = a68.download(spec, work)
    paths = list((work / "metadata" / str(item["id"])).rglob("delta.json"))
    assert len(paths) == 1
    report = json.loads(paths[0].read_text())
    assert report["status"] == "source-accepted Canonical53 ready-parent subset"
    assert report["source_revision"] == run["head_sha"]
    for key in ("base_artifact_id", "base_artifact_sha256",
                "raw124_delta_artifact_id", "raw124_delta_sha256"):
        assert report[key] == prior[key], key
    assert report["sharp_delta_artifact_id"] == resume.SHARP_ID
    assert report["sharp_delta_sha256"] == resume.SHARP_SHA
    assert report["previous_root_sha256"] == prior["root_sha256"]
    assert report["previous_residual_count"] == 53
    raws = report["accepted"]
    assert raws and len(raws) == len(set(raws)) and set(raws) <= set(resume.RAW_IDS)
    count = 53 - len(raws)
    assert report["remaining_residual_count"] == count
    suffix = f"Canonical{count}Ready" + "R".join(raws)
    ns = "BB6.Agent2" + suffix
    assert report["root"] == suffix + ".olean"
    assert report["exact_at_champion_score"] == ns + ".exact_at_champion_score"
    assert report["exact_at_champion_score"] in report["axioms"]
    assert all(set(v) <= ALLOWED for v in report["axioms"].values())
    objects = report["delta_objects"]
    observed = {}
    for d in dirs:
        for f in d.glob("*.olean"):
            assert f.name not in observed, f.name
            observed[f.name] = f
    assert set(objects) == set(observed)
    assert objects[report["root"]] == report["root_sha256"]
    for name, digest in objects.items():
        assert name == Path(name).name and a68.sha(observed[name]) == digest
        dest = linked / name
        assert not dest.exists(), name
        shutil.copy2(observed[name], dest)
    return report, ns, {"run_id": run_id, "artifact_id": item["id"],
                        "artifact_sha256": spec[2], "root_sha256": report["root_sha256"]}


def prepare_prefix(raw, run_id, folder, evidence):
    ns, bound, table = PARENTS[raw]
    module = f"Raw{raw}ParentCover"
    run, item, pin = artifact(run_id, f"raw{raw}-prefix-parent-certified")
    dirs = a68.download(pin, folder)
    metadata = folder / "metadata" / str(item["id"])
    manifests = []
    for path in metadata.rglob("*.json"):
        report = json.loads(path.read_text())
        if (report.get("claim") or {}).get("theorem") == ns + ".literal_cover":
            manifests.append((path, report))
    assert len(manifests) == 1
    path, report = manifests[0]
    assert report["proof_source_revision"] == run["head_sha"]
    assert report["claim"]["parent_table"] == table
    assert report["claim"]["weighted_bound"] == bound
    prefix = Path(subprocess.check_output(["lean", "--print-prefix"], text=True).strip())
    assert report["lean_binary"]["sha256"] == a68.sha(prefix / "bin" / "lean")
    assert report["lean_version"] == subprocess.check_output(["lean", "--version"], text=True).strip()
    assert any(x["module"] == module for x in report["roots"])
    allowed = {x["module"] + ".olean": x["olean_sha256"] for x in report["modules"]}
    assert len(allowed) == len(report["modules"])
    for d in dirs:
        for f in d.glob("*.olean"):
            assert allowed[f.name] == a68.sha(f), f
    shutil.copy2(path, evidence / f"raw{raw}-manifest.json")
    return {"label": "raw" + raw, "root": module, "run_id": run_id,
            "artifact_id": item["id"], "artifact_sha256": pin[2],
            "revision": run["head_sha"], "theorem": ns + ".literal_cover",
            "bound": bound, "table": table}, dirs


def generate(raws, prior, prior_ns, folder):
    n = prior["remaining_residual_count"]
    count = n - len(raws)
    module = f"Canonical{count}Extra" + "R".join(raws)
    ns = "BB6.Agent31" + module
    text = ["import " + Path(prior["root"]).stem]
    text += ["import Raw59KernelSlice" if r == "59" else f"import Raw{r}ParentCover" for r in raws]
    template = (HERE / "Canonical46SevenReadyAfterSharp.lean").read_text()
    header = template[template.index("set_option"):template.index("abbrev p106")]
    text.append(header.replace("BB6.Agent2Canonical46SevenReady", ns))
    text.append(f"noncomputable abbrev baseRoster := {prior_ns}.roster{n}")
    for raw in raws:
        if raw == "59":
            parent = "BB6.Agent31Canonical59Membership.p59"
            extra = """
theorem p59_source_eq : p59 = A32Raw59Slice.BB6.Agent32Raw59.p59 :=
  sameTable_sound (by decide)

theorem p59_cover : Cover (WeightedBound 6766859) p59 := by
  rw [p59_source_eq]
  exact liftCover (by decide) A32Raw59Slice.BB6.Agent32Raw59Exact.cover
"""
        else:
            pns, bound, _ = PARENTS[raw]
            parent = pns + ".literalParent"
            extra = f"""
theorem p{raw}_cover : Cover (WeightedBound 6766859) p{raw} := by
  apply Cover.leaf
  intro m hm k d hk hd
  exact Nat.le_trans
    ({pns}.literal_cover.sound m hm k d hk hd)
    (by decide : {bound} ≤ 6766859)
"""
        text.append(f"""
abbrev p{raw} : PartialMachine := {parent}
theorem p{raw}_count{n} :
    (baseRoster.filter (fun e => sameTable e.2 p{raw})).length = 1 := by decide
theorem p{raw}_root : p{raw} initialSlot = some (some ⟨true,true,1⟩) := by decide
""")
        text.append(extra)
    text.append("abbrev readyParents : List PartialMachine := [" + ", ".join("p" + r for r in raws) + "]")
    text.append("""
theorem parents_pairwise_distinct :
    List.Pairwise (fun p q => sameTable p q = false) readyParents := by decide
""")
    for suffix, goal in [("root", "p initialSlot = some (some ⟨true,true,1⟩)"),
                         ("cover", "Cover (WeightedBound 6766859) p")]:
        text.append(f"""
theorem parents_{suffix} : ∀ p ∈ readyParents, {goal} := by
  intro p hp
  simp only [readyParents, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with """ + " | ".join("rfl" for _ in raws))
        text.extend(f"  · exact p{r}_{suffix}" for r in raws)
    text.append(f"""
noncomputable def roster{count} := removeParents readyParents baseRoster
theorem count{count} : roster{count}.length = {count} := by decide
theorem all_ready_parents_removed :
    ∀ p ∈ readyParents, (roster{count}.filter (fun e => sameTable e.2 p)).length = 0 := by
  intro p hp
  simp only [readyParents, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with """ + " | ".join("rfl" for _ in raws) + " <;> decide")
    text.append(f"""
theorem raw59_count :
    (roster{count}.filter
      (fun e => sameTable e.2 BB6.Agent31Canonical59Membership.p59)).length = {int("59" not in raws)} := by decide
""")
    tail = template[template.index("theorem sound_integrated"):template.index("#print axioms")]
    text.append(tail.replace("BB6.Agent2Canonical53FourSharp", prior_ns)
                .replace("roster53", f"roster{n}").replace("roster46", f"roster{count}"))
    names = [f"p{r}_count{n}" for r in raws] + [f"p{r}_cover" for r in raws]
    if "59" in raws:
        names.append("p59_source_eq")
    names += ["parents_pairwise_distinct", f"count{count}", "all_ready_parents_removed",
              "raw59_count", "sound_integrated", "exact_at_target", "exact_at_champion_score"]
    text.extend("#print axioms " + x for x in names)
    text.append("end " + ns)
    path = folder / (module + ".lean")
    path.write_text("\n".join(text) + "\n")
    return path, ns, [ns + "." + x for x in names]


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--work", type=Path, required=True)
    ap.add_argument("--ready-run-id", type=int, required=True)
    ap.add_argument("--parents", default=json.dumps(RUNS), help="JSON map of raw ID to producer run ID")
    args = ap.parse_args()
    runs = json.loads(args.parents)
    assert runs and set(runs) <= set(RUNS) and all(type(v) is int and v > 0 for v in runs.values())
    # Refuse a stale branch or failed predecessor before restoring large objects.
    artifact(args.ready_run_id, "canonical-ready-resumed-thin-delta")
    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    delta = work / "extra-delta"
    evidence = delta / "evidence"
    evidence.mkdir(parents=True)
    generated = work / "generated"
    generated.mkdir()
    linked, _, _, base_report = base.verify_base(work, base.BASE_RUN)
    sharp = resume.restore_sharp(work, linked, base_report)
    prior, prior_ns, ready_pin = restore_ready(work, linked, sharp, args.ready_run_id)
    start = prior["remaining_residual_count"]
    accepted, rejected, audits, claims = [], {}, {}, {}
    copied = []
    root, ns, profiles = None, None, None
    for raw, run_id in runs.items():
        folder = work / ("raw" + raw)
        folder.mkdir()
        before = set(linked.glob("*.olean"))
        source, candidate_ns, names = generate([*accepted, raw], prior, prior_ns, generated)
        audit = {}
        try:
            if raw == "59":
                claims[raw] = add_raw59(folder, linked, run_id, parent_only=True, repair_exact_alias=True)
                shutil.copy2(folder / "raw59-link-audit.json", evidence)
                alias_dir = folder / "raw59-exact-bridge-alias"
                if alias_dir.exists():
                    shutil.copytree(alias_dir, evidence / alias_dir.name)
            else:
                spec, dirs = prepare_prefix(raw, run_id, folder, evidence)
                claims[raw] = spec
                selected.add_family(spec, dirs, linked, [], audit)
            output, ax = u.compile_one(source, linked, evidence, names)
        except (AssertionError, OSError, ValueError, KeyError, subprocess.CalledProcessError) as exc:
            for f in set(linked.glob("*.olean")) - before:
                f.unlink()
            rejected[raw] = repr(exc)
            print(f"RETAINED Raw{raw}: {exc!r}", flush=True)
        else:
            new = set(linked.glob("*.olean")) - before - {output}
            if root:
                root.unlink()
            root, ns, profiles = output, candidate_ns, ax
            accepted.append(raw)
            copied.extend(sorted(new))
            print(f"ACCEPTED Raw{raw}: {start-len(accepted)} retained", flush=True)
        audits[raw] = audit
        resume.write(evidence / "progress.json", {"accepted": accepted, "rejected": rejected, "audits": audits})
        shutil.rmtree(folder)
    assert accepted, "no extra parent accepted"
    objects = delta / "objects"
    objects.mkdir()
    hashes = {}
    for path in [*copied, root]:
        dst = objects / path.name
        assert not dst.exists()
        shutil.copy2(path, dst)
        hashes[path.name] = a68.sha(dst)
    resume.write(delta / "delta.json", {
        "status": "source-accepted additional ready-parent subset",
        "ready_predecessor": ready_pin, "previous_root_sha256": prior["root_sha256"],
        "previous_residual_count": start, "remaining_residual_count": start - len(accepted),
        "accepted": accepted, "rejected": rejected, "parents": {r: claims[r] for r in accepted},
        "link_audits": audits, "axioms": profiles, "root": root.name,
        "root_sha256": hashes[root.name], "delta_objects": hashes,
        "exact_at_champion_score": ns + ".exact_at_champion_score",
        "source_revision": subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip()})


if __name__ == "__main__":
    main()
