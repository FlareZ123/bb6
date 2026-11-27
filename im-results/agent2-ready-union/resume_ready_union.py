#!/usr/bin/env python3
"""Resume only the unaccepted ready cut; admit independent, kernel-checked subsets."""
import argparse
import json
import os
from pathlib import Path
import re
import shutil
import subprocess

import assemble_ready_union as u

a68, base, selected = u.a68, u.base, u.selected
HERE = Path(__file__).resolve().parent
REPO = "FlareZ123/bb6"
SHARP_RUN = 45962202844
SHARP_ID = 15181258095
SHARP_SHA = "e87654bcdf3f8f4107c39fae3e61e0df0c95514e2feb63d5ac6b4f6741637243"
SHARP_REV = "5f239debac488882260e22805834028ec435c1bd"
RAW_IDS = ("83", "85", "69", "73", "78", "106", "79")
IMPORTS = dict(zip(("106", "79", "83", "85", "69", "73", "78"),
                   ("Raw106ParentCover", "Raw79ParentCover", "A10Raw83Exact",
                    "Raw85Bound", "Raw69Bound", "Raw73Bound", "Raw78Bound")))


def write(path, obj):
    path.write_text(json.dumps(obj, indent=2, sort_keys=True) + "\n")


def restore_sharp(work, linked, base_report):
    run = a68.api_json(f"repos/{REPO}/actions/runs/{SHARP_RUN}")
    assert run["head_sha"] == SHARP_REV
    info = a68.api_json(f"repos/{REPO}/actions/artifacts/{SHARP_ID}")
    assert info["name"] == "canonical53-four-sharp-after-raw124-thin-delta"
    dirs = a68.download((SHARP_ID, SHARP_RUN, SHARP_SHA), work)
    paths = list((work / "metadata" / str(SHARP_ID)).rglob("delta.json"))
    assert len(paths) == 1
    report = json.loads(paths[0].read_text())
    assert report["status"] == "source-accepted canonical parent-union thin delta"
    assert report["source_revision"] == SHARP_REV
    assert report["previous_residual_count"] == 57
    assert report["remaining_residual_count"] == 53
    assert report["base_artifact_id"] == base.BASE_ARTIFACT_ID
    assert report["base_artifact_sha256"] == base.BASE_ARTIFACT_SHA
    assert report["raw124_delta_artifact_id"] == base.RAW124_DELTA_ID
    assert report["raw124_delta_sha256"] == base.RAW124_DELTA_SHA
    assert report["previous_root_sha256"] == base_report["graft_olean_sha256"]
    assert report["root"] == "Canonical53FourSharpAfterRaw124.olean"
    assert report["exact_at_champion_score"] == "BB6.Agent2Canonical53FourSharp.exact_at_champion_score"
    assert report["exact_at_champion_score"] in report["axioms"]
    assert all(set(v) <= {"propext", "Classical.choice", "Quot.sound"}
               for v in report["axioms"].values())
    objects = report["delta_objects"]
    assert len(objects) == 112
    assert objects[report["root"]] == report["root_sha256"]
    observed = {}
    for d in dirs:
        for f in d.glob("*.olean"):
            assert f.name not in observed, f.name
            observed[f.name] = f
    assert set(observed) == set(objects)
    for name, digest in objects.items():
        assert name == Path(name).name and a68.sha(observed[name]) == digest
        dest = linked / name
        assert not dest.exists(), name
        shutil.copy2(observed[name], dest)
    print(f"Restored {SHARP_ID}: {len(objects)} accepted objects", flush=True)
    return report


def prepare_family(raw, folder, linked, evidence):
    if raw in ("106", "79"):
        dirs, path, report = u.c55.verify_parent(raw, folder)
        spec = dict(u.c55.PARENTS[raw], run_id=u.c55.PARENT_RUN)
        # This producer exports its new modules, but NOT its Canonical64
        # dependencies. Recover ONLY objects authenticated by its link manifest.
        paths = list((folder / "metadata" / str(spec["artifact_id"])).rglob("kernel-link-manifest.json"))
        assert len(paths) == 1, paths
        assert a68.sha(paths[0]) == report["kernel_link_manifest_sha256"]
        manifest = json.loads(paths[0].read_text())
        prefix = Path(subprocess.check_output(["lean", "--print-prefix"], text=True).strip())
        assert manifest["compiler_sha256"] == report["compiler_sha256"] == a68.sha(prefix / "bin" / "lean")
        allowed = {name: {entry["sha256"]} for name, entry in manifest["objects"].items()}
        for collision in manifest["collisions"]:
            assert collision["equal"], collision["module"]
            name = collision["module"]
            assert collision["chosen"] in allowed[name]
            allowed[name].add(collision["other"])
        fallback = folder / "pinned-base-candidates"
        fallback.mkdir()
        for name in allowed:
            assert name == Path(name).name and name.endswith(".olean")
            if not any((d / name).is_file() for d in dirs) and (linked / name).is_file():
                (fallback / name).symlink_to(linked / name)
        dirs = [*dirs, fallback]
        shutil.copy2(paths[0], evidence / f"raw{raw}-producer-link.json")
    elif raw == "83":
        dirs, meta = u.five_parent.download_parent(u.c53.RAW83, folder)
        spec = dict(u.c53.RAW83, metadata=meta)
        path = None
    elif raw == "85":
        dirs, path, _ = u.c53.verify_raw85(folder)
        spec = u.c53.RAW85
    else:
        dirs, _, path, _ = u.ready.verify_legacy(raw, folder)
        spec = u.ready.LEGACY[raw]
    if path:
        shutil.copy2(path, evidence / f"raw{raw}-manifest.json")
    prefix = Path(subprocess.check_output(["lean", "--print-prefix"], text=True).strip())
    result = subprocess.run(
        ["lean", "--run", str(selected.HERE / "WalkImportClosure.lean"),
         str(prefix / "lib" / "lean"), str(len(dirs)), *map(str, dirs), spec["root"]],
        text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if result.returncode:
        raise ValueError(f"{spec['label']} import preflight: {result.stderr.strip()}")
    files = sorted(set(Path(x) for x in result.stdout.splitlines()))
    assert files and all(p.is_file() and p.parent in dirs and p.suffix == ".olean" for p in files)
    assert any(p.name == spec["root"] + ".olean" for p in files)
    borrowed = {}
    if raw in ("106", "79"):
        # No unpinned fallback can reach elaboration. This also verifies every
        # selected producer-owned object against the accepted producer audit.
        for p in files:
            digest = a68.sha(p)
            assert digest in allowed.get(p.name, set()), f"unmatched producer object: {p.name}"
            if p.parent == fallback:
                borrowed[p.name] = digest
    write(evidence / f"raw{raw}-preflight.json", {
        "root": spec["root"], "closure_modules": len(files),
        "authenticated_borrowed_objects": borrowed})
    return spec, dirs


def subset_source(raws, out):
    assert raws and set(raws) <= set(RAW_IDS)
    count = 53 - len(raws)
    ns_short = f"Agent2Canonical{count}Ready" + "R".join(raws)
    module = f"Canonical{count}Ready" + "R".join(raws)
    text = (HERE / "Canonical46SevenReadyAfterSharp.lean").read_text()
    for raw in set(RAW_IDS) - set(raws):
        text = text.replace(f"import {IMPORTS[raw]}\n", "")
        text, n = re.subn(
            rf"(?ms)^(?:abbrev|theorem) p{raw}(?:_\w+)?\b.*?(?=^(?:abbrev |theorem |noncomputable def |#print axioms |end )|\Z)",
            "", text)
        assert n == 4, (raw, n)
        text = re.sub(rf"(?m)^  · exact p{raw}_(?:root|cover)\n", "", text)
        text = re.sub(rf"(?m)^#print axioms p{raw}_\w+\n", "", text)
    # Preserve the original theorem/bullet order, independent of acceptance order.
    ordered = [r for r in ("106", "79", "83", "85", "69", "73", "78") if r in raws]
    text = text.replace("[p106, p79, p83, p85, p69, p73, p78]",
                        "[" + ", ".join("p" + r for r in ordered) + "]")
    text = text.replace("rfl | rfl | rfl | rfl | rfl | rfl | rfl",
                        " | ".join(["rfl"] * len(raws)))
    text = text.replace("Agent2Canonical46SevenReady", ns_short)
    text = text.replace("roster46", f"roster{count}").replace("count46", f"count{count}")
    text = text.replace("roster" + str(count) + ".length = 46",
                        "roster" + str(count) + f".length = {count}")
    path = out / (module + ".lean")
    path.write_text(text)
    names = [f"p{r}_count53" for r in raws] + [f"p{r}_cover" for r in raws]
    names += ["parents_pairwise_distinct", f"count{count}", "all_ready_parents_removed",
              "raw59_retained", "sound_integrated", "exact_at_target", "exact_at_champion_score"]
    ns = "BB6." + ns_short
    return path, ns, [ns + "." + n for n in names]



def preflight_membership(generated, evidence):
    """Elaborate the actual generated list eliminations without parent artifacts."""
    lines = ["import Lean"]
    for count in (1, 2, 7):
        source, _, _ = subset_source(RAW_IDS[:count], generated)
        text = source.read_text()
        roster = re.search(r"(?m)^abbrev readyParents : List PartialMachine :=\s*(\[[^\n]+\])", text)
        assert roster is not None
        ordered = re.findall(r"p(\d+)", roster.group(1))
        assert len(ordered) == count
        lines.append(f"namespace Cardinality{count}")
        lines.extend(f"abbrev p{r} : Nat := {r}" for r in ordered)
        lines.append("abbrev readyParents : List Nat := " + roster.group(1))
        for name, suffix in (("parents_root", "root"), ("parents_cover", "cover"),
                             ("all_ready_parents_removed", None)):
            body = text.split(f"theorem {name} :", 1)[1].split(":= by\n", 1)[1].split("\n\n", 1)[0]
            if suffix:
                hyps = " ".join(f"(p{r}_{suffix} : P p{r})" for r in ordered)
                lines.append(f"theorem {name} (P : Nat → Prop) {hyps} : ∀ p ∈ readyParents, P p := by")
            else:
                lines.append(f"theorem {name} : ∀ p ∈ readyParents, p ≤ {max(map(int, ordered))} := by")
            lines.append(body)
        lines.append(f"end Cardinality{count}")
    fixture = evidence / "GeneratedReadyMembershipPreflight.lean"
    fixture.write_text("\n".join(lines) + "\n")
    result = subprocess.run(["lean", str(fixture)], text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT)
    (evidence / "generated-membership-preflight.log").write_text(result.stdout)
    if result.returncode:
        raise ValueError("generated ready membership preflight failed: " + result.stdout)
    print("PASS: generated root, Cover and removal eliminations for 1, 2, 7 parents", flush=True)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--work", type=Path, required=True)
    args = ap.parse_args()
    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    delta = work / "ready-delta"
    evidence = delta / "evidence"
    evidence.mkdir(parents=True)
    objects = delta / "objects"
    objects.mkdir()
    generated = work / "generated"
    generated.mkdir()
    preflight_membership(generated, evidence)
    linked, _, _, base_report = base.verify_base(work, base.BASE_RUN)
    prior = restore_sharp(work, linked, base_report)
    families, rejected = {}, {}
    # Preflight every input before starting any merge.
    for raw in RAW_IDS:
        folder = work / ("raw" + raw)
        folder.mkdir()
        try:
            families[raw] = prepare_family(raw, folder, linked, evidence)
        except (AssertionError, OSError, ValueError, KeyError, subprocess.CalledProcessError) as e:
            rejected[raw] = repr(e)
            print(f"RETAINED Raw{raw}: {e!r}", flush=True)
    write(evidence / "preflight-status.json", {"passed": list(families), "rejected": rejected})
    accepted, copied, audits = [], [], {}
    root, ns, profiles = None, None, None
    for raw, (spec, dirs) in families.items():
        new = []
        audit = {}
        source, candidate_ns, names = subset_source([*accepted, raw], generated)
        candidate = linked / (source.stem + ".olean")
        try:
            selected.add_family(spec, dirs, linked, new, audit)
            output, ax = u.compile_one(source, linked, evidence, names)
        except (AssertionError, OSError, ValueError, subprocess.CalledProcessError) as e:
            candidate.unlink(missing_ok=True)
            for p in reversed(new):
                p.unlink(missing_ok=True)
            rejected[raw] = repr(e)
            print(f"RETAINED Raw{raw}: {e!r}", flush=True)
        else:
            if root:
                root.unlink()
            root, ns, profiles = output, candidate_ns, ax
            accepted.append(raw)
            copied.extend(new)
            print(f"ACCEPTED Raw{raw}; {53-len(accepted)} retained", flush=True)
        audits[raw] = audit
        write(evidence / "merge-status.json", {"accepted": accepted, "rejected": rejected,
                                                "link_audits": audits})
    assert accepted, "no independent ready parent accepted"
    hashes = {}
    for p in [*copied, root]:
        dest = objects / p.name
        assert not dest.exists(), p.name
        shutil.copy2(p, dest)
        hashes[p.name] = a68.sha(dest)
    write(delta / "delta.json", {
        "status": "source-accepted Canonical53 ready-parent subset",
        "base_artifact_id": base.BASE_ARTIFACT_ID,
        "base_artifact_sha256": base.BASE_ARTIFACT_SHA,
        "raw124_delta_artifact_id": base.RAW124_DELTA_ID,
        "raw124_delta_sha256": base.RAW124_DELTA_SHA,
        "sharp_delta_artifact_id": SHARP_ID, "sharp_delta_sha256": SHARP_SHA,
        "previous_root_sha256": prior["root_sha256"], "previous_residual_count": 53,
        "remaining_residual_count": 53-len(accepted), "accepted": accepted, "rejected": rejected,
        "parents": {r: families[r][0] for r in accepted}, "link_audits": audits,
        "axioms": profiles, "root": root.name, "root_sha256": a68.sha(root),
        "delta_objects": hashes, "exact_at_champion_score": ns + ".exact_at_champion_score",
        "source_revision": subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip()})
    print(f"PASS: {53-len(accepted)} residuals; {len(hashes)} new objects", flush=True)


if __name__ == "__main__":
    main()
