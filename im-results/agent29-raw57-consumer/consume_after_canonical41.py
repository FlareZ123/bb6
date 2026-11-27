#!/usr/bin/env python3
"""Consume an accepted Raw57 parent directly on the accepted Canonical41 delta."""
import argparse
import json
from pathlib import Path
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "agent2-ready-union"))

import extra_ready_union as extra
import resume_ready_union as resume

u, a68, base, selected = extra.u, extra.a68, extra.base, extra.selected

READY_RUN = 46031670976
EXTRA_RUN = 46037391095
EXTRA_ARTIFACT = 15221387172
EXTRA_SHA = "5c95aa1c657a36dea9958216e16f5b5b2c731de262d45a0a2cd42ba088d59697"
EXTRA_ACCEPTED = ["63", "61", "67", "59", "122"]
EXTRA_NS = "BB6.Agent31Canonical41Extra63R61R67R59R122"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def write(path, obj):
    path.write_text(json.dumps(obj, indent=2, sort_keys=True) + "\n")


def restore_extra(work, linked, ready, ready_pin):
    run, item, pin = extra.artifact(EXTRA_RUN, "canonical-extra-ready-thin-delta")
    assert item["id"] == EXTRA_ARTIFACT
    assert pin[2] == EXTRA_SHA
    dirs = a68.download(pin, work)
    paths = list((work / "metadata" / str(EXTRA_ARTIFACT)).rglob("delta.json"))
    assert len(paths) == 1
    report = json.loads(paths[0].read_text())
    assert report["status"] == "source-accepted additional ready-parent subset"
    assert report["source_revision"] == run["head_sha"]
    assert report["ready_predecessor"] == ready_pin
    assert report["previous_root_sha256"] == ready["root_sha256"]
    assert report["previous_residual_count"] == 46
    assert report["remaining_residual_count"] == 41
    assert report["accepted"] == EXTRA_ACCEPTED
    assert not report["rejected"]
    assert report["exact_at_champion_score"] == EXTRA_NS + ".exact_at_champion_score"
    assert report["exact_at_champion_score"] in report["axioms"]
    assert all(set(v) <= ALLOWED for v in report["axioms"].values())
    objects = report["delta_objects"]
    observed = {}
    for d in dirs:
        for f in d.glob("*.olean"):
            if f.name in observed:
                # Artifacts may package an identical shared dependency twice.
                # Permit only byte-identical duplicate names; incompatible
                # duplicates remain a hard source-integrity failure.
                assert a68.sha(observed[f.name]) == a68.sha(f), (
                    f"conflicting {f.name}: {observed[f.name]} vs {f}")
                continue
            observed[f.name] = f
    assert set(objects) == set(observed)
    assert objects[report["root"]] == report["root_sha256"]
    for name, digest in objects.items():
        assert name == Path(name).name
        assert a68.sha(observed[name]) == digest
        target = linked / name
        assert not target.exists(), name
        shutil.copy2(observed[name], target)
    return report, {
        "run_id": EXTRA_RUN,
        "artifact_id": EXTRA_ARTIFACT,
        "artifact_sha256": EXTRA_SHA,
        "root_sha256": report["root_sha256"],
    }


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--work", type=Path, required=True)
    ap.add_argument("--raw57-run-id", type=int, required=True)
    args = ap.parse_args()

    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    delta = work / "canonical40-delta"
    evidence = delta / "evidence"
    objects = delta / "objects"
    evidence.mkdir(parents=True)
    objects.mkdir()

    linked, _, _, base_report = base.verify_base(work, base.BASE_RUN)
    sharp = resume.restore_sharp(work, linked, base_report)
    ready, ready_ns, ready_pin = extra.restore_ready(work, linked, sharp, READY_RUN)
    assert ready["remaining_residual_count"] == 46
    prior, prior_pin = restore_extra(work, linked, ready, ready_pin)
    assert prior["remaining_residual_count"] == 41

    parent_dir = work / "raw57"
    parent_dir.mkdir()
    spec, dirs = extra.prepare_prefix("57", args.raw57_run_id, parent_dir, evidence)
    copied = []
    audit = {}
    selected.add_family(spec, dirs, linked, copied, audit)

    source, ns, names = extra.generate(["57"], prior, EXTRA_NS, work)
    assert ns == "BB6.Agent31Canonical40Extra57"
    root, profiles = u.compile_one(source, linked, evidence, names)
    copied.append(root)

    hashes = {}
    for src in copied:
        dst = objects / src.name
        assert not dst.exists(), dst
        shutil.copy2(src, dst)
        hashes[dst.name] = a68.sha(dst)

    report = {
        "status": "source-accepted Raw57 successor of Canonical41",
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
            ["git", "rev-parse", "HEAD"], text=True).strip(),
        "exact_at_champion_score": ns + ".exact_at_champion_score",
    }
    assert report["exact_at_champion_score"] in profiles
    assert all(set(v) <= ALLOWED for v in profiles.values())
    write(delta / "delta.json", report)
    shutil.rmtree(parent_dir)
    print("PASS: Raw57 consumed directly on Canonical41; 40 residuals", flush=True)


if __name__ == "__main__":
    main()
