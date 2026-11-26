#!/usr/bin/env python3
"""Consume the accepted Canonical60 plus a successful independent Raw59 slice.

The large Raw59 artifact is streamed only once; only new objects are extracted.
All of its reached shared objects are checked against the accepted Canonical60
environment before the new ordinary Lean roster consumer is compiled.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import subprocess
import zipfile

import assemble_canonical68 as a68

HERE = Path(__file__).resolve().parent
REPO = "FlareZ123/bb6"
BASE_PIN = (15146101833, 45876657378, "68b3819703aa7d131a6e2021b083760e8e555ee499357c73b4b95931002860b6")
BASE_REV = "3f923338bb7a95403a8fa089741f59ad892d4e70"
BASE_SHA = "d538c5479fb948c59f00e5735673884dec86abaec79b702ea2e6f6ba3ba5ba1e"
NS = "BB6.Agent32Canonical59Raw59Graft"


def report_in_zip(z, name):
    files = [x for x in z.infolist() if not x.is_dir() and PurePosixPath(x.filename).name == name]
    assert len(files) == 1, (name, [x.filename for x in files])
    return json.loads(z.read(files[0]))


def verify_base(work):
    run = a68.api_json(f"repos/{REPO}/actions/runs/{BASE_PIN[1]}")
    assert run["conclusion"] == "success" and run["head_sha"] == BASE_REV
    dirs = a68.download(BASE_PIN, work)
    choices = [p for p in dirs if (p / "CanonicalSelectedParentIntegrated.olean").is_file()]
    assert len(choices) == 1
    linked = choices[0]
    assert a68.sha(linked / "CanonicalSelectedParentIntegrated.olean") == BASE_SHA
    reports = list((work / "metadata" / str(BASE_PIN[0])).rglob("selected-integration.json"))
    assert len(reports) == 1
    report = json.loads(reports[0].read_text())
    assert report["source_revision"] == BASE_REV and report["remaining_residual_count"] == 60
    assert {x["label"] for x in report["accepted"]} == {"raw119", "raw115", "raw58", "raw108"}
    assert report["raw59_retained"] and not report["rejected"]
    assert report["olean_sha256"] == BASE_SHA
    return linked, report


def add_raw59(work, linked, run_id):
    run = a68.api_json(f"repos/{REPO}/actions/runs/{run_id}")
    assert run["conclusion"] == "success", run.get("conclusion")
    artifacts = a68.api_json(f"repos/{REPO}/actions/runs/{run_id}/artifacts")["artifacts"]
    candidates = [x for x in artifacts if x["name"] in (
        "canonical64-raw59-slice-integrated", "canonical64-raw59-staged-integrated")]
    assert len(candidates) == 1
    artifact = candidates[0]
    assert not artifact["expired"] and artifact["digest"].startswith("sha256:")
    aid = artifact["id"]
    expected = artifact["digest"].removeprefix("sha256:")
    archive = work / f"{aid}.zip"
    with archive.open("wb") as f:
        subprocess.run(["gh", "api", f"repos/{REPO}/actions/artifacts/{aid}/zip"], stdout=f, check=True)
    assert a68.sha(archive) == expected
    audit = []
    new_objects = []
    with zipfile.ZipFile(archive) as z:
        report = report_in_zip(z, "selected-integration.json")
        assert report["source_revision"] == run["head_sha"]
        assert report["base_residual_count"] == 64 and report["remaining_residual_count"] == 63
        assert not report["raw59_retained"] and not report["rejected"]
        assert len(report["accepted"]) == 1 and report["accepted"][0]["label"] == "raw59"
        claim = report["accepted"][0]
        assert claim["theorem"] == "BB6.Agent32Raw59Exact.cover"
        assert claim["bound"] <= 6766859
        entries = {}
        for i in z.infolist():
            if i.is_dir():
                continue
            p = PurePosixPath(i.filename)
            if p.suffix == ".olean":
                assert p.name not in entries, f"duplicate producer object {p.name}"
                entries[p.name] = i
        for name, i in entries.items():
            dst = linked / name
            if not dst.exists():
                with z.open(i) as src, dst.open("wb") as out:
                    shutil.copyfileobj(src, out)
                new_objects.append(name)
        root = linked / "CanonicalSelectedRaw59.olean"
        assert root.is_file() and a68.sha(root) == claim["olean_sha256"]
        prefix = Path(subprocess.check_output(["lean", "--print-prefix"], text=True).strip())
        reached = subprocess.check_output(
            ["lean", "--run", str(HERE / "WalkImportClosure.lean"),
             str(prefix / "lib" / "lean"), "1", str(linked), "CanonicalSelectedRaw59"],
            text=True)
        compare = HERE.parent / "agent13-raw125" / "CompareKernelImports.lean"
        reached_names = {Path(p).name for p in reached.splitlines()}
        for name in sorted(reached_names):
            assert name in entries, f"producer closure lacks {name}"
            local = linked / name
            with z.open(entries[name]) as f:
                digest = hashlib.file_digest(f, "sha256").hexdigest()
            chosen = a68.sha(local)
            equal = chosen == digest
            if not equal:
                scratch = work / "compare" / name
                scratch.parent.mkdir(exist_ok=True)
                with z.open(entries[name]) as f, scratch.open("wb") as out:
                    shutil.copyfileobj(f, out)
                proc = subprocess.run(["lean", "--run", str(compare), str(local), str(scratch)],
                                      stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
                scratch.unlink()
                assert proc.returncode == 0, (name, proc.stdout)
            audit.append({"module": name, "producer_sha256": digest, "chosen_sha256": chosen,
                          "exact_bytes": equal, "kernel_equal": True})
        for name in new_objects:
            if name not in reached_names:
                (linked / name).unlink()
    archive.unlink()
    (work / "raw59-link-audit.json").write_text(json.dumps(audit, indent=2) + "\n")
    print(f"Verified Raw59 delta: {len(reached_names)} reached objects, "
          f"{len(set(new_objects) & reached_names)} new modules", flush=True)
    return {"run_id": run_id, "revision": run["head_sha"], "artifact_id": aid,
            "artifact_sha256": expected, "claim": claim,
            "link_audit_sha256": a68.sha(work / "raw59-link-audit.json")}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--work", required=True, type=Path)
    p.add_argument("--raw59-run-id", required=True, type=int)
    args = p.parse_args()
    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    linked, base_report = verify_base(work)
    delta = add_raw59(work, linked, args.raw59_run_id)
    source = HERE / "Canonical59Raw59Graft.lean"
    output = linked / (source.stem + ".olean")
    env = dict(os.environ, LEAN_PATH=str(linked))
    log = a68.compile_module(source, output, env, work / "canonical59-raw59-graft.log")
    assert not re.search(r"sorryAx|native_decide", log)
    names = [NS + "." + n for n in ("p59_count60", "p59_count59", "count59", "parents_root",
             "parents_cover", "sound_integrated", "exact_at_target", "exact_at_champion_score")]
    profiles = a68.gate(log, names)
    report = {"status": "source-checked Canonical59 Raw59 graft", "base_residual_count": 60,
              "remaining_residual_count": 59, "base_pin": BASE_PIN,
              "base_revision": BASE_REV, "base_olean_sha256": BASE_SHA,
              "raw59": delta, "axioms": profiles, "source_sha256": a68.sha(source),
              "olean_sha256": a68.sha(output), "exact_at_champion_score": NS + ".exact_at_champion_score",
              "source_revision": subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip()}
    (work / "canonical59-raw59-graft.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2), flush=True)


if __name__ == "__main__":
    main()
