"""Reassemble Raw115 from the 53 original and one recovered source-audit shard.

The recovery job compiled Sparse8, not the unrelated modified Sparse7 sources
that its artifact also uploaded. Use the original generated-source ZIP as
the only generated-source authority. Reject every conflicting object, verify
each producer's exact recursive import cut, and kernel-check the parent.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor
from hashlib import file_digest
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import subprocess
import zipfile

REPO = "FlareZ123/bb6"
THEOREM = "BB6.Agent47Raw115.all_completions"
TABLE = "1RB---_1RC---_0RD---_1LD1RE_---0RD_------"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def sha(path):
    with path.open("rb") as f:
        return file_digest(f, "sha256").hexdigest()


def api(path):
    return json.loads(subprocess.check_output(["gh", "api", path]))


def get_archive(pin, directory):
    aid = pin["artifact_id"]
    job = api(f"repos/{REPO}/actions/jobs/{pin['job_id']}")
    assert job["run_id"] == pin["run_id"], job
    assert job["head_sha"] == pin["workflow_head_sha"], job
    assert job["name"] == pin["job_name"] and job["conclusion"] == "success", job
    info = api(f"repos/{REPO}/actions/artifacts/{aid}")
    assert info["workflow_run"]["id"] == pin["run_id"], info
    assert info["workflow_run"]["head_sha"] == pin["workflow_head_sha"], info
    assert info["name"] == pin["name"] and not info["expired"], info
    assert info["digest"] == pin["digest"], info
    archive = directory / f"{aid}.zip"
    with archive.open("wb") as out:
        subprocess.run(["gh", "api", f"repos/{REPO}/actions/artifacts/{aid}/zip"],
                       stdout=out, check=True)
    assert "sha256:" + sha(archive) == pin["digest"], aid
    print(f"Verified {pin['name']} ({aid}, job {pin['job_id']})", flush=True)
    return archive


def extract_sources(archive, root):
    with zipfile.ZipFile(archive) as z:
        names = [n for n in z.namelist() if not n.endswith("/")]
        assert len(names) == len(set(names)) == 456
        for name in names:
            assert re.fullmatch(r"Raw115\w*\.lean", name), name
            dest = root / name
            data = z.read(name)
            if dest.exists():
                assert dest.read_bytes() == data, dest
            else:
                dest.write_bytes(data)


def expected_shards(root):
    expected = {}
    for i in range(24):
        b = f"{i:02d}"
        if (root / f"Raw115Kid{b}_00.lean").is_file():
            for k in (0, 6, 12, 18):
                expected[f"raw115-audit-{b}-{k}"] = [
                    f"Raw115Kid{b}_{j:02d}" for j in range(k, k + 6)]
        else:
            expected[f"raw115-audit-{b}--1"] = [f"Raw115Branch{b}"]
    expected["raw115-recovered-17-12"] = expected.pop("raw115-audit-17-12")
    return expected


def merge_objects(pin, archive, audit, origins):
    """Use only compiled objects. In particular, ignore all recovery .lean files."""
    aid = pin["artifact_id"]
    is_recovery = pin["name"] == "raw115-recovered-17-12"
    provided = set()
    with zipfile.ZipFile(archive) as z:
        for item in z.infolist():
            p = PurePosixPath(item.filename)
            if p.suffix != ".olean":
                continue
            assert str(p.parent) == ("tmp/recovered" if is_recovery else "."), p
            assert re.fullmatch(r"[A-Za-z_]\w*\.olean", p.name), p
            module = p.stem
            assert module not in provided, (aid, module)
            provided.add(module)
            dest = audit / p.name
            data = z.read(item)
            if dest.exists():
                assert dest.read_bytes() == data, (
                    "conflicting compiled module", module, origins[module], aid)
            else:
                dest.write_bytes(data)
            origins.setdefault(module, []).append(aid)
    assert set(pin["roots"]) <= provided, (aid, pin["roots"] - provided)
    return provided


def compile_module(module, audit):
    output = audit / (module + ".olean")
    assert not output.exists(), output
    log = subprocess.check_output(["lean", "-o", output.name, module + ".lean"],
                                  cwd=audit, text=True, stderr=subprocess.STDOUT,
                                  env=dict(os.environ, LEAN_PATH=str(audit)))
    print(log, end="", flush=True)
    return log


def audit_axioms(log):
    profiles = {}
    for name, values in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log):
        profiles[name] = sorted(s.strip() for s in values.split(",") if s.strip())
    for name in re.findall(r"'([^']+)' does not depend on any axioms", log):
        profiles[name] = []
    required = [THEOREM, "BB6.Agent47Raw115.sound",
                "BB6.Agent47Raw115.residual_count"]
    assert set(required) <= profiles.keys(), profiles
    assert all(set(v) <= ALLOWED for v in profiles.values()), profiles
    return profiles


def verify_producer_closures(manifest, pins, provided, assembled):
    modules = {m["module"]: m for m in manifest["modules"]}
    assert len(modules) == manifest["module_count"]
    cache = {}

    def closure(m):
        if m not in cache:
            cache[m] = {m}.union(*(closure(d) for d in modules[m]["project_imports"]))
        return cache[m]

    for pin in pins:
        aid = pin["artifact_id"]
        expected = set().union(*(closure(m) for m in pin["roots"]))
        actual = provided[aid]
        assert expected == actual, (aid, "missing", sorted(expected - actual),
                                    "extra", sorted(actual - expected))
    all_provided = set().union(*provided.values())
    assert set(modules) == all_provided | assembled
    assert not all_provided & assembled
    return len(modules)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--pins", type=Path, required=True)
    p.add_argument("--work", type=Path, required=True)
    args = p.parse_args()
    pins_path = args.pins.resolve()
    spec = json.loads(pins_path.read_text())
    pins = spec["artifacts"]
    source, shards = pins[0], pins[1:]
    assert len(shards) == 54 and len({a["artifact_id"] for a in pins}) == 55
    assert source["name"] == "raw115-generated-source" and not source["roots"]
    repo = Path.cwd()
    root = repo / "im-results/agent47-raw115-cut"
    actual_rev = subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip()
    assert actual_rev == spec["source_revision"], actual_rev
    for run, rev in [(spec["source_run"], spec["source_revision"]),
                     (spec["recovery_run"], spec["recovery_revision"])]:
        info = api(f"repos/{REPO}/actions/runs/{run}")
        assert info["head_sha"] == rev and info["status"] == "completed", info
    # The original failed run's generate and preflight jobs both succeeded.
    preflight = api(f"repos/{REPO}/actions/jobs/139694555128")
    assert preflight["run_id"] == spec["source_run"]
    assert preflight["head_sha"] == actual_rev and preflight["conclusion"] == "success"
    version = subprocess.check_output(["lean", "--version"], text=True).strip()
    assert "4.36.0-rc2" in version and "b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a" in version, version
    prefix = Path(subprocess.check_output(["lean", "--print-prefix"], text=True).strip())
    compiler = sha(prefix / "bin/lean")
    assert compiler == spec["lean_binary_sha256"], compiler

    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    archives = work / "archives"
    archives.mkdir()
    audit = work / "audit"
    audit.mkdir()
    extract_sources(get_archive(source, archives), root)
    expected = expected_shards(root)
    assert {a["name"]: a["roots"] for a in shards} == expected
    origins, provided = {}, {}
    with ThreadPoolExecutor(max_workers=4) as pool:
        for pin, archive in zip(shards, pool.map(lambda a: get_archive(a, archives), shards)):
            provided[pin["artifact_id"]] = merge_objects(pin, archive, audit, origins)
            archive.unlink()
    print(f"Merged {len(origins)} distinct objects; all overlapping bytes match.", flush=True)
    for src in root.glob("Raw115*.lean"):
        shutil.copy2(src, audit / src.name)
    assembled = set()
    for i in range(24):
        branch = f"Raw115Branch{i:02d}"
        if branch not in origins:
            assert all(f"Raw115Kid{i:02d}_{j:02d}" in origins for j in range(24))
            compile_module(branch, audit)
            assembled.add(branch)
    log = compile_module("Raw115Data", audit)
    assembled.add("Raw115Data")
    (work / "root.log").write_text(log)
    axioms = audit_axioms(log)

    subprocess.run(["python", "im-results/agent13-coverage/unpack.py"], check=True)
    manifest_path = audit / "source-manifest.json"
    subprocess.run(["python", "tools/lean_compile_closure.py", "--manifest-only",
                    "--artifact-dir", str(audit), "--manifest", str(manifest_path),
                    "--label", "raw115", "--theorem", THEOREM, "--parent-table", TABLE,
                    "--weighted-bound", "7014", "--artifact-name", "raw115-certified-root",
                    "--provenance-input", str(root / "generate.py"),
                    "--provenance-input", str(root / "symbolic.py"),
                    "--provenance-input", str(root / "far-bank.txt"),
                    "--provenance-input", str(pins_path),
                    str(root / "Raw115Data.lean")], check=True)
    manifest = json.loads(manifest_path.read_text())
    assert manifest["proof_source_revision"] == actual_rev
    assert manifest["lean_binary"]["sha256"] == compiler
    count = verify_producer_closures(manifest, shards, provided, assembled)
    report = {"source_revision": actual_rev, "source_artifact": source,
              "producer_pins": shards, "compiler": version, "compiler_sha256": compiler,
              "object_origins": origins, "assembled_modules": sorted(assembled),
              "exact_shard_closures_checked": len(shards), "module_count": count,
              "shared_modules": sum(len(v) > 1 for v in origins.values()),
              "axioms": axioms, "source_manifest_sha256": sha(manifest_path),
              "pins_sha256": sha(pins_path)}
    (audit / "producer-audit.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"Accepted Raw115 parent; {count} exact source modules, 54 complete producer cuts.",
          flush=True)


if __name__ == "__main__":
    main()
