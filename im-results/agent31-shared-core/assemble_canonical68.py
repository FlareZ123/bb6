"""Link the pinned, independently source-audited parent proof objects.

This is an integration experiment, not a new source audit of the parents.
Every input ZIP is identified by its successful source-audit job and digest.
The existing kernel comparator is used on all differing duplicate objects.
The final consumer is elaborated by the pinned Lean kernel in a single import
environment; a missing or incompatible dependency is a hard failure.
"""
from concurrent.futures import ThreadPoolExecutor
from hashlib import file_digest
from pathlib import Path, PurePosixPath
import argparse
import json
import os
import re
import shutil
import subprocess
import zipfile

REPO = "FlareZ123/bb6"
HERE = Path(__file__).resolve().parent
# (artifact id, successful run id, sha256, source revision).
# Canonical76's exactness job succeeded although another job in that run failed.
PINS = [
    (14997966221, 45554648116, "b55e4c939da70aaa4d2f50f5721b9183ab776682f1b682f647ee27aa6cc5da17"),
    (15043876968, 45647053824, "cfa00335da67bb71caf725c8a8fa6f0fd7c257035a4dfddc43531282924e305c"),
    (15057164854, 45686044022, "0d4d87e1d342d3771666a292cef60051a5aad7fbd52a26215f4859b924282c5d"),
    (15035255805, 45633764095, "f68d8324508ec0c7e50d60a23c05a2d793390b379a3edd5adc65c5a0cb788ae0"),
    (15014940132, 45597857116, "5a5302602f5bdf563c7fc135919af39d6599d9e5ae745c90a87812162b87f0bb"),
    (15002070122, 45568081544, "fd07cc60a538ae2081d1d4d4e440fbe79e5432e75cd075597023203f3fbae951"),
    (15024725827, 45616647230, "f8ea8d2a09cc9230f92f442f1c7f09b61a958565dd530c46e7c98b58b4dc8e2e"),
    (15062767168, 45700813110, "3d55130f37b32fbda54ac9e0e5c1e5194b5d602570116f72ee925cb2762193db"),
    (15072483796, 45722543448, "a7d9207b3f167bdca634c04a5169ff8e670f6fc880d200a50292ca6f415aee75"),
    (14997867504, 45561386072, "106cef851634988cc4edf0ceac7c206fa8c111dfd630ac3c1f3673302cbb3a12"),
    (14998421867, 45561386072, "876ad727f0794266432ac0243241710ece5b3fb8971c85910746a460750bfcc0"),
    (14998473632, 45561386072, "621af46fe6b85a54e32c4cf1816898bd8bff9bb6a02a04176f5389b98ebdb4d3"),
    (14998667570, 45561386072, "77b046f2234cc40675c4b6106b83b8ffaa49442b94a6a861952993638a858f57"),
    (14998821667, 45561386072, "e7f82d560d0cd694883445c783a5a5f63c82ac5ade505b640f2ec195f2e4c68e"),
    (14999240431, 45561386072, "8272cda64fa6884cf69796aee1051e1727e81939dcdcd7badea18d9e8f29c48e"),
    (14999780112, 45561386072, "77a7ecc9a7cad8415a81cd8df8bb3ac5dfac67fda916f1c4be2a3bd47bd44eff"),
]
SOURCE_REVISIONS = {
    45554648116: "1217c6166525b6297191a35f2627eeea5691f17f",
    45647053824: "6df83f9e433d7e8c75e074b1789a457be6f4a4f3",
    45686044022: "9dfc3b3b5b0247e01dad1a8c323fd2a4f6963589",
    45633764095: "b4788a0c0b1cef8ff70ed79ddaf8c02e8de6ae43",
    45597857116: "3416108ec22f7e4519a365723a004b894dbbeed6",
    45568081544: "4e2d3bf7bcb982f5bc7be1f53ffaacb9b06c6a9d",
    45561386072: "988705d0e0d7de1b736777b1b66b324115d75fdb",
    45616647230: "736bfe4df57879407d074915a56b099763ddafbd",
    45700813110: "c14668f979fee95df18664cb383af1b51c5d77f1",
    45722543448: "779cbab28cf77c823e4a99dc3b358980e7a7f410",
}
THREE = (15001137494, 45560876359, "36c86203f3f7fb589b221046038513097a03534c8dc029cd83c328db53ae09aa")
THREE_REVISION = "735f449865149459df272eb9b858cf8ccf793404"
REQUIRED = [
    "CanonicalTwoParentRosterOnly", "Raw60RootFull", "Raw109Closed",
    "Raw110ParentLateCover", "Raw111Data", "Raw121Data",
    "Raw123ResidualClosure", "Raw125ResidualClosure",
]

def sha(path):
    with path.open("rb") as stream:
        return file_digest(stream, "sha256").hexdigest()

def api_json(path):
    return json.loads(subprocess.check_output(["gh", "api", path]))

def download(pin, work):
    aid, run, expected = pin
    info = api_json(f"repos/{REPO}/actions/artifacts/{aid}")
    assert info["workflow_run"]["id"] == run, (aid, info["workflow_run"])
    assert info["digest"] == "sha256:" + expected and not info["expired"], aid
    archive = work / f"{aid}.zip"
    with archive.open("wb") as f:
        subprocess.run(["gh", "api", f"repos/{REPO}/actions/artifacts/{aid}/zip"], stdout=f, check=True)
    assert sha(archive) == expected, f"ZIP digest mismatch: {aid}"
    dirs = {}
    with zipfile.ZipFile(archive) as z:
        for i in z.infolist():
            if i.is_dir():
                continue
            path = PurePosixPath(i.filename)
            if ".olean." in path.name or path.suffix == ".ir":
                raise ValueError(f"unsupported split object: {i.filename}")
            if path.suffix == ".olean":
                # These source audits use flat, unqualified project modules.
                # Keep distinct artifact directories distinct until collision checks.
                destdir = dirs.setdefault(str(path.parent), work / "parts" / str(aid) / str(len(dirs)))
                destdir.mkdir(parents=True, exist_ok=True)
                dest = destdir / path.name
                assert not dest.exists(), (aid, i.filename)
                with z.open(i) as src, dest.open("wb") as dst:
                    shutil.copyfileobj(src, dst)
            elif path.name == "manifest.json":
                dest = work / "metadata" / str(aid) / Path(*path.parts)
                dest.parent.mkdir(parents=True, exist_ok=True)
                with z.open(i) as src, dest.open("wb") as dst:
                    shutil.copyfileobj(src, dst)
            elif aid == 14997867504 and path.name in {"Raw117Data.lean", "SOURCE_COMMIT", "RAW117_SOURCE.sha256"}:
                dest = work / path.name
                assert not dest.exists(), i.filename
                dest.write_bytes(z.read(i))
    archive.unlink()
    assert dirs, f"no objects in {aid}"
    print(f"Verified and extracted artifact {aid}: {info['name']}", flush=True)
    return list(dirs.values())


def download_named_artifact(run_id, name, work):
    """Download one named artifact only from a successful, specified producer run."""
    run_info = api_json(f"repos/{REPO}/actions/runs/{run_id}")
    assert run_info["conclusion"] == "success", (run_id, run_info.get("conclusion"))
    artifacts = api_json(f"repos/{REPO}/actions/runs/{run_id}/artifacts")["artifacts"]
    matches = [item for item in artifacts if item["name"] == name]
    assert len(matches) == 1, (run_id, name, [(x["id"], x["name"]) for x in matches])
    item = matches[0]
    assert not item["expired"], (item["id"], "artifact expired")
    digest = item.get("digest") or ""
    assert digest.startswith("sha256:"), (item["id"], digest)
    expected = digest.removeprefix("sha256:")
    dirs = download((item["id"], run_id, expected), work)

    candidates = []
    for path in (work / "metadata" / str(item["id"])).rglob("manifest.json"):
        try:
            manifest = json.loads(path.read_text())
        except (OSError, json.JSONDecodeError):
            continue
        claim = manifest.get("claim") or {}
        modules = {entry.get("module") for entry in manifest.get("modules", [])}
        if (claim.get("theorem") == "BB6.Agent47Raw112.parent_cover"
                and claim.get("parent_table") == "1RB---_1RC---_0RD---_1LD1RE_---1LC_------"
                and claim.get("weighted_bound") == 100000
                and {"Raw112ClosedCover", "Raw112Data"} <= modules):
            candidates.append((path, manifest))
    assert len(candidates) == 1, (
        "expected exactly one Raw112 closed-parent manifest with the exact theorem/table/bound",
        [str(path) for path, _ in candidates],
    )
    manifest_path, manifest = candidates[0]
    assert manifest["proof_source_revision"] == run_info["head_sha"], (
        manifest["proof_source_revision"], run_info["head_sha"]
    )
    assert "4.36.0-rc2" in manifest["lean_version"], manifest["lean_version"]
    prefix = Path(subprocess.check_output(["lean", "--print-prefix"], text=True).strip())
    assert manifest["lean_binary"]["sha256"] == sha(prefix / "bin" / "lean")
    metadata = {
        "run_id": run_id,
        "source_revision": run_info["head_sha"],
        "artifact_id": item["id"],
        "artifact_name": name,
        "artifact_digest": digest,
        "manifest_path": str(manifest_path),
        "manifest_sha256": sha(manifest_path),
        "theorem": manifest["claim"]["theorem"],
        "parent_table": manifest["claim"]["parent_table"],
        "weighted_bound": manifest["claim"]["weighted_bound"],
        "lean_version": manifest["lean_version"],
        "lean_binary_sha256": manifest["lean_binary"]["sha256"],
        "module_count": manifest["module_count"],
    }
    print(f"Verified Raw112 parent artifact {item['id']} from successful run {run_id}.", flush=True)
    return metadata, dirs


def gate(log, required):
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    profiles = {}
    for name, axioms in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log):
        profiles[name] = {x.strip() for x in axioms.split(",") if x.strip()}
    for name in re.findall(r"'([^']+)' does not depend on any axioms", log):
        profiles[name] = set()
    for name in required:
        assert name in profiles, f"missing axiom report: {name}"
    for name, axioms in profiles.items():
        assert axioms <= allowed, (name, axioms - allowed)
    return {name: sorted(a) for name, a in profiles.items()}

def compile_module(source, output, env, logpath):
    result = subprocess.run(["lean", "-o", str(output), str(source)], env=env, cwd=source.parent, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    logpath.write_text(result.stdout)
    print(result.stdout, flush=True)
    result.check_returncode()
    return result.stdout

def link_reachable(groups, work, linked, families=None, extra_families=()):
    """Select only the recursive import closures of the actual proof roots.
    Every reached duplicate is still checked by exact kernel-data equality.
    Each source-audited root is resolved within its own artifact family first,
    so a missing import cannot be silently borrowed from an unrelated build.
    """
    from collections import defaultdict
    # Two accepted canonical artifacts form one explicitly checked base.
    # The eight Raw117 artifacts consist of its common closure and child shards.
    if families is None:
        families = [
            ("canonical76", [p for g in reversed(groups[:2]) for p in g],
             ["CanonicalTwoParentRosterOnly", "CanonicalRosterRefinement"]),
            ("raw60", groups[2], ["Raw60RootFull"]),
            ("raw109", groups[3], ["Raw109Closed"]),
            ("raw110", groups[4], ["Raw110ParentLateCover"]),
            ("raw111", groups[5], ["Raw111Data"]),
            ("raw121", groups[6], ["Raw121Data"]),
            ("raw123", groups[7], ["Raw123ResidualClosure"]),
            ("raw125", groups[8], ["Raw125ResidualClosure"]),
            ("raw117", [p for g in groups[9:] for p in g],
             [f"Raw117Kid{k:02d}" for k in range(24)]),
        ]
    prefix = Path(subprocess.check_output(["lean", "--print-prefix"], text=True).strip())
    stdlib = prefix / "lib" / "lean"
    walker = HERE / "WalkImportClosure.lean"
    comparator = HERE.parent / "agent13-raw125" / "CompareKernelImports.lean"
    objects = defaultdict(list)
    reached = {}
    for label, dirs, roots in [*families, *extra_families]:
        command = ["lean", "--run", str(walker), str(stdlib), str(len(dirs)),
                   *map(str, dirs), *roots]
        result = subprocess.check_output(command, text=True)
        files = sorted(set(Path(x) for x in result.splitlines()))
        assert files and all(p.suffix == ".olean" and p.is_file() for p in files), label
        assert all(any(p.name == root + ".olean" for p in files) for root in roots), label
        for p in files:
            assert p.parent in dirs, p
            if p not in objects[p.name]:
                objects[p.name].append(p)
        reached[label] = {"roots": roots, "files": [str(p) for p in files]}
        print(f"{label}: selected {len(files)} recursive project objects", flush=True)
    manifest = {"compiler_sha256": sha(prefix / "bin" / "lean"),
                "reached_families": reached, "objects": {}, "collisions": []}
    conflicts = []
    for name, files in sorted(objects.items()):
        first = files[0]
        digest = sha(first)
        manifest["objects"][name] = {"path": str(first), "sha256": digest}
        for other in files[1:]:
            oh = sha(other)
            if oh == digest:
                continue
            comparison = subprocess.run(["lean", "--run", str(comparator), str(first), str(other)],
                                        text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            row = {"module": name, "chosen": digest, "other": oh,
                   "other_path": str(other), "comparison": comparison.stdout.strip(),
                   "equal": comparison.returncode == 0}
            manifest["collisions"].append(row)
            print(comparison.stdout, end="", flush=True)
            if comparison.returncode:
                conflicts.append(name)
    (work / "reachable-link-audit.json").write_text(json.dumps(manifest, indent=2) + "\n")
    assert not conflicts, f"incompatible reached kernel declarations: {sorted(set(conflicts))}"
    linked.mkdir()
    for name, files in objects.items():
        # Keep the original downloaded audit objects immutable during elaboration.
        shutil.copy2(files[0], linked / name)
    (linked / "kernel-link-manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(f"Linked {len(objects)} reached modules with exact duplicate checks", flush=True)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--work", type=Path, required=True)
    ap.add_argument("--three", action="store_true", help="also consume Raw71, Raw77 and Raw81")
    ap.add_argument("--raw112-run-id", type=int,
                    help="successful run producing raw112-closed-parent-cover")
    args = ap.parse_args()
    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    assert "4.36.0-rc2" in subprocess.check_output(["lean", "--version"], text=True)
    for run, rev in SOURCE_REVISIONS.items():
        info = api_json(f"repos/{REPO}/actions/runs/{run}")
        assert info["head_sha"] == rev, (run, info["head_sha"])
        if run == 45647053824:
            job = api_json(f"repos/{REPO}/actions/jobs/139320746934")
            assert job["run_id"] == run and job["conclusion"] == "success", job
        else:
            assert info["conclusion"] == "success", (run, info["conclusion"])
    stable = [download(pin, work) for pin in PINS[:2]]
    stable_env = dict(os.environ, LEAN_PATH=os.pathsep.join(str(p) for group in reversed(stable) for p in group))
    stable_log = compile_module(HERE / "Canonical68StableBatch.lean", work / "Canonical68StableBatch.olean", stable_env, work / "stable68-standalone.log")
    gate(stable_log, ["BB6.Agent31StableParentBatch." + n for n in ["removeParents_sound", "liftCover", "parent_roots", "count68", "sound68", "exact_at_target"]])
    with ThreadPoolExecutor(max_workers=3) as pool:
        groups = stable + list(pool.map(lambda pin: download(pin, work), PINS[2:]))
    assert (work / "SOURCE_COMMIT").read_text().strip() == SOURCE_REVISIONS[45561386072]
    lines = (work / "RAW117_SOURCE.sha256").read_text().splitlines()
    expect = [line.split()[0] for line in lines if line.split()[-1] == "Raw117Data.lean"]
    assert expect == [sha(work / "Raw117Data.lean")], "Raw117 source hash"
    linked = work / "linked"
    extra_families = []
    raw112_meta = None
    if args.raw112_run_id is not None:
        raw112_meta, raw112_dirs = download_named_artifact(
            args.raw112_run_id, "raw112-closed-parent-cover", work
        )
        extra_families.append(("raw112", raw112_dirs, ["Raw112ClosedCover"]))
    if args.three:
        info = api_json(f"repos/{REPO}/actions/runs/{THREE[1]}")
        assert info["head_sha"] == THREE_REVISION and info["conclusion"] == "success"
        extra_families.append(("raw71-77-81", download(THREE, work), ["Raw71Data", "Raw77Data", "Raw81Data"]))
    link_reachable(groups, work, linked, extra_families=extra_families)
    for mod in REQUIRED:
        assert (linked / (mod + ".olean")).is_file(), f"missing module {mod}"
    for k in range(24):
        assert (linked / f"Raw117Kid{k:02d}.olean").is_file()
    env = dict(os.environ, LEAN_PATH=str(linked))
    assert not (linked / "Raw117Data.olean").exists(), "unexpected Raw117Data object"
    raw117log = compile_module(work / "Raw117Data.lean", linked / "Raw117Data.olean", env, work / "raw117.log")
    gate(raw117log, ["BB6.Agent8Raw117.all117"])
    thinlog = compile_module(HERE / "Canonical68StableBatch.lean", linked / "Canonical68StableBatch.olean", env, work / "stable68.log")
    gate(thinlog, ["BB6.Agent31StableParentBatch." + n for n in ["removeParents_sound", "liftCover", "parent_roots", "count68", "sound68", "exact_at_target"]])
    result = compile_module(HERE / "Canonical68Integrated.lean", linked / "Canonical68Integrated.olean", env, work / "canonical68.log")
    required = ["BB6.Agent31Canonical68Integrated." + name for name in [
        "p109_eq", "p123_eq", "cover109", "cover123", "all_parents", "p60_eq", "p110_eq", "p111_eq", "p117_eq", "p121_eq", "p125_eq",
        "cover60", "cover110", "cover111", "cover117", "cover121", "cover125",
        "sound68_integrated", "exact_at_target",
    ]]
    report = {"pins": PINS, "source_revisions": SOURCE_REVISIONS,
              "axioms": gate(result, required), "source_sha256": sha(HERE / "Canonical68Integrated.lean"),
              "olean_sha256": sha(linked / "Canonical68Integrated.olean"),
              "lean_version": subprocess.check_output(["lean", "--version"], text=True).strip()}
    (work / "canonical68-integration.json").write_text(json.dumps(report, indent=2) + "\n")
    print("Canonical68 integrated consumer compiled with the standard axiom gate.", flush=True)
    if raw112_meta is not None:
        stages = [
            (
                HERE / "Canonical74Raw109Raw123Graft.lean",
                "Canonical74Raw109Raw123Graft",
                [
                    "BB6.Agent31Canonical74Raw109Raw123.p109_root",
                    "BB6.Agent31Canonical74Raw109Raw123.p123_root",
                    "BB6.Agent31Canonical74Raw109Raw123.p109_parent_count",
                    "BB6.Agent31Canonical74Raw109Raw123.p123_parent_count",
                    "BB6.Agent31Canonical74Raw109Raw123.count75",
                    "BB6.Agent31Canonical74Raw109Raw123.count74",
                    "BB6.Agent31Canonical74Raw109Raw123.base_sound_at_target",
                    "BB6.Agent31Canonical74Raw109Raw123.raw109_sound",
                    "BB6.Agent31Canonical74Raw109Raw123.sound",
                    "BB6.Agent31Canonical74Raw109Raw123.exact_at_target",
                ],
            ),
            (
                HERE.parent / "agent6-e1-parent-consumer" / "Canonical68E1ParentGraft.lean",
                "Canonical68E1ParentGraft",
                [
                    "BB6.Agent6Canonical68E1ParentGraft.p60_parent_count",
                    "BB6.Agent6Canonical68E1ParentGraft.p110_parent_count",
                    "BB6.Agent6Canonical68E1ParentGraft.p111_parent_count",
                    "BB6.Agent6Canonical68E1ParentGraft.p117_parent_count",
                    "BB6.Agent6Canonical68E1ParentGraft.p121_parent_count",
                    "BB6.Agent6Canonical68E1ParentGraft.p125_parent_count",
                    "BB6.Agent6Canonical68E1ParentGraft.count68",
                    "BB6.Agent6Canonical68E1ParentGraft.sound68",
                    "BB6.Agent6Canonical68E1ParentGraft.exact_at_target",
                ],
            ),
            (
                HERE.parent / "agent47-raw112-cut" / "Canonical67E1ParentGraft.lean",
                "Canonical67E1ParentGraft",
                [
                    "BB6.Agent47Canonical67E1ParentGraft.p112_root",
                    "BB6.Agent47Canonical67E1ParentGraft.p112_parent_count",
                    "BB6.Agent47Canonical67E1ParentGraft.count67",
                    "BB6.Agent47Canonical67E1ParentGraft.sound67",
                    "BB6.Agent47Canonical67E1ParentGraft.exact_at_target67",
                ],
            ),
            (
                HERE.parent / "agent47-raw112-cut" / "Canonical67Integrated.lean",
                "Canonical67Integrated",
                [
                    "BB6.Agent47Canonical67Integrated.p112_eq",
                    "BB6.Agent47Canonical67Integrated.raw112_cover",
                    "BB6.Agent47Canonical67Integrated.sound67_integrated",
                    "BB6.Agent47Canonical67Integrated.exact_at_target67",
                ],
            ),
        ]
        stage_reports = {}
        for source, module, required in stages:
            log = compile_module(source, linked / (module + ".olean"), env,
                                 work / (module + ".log"))
            if re.search(r"sorryAx|native_decide", log):
                raise AssertionError(f"forbidden proof mechanism in {module}")
            stage_reports[module] = {
                "source_sha256": sha(source),
                "olean_sha256": sha(linked / (module + ".olean")),
                "axioms": gate(log, required),
            }
        integrated67 = {
            "status": "source-audited integrated conditional 67-residual interface",
            "weighted_bound_floor": 6766859,
            "residual_count": 67,
            "remaining_obligations": "a Cover at the target bound for each of the 67 retained quotient representatives, plus an attaining blank-start witness",
            "raw112_parent": raw112_meta,
            "canonical68_integration": report,
            "modules": stage_reports,
        }
        (work / "canonical67-integrated.json").write_text(
            json.dumps(integrated67, indent=2, sort_keys=True) + "\n"
        )
        print("Canonical67 integrated consumer compiled with the standard axiom gate.", flush=True)
    if args.three:
        source = HERE / "Canonical65AfterThree.lean"
        log = compile_module(source, linked / "Canonical65AfterThree.olean", env, work / "canonical65-three.log")
        gate(log, ["BB6.Agent31Canonical65AfterThree." + n for n in ["extra_roots", "extra_covers", "count65", "sound65", "exact_at_target"]])
        source = HERE / "Canonical65Integrated.lean"
        obj = linked / "Canonical65Integrated.olean"
        log = compile_module(source, obj, env, work / "canonical65-integrated.log")
        report = {"pins": PINS + [THREE], "source_revisions": {**SOURCE_REVISIONS, THREE[1]: THREE_REVISION},
                  "axioms": gate(log, ["BB6.Agent31Canonical65Integrated." + n for n in ["sound65_integrated", "exact_at_target"]]),
                  "source_sha256": sha(source), "olean_sha256": sha(obj)}
        (work / "canonical65-integrated.json").write_text(json.dumps(report, indent=2) + "\n")
        print("All eleven parent closures consumed in the canonical65 integrated theorem.", flush=True)

if __name__ == "__main__":
    main()
